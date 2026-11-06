-- Unit2Dedukti.hs -- translating a checked Unit program to Dedukti.
--
-- The translation follows the checker's context through the program (the
-- units with their hidden arguments filled, as Seg.checkUnitsF returns
-- them) and reads the values of Unit back into Dedukti terms, typed: a
-- constructor gets the arguments of its data type, a pair its Sigma type,
-- a type used at a higher universe its lift.  Definitions stay folded: a
-- value refers to a definition by its name (Seg's VRef), never by its body.
--
-- The encoding (prelude.dk, printed at the head of the output):
--
--  * levels: Lvl, lz, ls and an associative, commutative, idempotent lmax
--    with lz as unit, as Unit's Level.hs normalises them;
--  * universes a la Tarski: U l the codes, El l decoding them, u l : U (ls l)
--    the code of U l, and cumulativity as  lift l m : U l -> U (lmax l m)
--    with  El _ (lift l m a) --> El l a ;
--  * Pi, Sigma and Id as codes (pi, sigma, id), with pairs, projections, J
--    and their rules; a record type sig { .. } as nested sigmas;
--  * a data type as a constant with one constant per constructor, and a
--    definition by split as a constant with one rewrite rule per path
--    through its branches (the recursive results are recursive calls);
--  * a segment by lambda lifting: each member is a constant taking the
--    parameters (levels and terms) of its segments declared before it, and
--    M[args].f is the constant applied to args.
--
-- What is not translated (yet) becomes an axiom of the same type, marked
-- with a comment: the definitions using records declared with `record`
-- (new, segment types), constraint products, and whatever fails.

module Unit2Dedukti (translateProgram, Result(..)) where

import Seg
import Level
import qualified Dedukti.AbsDedukti as D
import qualified Data.Map as M
import qualified Data.Set as Set
import Data.Char (isAlphaNum)

------------------------------------------------------------------------
-- Dedukti syntax

type DExp = D.Exp

qid :: String -> D.QIdent
qid = D.QIdent

dv :: String -> DExp
dv = D.EIdent . qid

dapp :: DExp -> [DExp] -> DExp
dapp = foldl D.EApp

dlam :: String -> DExp -> DExp
dlam x = D.EAbs (D.BVar (qid x))

-- a lambda with its domain
dlamT :: String -> DExp -> DExp -> DExp
dlamT x a = D.EAbs (D.BTyped (qid x) a)

dpi :: String -> DExp -> DExp -> DExp
dpi x a = D.EFun (D.HVarExp (qid x) a)

-- the constants of the prelude
cLvl, cLz, cLs, cLmax, cU, cEl, cu, cLift, cPi, cSigma, cPair, cFst, cSnd, cId, cRefl, cJ, cOne, cTt :: String
cLvl = "Lvl"; cLz = "lz"; cLs = "ls"; cLmax = "lmax"; cU = "U"; cEl = "El"; cu = "u"
cLift = "lift"; cPi = "pi"; cSigma = "sigma"; cPair = "pair"; cFst = "fst"; cSnd = "snd"
cId = "id"; cRefl = "refl"; cJ = "J"; cOne = "one"; cTt = "tt"

-- a global (a declaration of the program): its id, quoted
gname :: Id -> String
gname i = "{|" ++ i ++ "|}"

-- the constructor c of the data type d
cname :: Id -> Name -> String
cname d c = "{|" ++ d ++ "." ++ c ++ "|}"

-- a local name: the name as written, quoted if Dedukti does not take it
-- as it is, and never one of the prelude's
lname :: Name -> String
lname x0
  | x `elem` reserved = x ++ "'"
  | not (null x) && all ok x && not (head x `elem` "'0123456789") = x
  | otherwise = "{|" ++ x ++ "|}"
 where
  x = takeWhile (/= '\1') x0
  ok c = isAlphaNum c && c < '\128' || c `elem` "_!?'"
  reserved = [cLvl, cLz, cLs, cLmax, cU, cEl, cu, cLift, cPi, cSigma, cPair, cFst, cSnd, cId, cRefl, cJ, cOne, cTt,
              "Type", "def", "thm", "injective"]

------------------------------------------------------------------------
-- What is known of the declarations translated so far

-- a parameter of a lifted constant: a term or a level of its segments, or
-- (for the derived members of a record) the element of the record, with
-- its Dedukti name and its type
data Param = PTm Name Val | PLv Name | PSelf String Val

data Info = Info
  { iParams :: [Param]                -- the parameters of its segments, outermost first
  , iData   :: Maybe ([Name], Exp)    -- a data type: the names of its lambdas, its type
  , iPrim   :: Bool                   -- a primitive notion (a parameter at top level)
  , iRec    :: Maybe RecInfo          -- a record type
  }

-- a record R (heads) { fields }: R : (params) (heads) -> U l
data RecInfo = RecInfo
  { rHeads  :: [Param]                -- its head parameters
  , rFields :: [(Name, Exp)]          -- its fields and their types
  , rLvl    :: Lvl                    -- the level of R[ps], in the level names of its declaration
  }

type Glob = M.Map Id Info

-- the translation context: the checker's context, and for each generic
-- variable (VGen k, or the level %k) the Dedukti term standing for it
-- (a variable, or a recursive call for the recursive results of a branch)
data TC = TC
  { tcCx    :: Cx
  , tcGens  :: M.Map Int (DExp, Val)  -- term generics: term and type
  , tcLGens :: M.Map String DExp      -- level generics %k
  , tcNames :: [String]               -- the Dedukti names in scope
  , tcGlob  :: Glob
  , tcPars  :: [Param]                -- the parameters in scope
  }

type T a = Either String a

-- a fresh Dedukti name for the binder x
fresh :: TC -> Name -> String
fresh tc x = head [ n | n <- base : [ base ++ show i | i <- [(1 :: Int) ..] ], n `notElem` tcNames tc ]
 where base = lname (if null x || x == "_" then "x" else x)

-- extend by a term variable of type t
extend :: TC -> Name -> Val -> (TC, Val, String)
extend tc x t =
  let n = fresh tc x
      k = cxK (tcCx tc)
      (cx', v) = extVar (tcCx tc) x t
  in (tc { tcCx = cx', tcGens = M.insert k (dv n, t) (tcGens tc), tcNames = n : tcNames tc }, v, n)

-- extend by a level variable
extendL :: TC -> Name -> (TC, Lvl, String)
extendL tc x =
  let n = fresh tc x
      k = cxK (tcCx tc)
      (cx', l) = extLvl (tcCx tc) x
  in (tc { tcCx = cx', tcLGens = M.insert ("%" ++ show k) (dv n) (tcLGens tc), tcNames = n : tcNames tc }, l, n)

------------------------------------------------------------------------
-- Levels

dlvl :: TC -> Lvl -> DExp
dlvl tc l = foldr1 (\a b -> dapp (dv cLmax) [a, b]) [ atom x k | (x, k) <- latoms l ]
 where
  atom x k = iterate (\e -> dapp (dv cLs) [e]) (base x) !! k
  base x | x == "0" = dv cLz
         | otherwise = M.findWithDefault (dv (lname x)) x (tcLGens tc)

-- a code of level l used at level m
lift :: TC -> Lvl -> Lvl -> DExp -> DExp
lift tc l m c
  | eqLvl (cxTh (tcCx tc)) l m = c
  | otherwise = dapp (dv cLift) [dlvl tc l, dlvl tc m, c]

------------------------------------------------------------------------
-- Reading values back, typed

-- the weak head normal form of a type, unfolding every definition: the
-- checker's locks say what conversion may unfold, but the translation has
-- to see the structure of a type
whnfT :: TC -> Val -> Val
whnfT _ = whnf Set.empty

-- a value of type t
readNf :: TC -> Val -> Val -> T DExp
readNf tc t v = case v of
  VLam f -> case whnfT tc t of
    VPi a g -> do
      da <- readType tc a
      let (tc', x, n) = extend tc (closName f) a
      b <- readNf tc' (capp g x) (capp f x)
      Right (dlamT n da b)
    t' -> Left ("a function at the type " ++ showT tc t')
  VLLam f -> case whnfT tc t of
    VLPi g -> do
      let (tc', l, n) = extendL tc (lclosName f)
      b <- readNf tc' (lcapp g l) (lcapp f l)
      Right (dlamT n (dv cLvl) b)
    t' -> Left ("a level function at the type " ++ showT tc t')
  VPair a b -> case whnfT tc t of
    VSig _ ta g -> do
      (cs, _) <- sigmaCode tc ta g
      da <- readNf tc ta a
      db <- readNf tc (capp g a) b
      Right (dapp (dv cPair) (cs ++ [da, db]))
    t' -> Left ("a pair at the type " ++ showT tc t')
  VStruct fs -> case whnfT tc t of
    VRec _ tel r -> readStruct tc tel r (map snd fs)
    t' -> Left ("a struct at the type " ++ showT tc t')
  VCon c vs -> case whnfT tc t of
    VSum _ _ (_:_) _ _ -> Left "an indexed family: not translated yet"
    VSum st _ _ cs r -> case lookup c (plainCons cs) of
      Just tel -> do
        let d = dataId st
        as <- dataArgs tc d r
        fs <- readFields tc tel r vs
        Right (dapp (dv (cname d c)) (as ++ fs))
      Nothing -> Left ("constructor " ++ c ++ " not in its type")
    t' -> Left ("a constructor at the type " ++ showT tc t')
  VInst m r -> do
    -- new R[ps, v1, .., vn]: the constructor at the parameters and the fields
    let rid = dataId (modId m)
        heads = [ (h, lookupDyn r h) | h <- recordHeads m ]
    as <- recArgs tc m heads
    ds <- mapM (\(y, ta) -> readNf tc (eval r ta) (lookupDyn r y)) (recordFieldUnits m)
    Right (dapp (dv (cname rid "mk")) (as ++ ds))
  VRefl a -> case whnfT tc t of
    VId ta _ _ -> do
      (ca, la) <- readCode tc ta
      da <- readNf tc ta a
      Right (dapp (dv cRefl) [dlvl tc la, ca, da])
    t' -> Left ("refl at the type " ++ showT tc t')
  _ | isTypeVal v -> case whnfT tc t of
    VU m -> do (c, l) <- readCode tc v
               Right (lift tc l m c)
    t' -> Left ("a type at the type " ++ showT tc t')
  _ -> do
    (d, t') <- readNe tc v
    case (whnfT tc t, whnfT tc t') of
      (VU m, VU l) -> Right (lift tc l m d)
      _ -> Right d

isTypeVal :: Val -> Bool
isTypeVal v = case v of
  VU _ -> True; VPi _ _ -> True; VSig _ _ _ -> True; VId _ _ _ -> True
  VSum{} -> True; VRec{} -> True; VSegT{} -> True
  _ -> False

closName :: Clos -> Name
closName (Clos x _ _) = x

lclosName :: LClos -> Name
lclosName (LClos x _ _) = x

showT :: TC -> Val -> String
showT tc = take 300 . showV (tcCx tc)

-- the fields of a constructor, typed by its telescope
readFields :: TC -> Tel -> Env -> [Val] -> T [DExp]
readFields _ [] _ [] = Right []
readFields tc ((y, ta) : tel) r (v : vs) = do
  d <- readNf tc (eval r ta) v
  ds <- readFields tc tel (EVar r y v) vs
  Right (d : ds)
readFields _ _ _ _ = Left "constructor arity"

-- a neutral value, with its type
readNe :: TC -> Val -> T (DExp, Val)
readNe tc v = case v of
  VGen k -> maybe (Left ("unknown variable #" ++ show k)) Right (M.lookup k (tcGens tc))
  -- a variable of record type: a bound variable (%vk), or a parameter
  VVar x _ _
    | take 2 x == "%v" -> maybe (Left ("unknown variable " ++ x)) Right (M.lookup (read (drop 2 x)) (tcGens tc))
    | otherwise -> do
        t <- tyOf x
        Right (dv (lname x), t)
  VConst x _ -> case M.lookup x (tcGlob tc) of
    Just i | iPrim i -> do
      t <- tyOf x
      Right (dv (gname x), t)
    _ -> do
      t <- tyOf x
      Right (dv (lname x), t)
  VRef u r -> case u of
    UDef i _ a _
      | M.member i (tcGlob tc) -> do
          as <- globalArgs tc i r
          Right (dapp (dv (gname i)) as, eval r a)
      -- a local definition (where, let): unfolded where it is used
      | otherwise -> do
          let t = eval r a
          d <- readNf tc t (unfoldRef u r)
          Right (d, t)
    _ -> Left "a reference to something else than a definition"
  VApp f a -> do
    (df, tf) <- readNe tc f
    case whnfT tc tf of
      VPi ta g -> do
        da <- readNf tc ta a
        Right (D.EApp df da, capp g a)
      t' -> Left ("an application of something of type " ++ showT tc t')
  VLApp f l -> do
    (df, tf) <- readNe tc f
    case whnfT tc tf of
      VLPi g -> Right (D.EApp df (dlvl tc l), lcapp g l)
      t' -> Left ("a level application of something of type " ++ showT tc t')
  VFst p -> do
    (dp, tp) <- readNe tc p
    case whnfT tc tp of
      VSig _ ta g -> do
        (cs, _) <- sigmaCode tc ta g
        Right (dapp (dv cFst) (cs ++ [dp]), ta)
      t' -> Left ("fst of something of type " ++ showT tc t')
  VSnd p -> do
    (dp, tp) <- readNe tc p
    case whnfT tc tp of
      VSig _ ta g -> do
        (cs, _) <- sigmaCode tc ta g
        Right (dapp (dv cSnd) (cs ++ [dp]), capp g (vfst p))
      t' -> Left ("snd of something of type " ++ showT tc t')
  VProj p l -> do
    (dp, tp) <- readNe tc p
    case whnfT tc tp of
      VRec _ tel r -> projField tc dp p tel r l
      -- a field of a record: its selector at the parameters and the element
      VSegT md fs -> do
        as <- recArgs tc md fs
        case lookup l (recordFieldUnits md) of
          Just ta -> Right ( dapp (dv (cname (dataId (modId md)) l)) (as ++ [dp])
                           , eval (selfEnv md fs p) ta )
          Nothing -> Left ("no field " ++ l ++ " in " ++ modId md)
      t' -> Left ("the projection ." ++ l ++ " of something of type " ++ showT tc t')
  VIdJ a x c d y p -> do
    (ca, la) <- readCode tc a
    dx <- readNf tc a x
    -- the motive: (z : A) -> Id A x z -> U m, m its level
    let (tc1, z, nz) = extend tc "z" a
        (tc2, q, nq) = extend tc1 "q" (VId a x z)
    (cm, m) <- readCode tc2 (app (app c z) q)
    let tz = dapp (dv cEl) [dlvl tc la, ca]
        tq = dapp (dv cEl) [dlvl tc la, dapp (dv cId) [dlvl tc la, ca, dx, dv nz]]
    dd <- readNf tc (app (app c x) (VRefl x)) d
    dy <- readNf tc a y
    dp <- readNf tc (VId a x y) p
    Right ( dapp (dv cJ) [dlvl tc la, ca, dx, dlvl tc m, dlamT nz tz (dlamT nq tq cm), dd, dy, dp]
          , app (app c y) p )
  _ -> Left ("cannot read back " ++ take 200 (showV (tcCx tc) v))
 where
  tyOf x = maybe (Left ("no type for " ++ x)) Right (lookup x (cxTys (tcCx tc)))

-- the code of a type, with its level
readCode :: TC -> Val -> T (DExp, Lvl)
readCode tc v = case v of
  VU l -> Right (dapp (dv cu) [dlvl tc l], lsuc l)
  VPi a f -> binderCode cPi tc a f
  VSig _ a f -> binderCode cSigma tc a f
  VId a x y -> do
    (ca, la) <- readCode tc a
    dx <- readNf tc a x
    dy <- readNf tc a y
    Right (dapp (dv cId) [dlvl tc la, ca, dx, dy], la)
  VSum _ _ (_:_) _ _ -> Left "an indexed family: not translated yet"
  VSum st _ _ _ r -> do
    let d = dataId st
    as <- dataArgs tc d r
    l <- dataLevel tc d r
    Right (dapp (dv (gname d)) as, l)
  VRec _ tel r -> telCode tc tel r
  VSegT md fs -> do
    as <- recArgs tc md fs
    l <- recLevel tc md fs
    Right (dapp (dv (gname (dataId (modId md)))) as, l)
  _ -> do
    (d, t) <- readNe tc v
    case whnfT tc t of
      VU l -> Right (d, l)
      t' -> Left ("not a small type: something of type " ++ showT tc t')

-- the parts of a Pi or Sigma: [l1, l2, a, \x. b], each at its own level,
-- and the level of the whole
parts :: TC -> Val -> Clos -> T ([DExp], Lvl)
parts tc a f = do
  (ca, la) <- readCode tc a
  let (tc', x, n) = extend tc (closName f) a
  (cb, lb) <- readCode tc' (capp f x)
  Right ([dlvl tc la, dlvl tc lb, ca, dlamT n (dapp (dv cEl) [dlvl tc la, ca]) cb], lmax la lb)

binderCode :: String -> TC -> Val -> Clos -> T (DExp, Lvl)
binderCode k tc a f = do
  (ps, m) <- parts tc a f
  Right (dapp (dv k) ps, m)

sigmaCode :: TC -> Val -> Clos -> T ([DExp], Lvl)
sigmaCode = parts

-- a record type: its fields as nested sigmas ending in one
telCode :: TC -> Tel -> Env -> T (DExp, Lvl)
telCode tc tel r = case tel of
  [] -> Right (dv cOne, lzero)
  _ -> do
    (ps, m, _) <- telParts tc tel r
    Right (dapp (dv cSigma) ps, m)

-- the parts of the sigma of the first field: its code, and the code of the
-- rest as a function of it
telParts :: TC -> Tel -> Env -> T ([DExp], Lvl, Val)
telParts tc tel r = case tel of
  (y, ta) : rest -> do
    let a = eval r ta
    (ca, la) <- readCode tc a
    let (tc', w, n) = extend tc y a
    (cr, lr) <- telCode tc' rest (EVar r y w)
    Right ([dlvl tc la, dlvl tc lr, ca, dlamT n (dapp (dv cEl) [dlvl tc la, ca]) cr], lmax la lr, a)
  [] -> Left "no field"

-- a struct, as nested pairs ending in tt
readStruct :: TC -> Tel -> Env -> [Val] -> T DExp
readStruct _ [] _ [] = Right (dv cTt)
readStruct tc tel@((y, _) : rest) r (v : vs) = do
  (ps, _, a) <- telParts tc tel r
  d <- readNf tc a v
  ds <- readStruct tc rest (EVar r y v) vs
  Right (dapp (dv cPair) (ps ++ [d, ds]))
readStruct _ _ _ _ = Left "struct arity"

-- the projection l of a record, as fst after snds
projField :: TC -> DExp -> Val -> Tel -> Env -> Name -> T (DExp, Val)
projField tc dp0 p tel0 r0 l = go dp0 tel0 r0
 where
  go d tel r = case tel of
    [] -> Left ("no field " ++ l)
    (y, _) : rest -> do
      (ps, _, a) <- telParts tc tel r
      if y == l
        then Right (dapp (dv cFst) (ps ++ [d]), a)
        else go (dapp (dv cSnd) (ps ++ [d])) rest (EVar r y (vproj p y))

------------------------------------------------------------------------
-- Globals: the arguments of a lifted constant, data types

dataId :: Id -> Id
dataId = takeWhile (/= '\0')

-- the arguments of the global i (its segments' parameters) at the
-- environment r of an access
globalArgs :: TC -> Id -> Env -> T [DExp]
globalArgs tc i r = case M.lookup i (tcGlob tc) of
  Nothing -> Left ("unknown global " ++ i)
  Just info -> mapM arg (iParams info)
 where
  arg p = case p of
    -- the element of a record, for its derived members
    PSelf _ _ -> case lookupVal r "%self" of
      w@(VInst m r') -> readNf tc (VSegT m [ (h, lookupDyn r' h) | h <- recordHeads m ]) w
      w -> fst <$> readNe tc w
    PLv x -> Right (dlvl tc (lookupLvl r x))
    PTm x _ -> case lookupVal r x of
      VConst y _ | y == x -> Right (dv (lname x))
      w -> do
        -- the type of the parameter at this instance
        t <- paramType x
        readNf tc t w
  paramType x = case [ t | PTm y t0 <- iParams (tcGlob tc M.! i), y == x, let t = t0 ] of
    (t : _) -> Right (reEval t)
    [] -> Left ("no parameter " ++ x)
  -- the parameter's type, evaluated where it was declared, now at the
  -- instance: re-evaluated in r
  reEval t = t `seq` paramTypeAt r t

-- the type of a parameter at an instance environment: its type was
-- evaluated in the segment's own context, where the earlier parameters are
-- rigid; at an instance they are bound in r, so the type is read back and
-- evaluated in r
paramTypeAt :: Env -> Val -> Val
paramTypeAt r t = eval r (rb False mempty 0 t)

-- the arguments of a data type: its segments' parameters and its lambdas
dataArgs :: TC -> Id -> Env -> T [DExp]
dataArgs tc d r = do
  ps <- globalArgs tc d r
  case M.lookup d (tcGlob tc) >>= iData of
    Nothing -> Left ("not a data type: " ++ d)
    Just (xs, ty) -> do
      as <- lamArgs (ev' ty) xs
      Right (ps ++ as)
 where
  ev' ty = eval r ty
  lamArgs _ [] = Right []
  lamArgs t (x : xs) = case whnfT tc t of
    VPi a f -> do
      let w = lookupVal r x
      dw <- readNf tc a w
      rest <- lamArgs (capp f w) xs
      Right (dw : rest)
    VLPi f -> do
      let l = lookupLvl r x
      rest <- lamArgs (lcapp f l) xs
      Right (dlvl tc l : rest)
    t' -> Left ("data type parameters: " ++ showT tc t')

-- the level of a data type at the environment of its value
dataLevel :: TC -> Id -> Env -> T Lvl
dataLevel tc d r = case M.lookup d (tcGlob tc) >>= iData of
  Nothing -> Left ("not a data type: " ++ d)
  Just (xs, ty) -> go (eval r ty) xs
 where
  go t xs = case (whnfT tc t, xs) of
    (VU l, []) -> Right l
    (VPi _ f, x : rest) -> go (capp f (lookupVal r x)) rest
    (VLPi f, x : rest) -> go (lcapp f (lookupLvl r x)) rest
    (t', _) -> Left ("the type of a data type: " ++ showT tc t')

------------------------------------------------------------------------
-- Records

-- the fields of a record and their types (not its head parameters)
recordFieldUnits :: Mod -> [(Name, Exp)]
recordFieldUnits md = [ (x, a) | UPar _ x a <- modUnits md, x `notElem` recordHeads md ]

-- the arguments of a record type R[ps]: the parameters of its segments, at
-- the environment of the instance, and its head parameters, from the type
recArgs :: TC -> Mod -> [(Name, Val)] -> T [DExp]
recArgs tc md fs = case M.lookup rid (tcGlob tc) >>= iRec of
  Nothing -> Left ("not a record translated: " ++ rid)
  Just ri -> do
    outer <- globalArgs tc rid (modEnv md)
    hs <- heads (modEnv md) (rHeads ri)
    Right (outer ++ hs)
 where
  rid = dataId (modId md)
  heads _ [] = Right []
  heads r (p : ps) = case p of
    PLv x -> case lookup x fs of
      Just (VLvl l) -> (dlvl tc l :) <$> heads (ELvl r x l) ps
      _ -> Left ("the head level " ++ x ++ " of " ++ rid)
    PTm x t -> case lookup x fs of
      Just v -> do
        d <- readNf tc (paramTypeAt r t) v
        (d :) <$> heads (EVar r x v) ps
      Nothing -> Left ("the head parameter " ++ x ++ " of " ++ rid)
    PSelf _ _ -> Left "a record element as a head"

-- the level of a record type at an instance: its level, with the level
-- parameters of its segments and of its head as the instance gives them
recLevel :: TC -> Mod -> [(Name, Val)] -> T Lvl
recLevel tc md fs = case M.lookup rid (tcGlob tc) of
  Just Info { iRec = Just ri, iParams = ps } ->
    let outer = [ (x, lookupLvl (modEnv md) x) | PLv x <- ps ]
        heads = [ (x, l) | PLv x <- rHeads ri, Just (VLvl l) <- [lookup x fs] ]
    in Right (lsubst (\x -> maybe (lvar x) id (lookup x (heads ++ outer))) (rLvl ri))
  _ -> Left ("not a record translated: " ++ rid)
 where rid = dataId (modId md)

-- record R (heads) { fields ; derived members }: the type R, its
-- constructor R.mk, a selector for each field with its rule, and the
-- derived members as constants taking the element
recordDecl :: TC -> Id -> Mod -> Result -> (Glob, Result)
recordDecl tc i md out = case decls of
  Left m -> (tcGlob tc, out { rSkipped = (i, "record: " ++ m) : rSkipped out })
  Right (js, glob, line, extra) ->
    (glob, extra out { rJmts = reverse js ++ rJmts out, rDkgf = line : rDkgf out, rFull = rFull out + 1 })
 where
  hs = recordHeads md
  decls = do
    -- the head parameters, as the parameters of a segment
    let tcH = fst (units tc [i] (headUnits md) (Result [] [] 0 [] []))
        heads = drop (length (tcPars tc)) (tcPars tcH)
        pnames = map fst (paramBinds tcH)
        tcH' = tcH { tcNames = pnames ++ tcNames tcH }
    -- the constructor: the fields as variables
    (_, fields) <- conFields tcH' (filter (not . isHeadUnit) (modUnits md))
    let l = foldr (lmax . (\(_, _, k) -> k)) lzero fields
        self = dapp (dv (gname i)) (map dv pnames)
        elT = dapp (dv cEl) [dlvl tcH l, self]
        tyR = closeParams tcH (dapp (dv cU) [dlvl tcH l])
        mk = cname i "mk"
        tyMk = closeParams tcH (foldr (\(n, a, _) e -> dpi n a e) elT fields)
        ri = RecInfo heads (recordFieldUnits md) l
        glob = M.insert i (Info (tcPars tc) Nothing False (Just ri)) (tcGlob tc)
        tcG = tcH' { tcGlob = glob }
    -- the selectors: the element as a variable t, the earlier fields as
    -- its projections
        hv = [ case p of { PLv x -> (x, VLvl (lvar x)); PTm x _ -> (x, lookupVal (cxEnv (tcCx tcH)) x)
                         ; PSelf x _ -> (x, VConst x []) } | p <- heads ]
        selfTy = VSegT md hv
        (tcT, tv, nt) = extend tcG "t" selfTy
        env = selfEnv md hv tv
        fnames = [ n | (n, _, _) <- fields ]
        vars = map (D.PBVar . qid) (pnames ++ fnames)
        lhsMk = pappl mk (map (D.PVar . qid) (pnames ++ fnames))
    sels <- mapM (\((y, ta), n) -> do
                    dt <- readType tcT (eval env ta)
                    let sel = cname i y
                        ty = closeParams tcH (dpi nt elT dt)
                        rule = D.RRule vars (pappl sel (map (D.PVar . qid) pnames ++ [lhsMk])) (dv n)
                    Right (sel, [D.JDef (qid sel) (D.MTExp ty) D.MENone, D.JRules [rule]]))
                 (zip (recordFieldUnits md) fnames)
    -- the derived members, each with the element as its last parameter
    let tcD = tcT { tcPars = tcPars tcH ++ [PSelf nt selfTy] }
        defs = [ u | u@(UDef{}) <- modUnits md ]
        globD = foldl (\g (UDef j _ _ _) -> M.insert j (Info (tcPars tcD) Nothing False Nothing) g) glob defs
        tcD' = tcD { tcGlob = globD }
        derived = [ member tcD' env u | u <- defs ]
        line = "#RECORD " ++ gname i ++ " " ++ mk ++ " " ++ unwords (map fst sels)
        extra o = foldl (\o' (_, f) -> f o') o derived
    Right ( [D.JStatic (qid (gname i)) tyR, D.JStatic (qid mk) tyMk] ++ concatMap snd sels
            ++ concatMap fst derived
          , globD, line, extra )
  isHeadUnit u = case u of
    ULvl x -> x `elem` hs
    UPar _ x _ -> x `elem` hs
    _ -> False
  -- the fields as variables, with their types and levels; the derived
  -- members and opens in between are entered (and unfolded where used)
  conFields t [] = Right (t, [])
  conFields t (u : us) = case u of
    UPar _ y a -> do
      let va = ev (tcCx t) a
      (_, k) <- readCode t va
      da <- readType t va
      let (t', _, n) = extend t y va
      (t'', rest) <- conFields t' us
      Right (t'', (n, da, k) : rest)
    UDef{} -> let (g, rest) = span isGroupUnit (u : us)
              in conFields t { tcCx = enterGroup (tcCx t) g } rest
    UInst{} -> conFields t { tcCx = (tcCx t) { cxEnv = mkGroup (cxEnv (tcCx t)) [u] } } us
    UCstr cs -> conFields t { tcCx = addCs (tcCx t) (map (evalCs (cxEnv (tcCx t))) cs) } us
    _ -> conFields t us
  -- a derived member: a definition with the element as its last parameter
  member t env u = case u of
    UDef j _ a b ->
      let ta = eval env a
      in case readType t ta of
        Left m -> ([], \o -> o { rSkipped = (j, "type: " ++ m) : rSkipped o })
        Right dt ->
          let ty = closeParams t dt
          in case readNf t ta (eval env b) of
            Right db -> ([D.JDef (qid (gname j)) (D.MTExp ty) (D.MEExp (closeLams t db))], \o -> o { rFull = rFull o + 1 })
            Left m -> ([D.JStatic (qid (gname j)) ty], \o -> o { rAxioms = (j, m) : rAxioms o })
    _ -> ([], id)

------------------------------------------------------------------------
-- Types, in type position: Pi as Dedukti's own, otherwise El of a code

readType :: TC -> Val -> T DExp
readType tc t = case whnfFoldedT t of
  VPi a f -> do
    da <- readType tc a
    let (tc', x, n) = extend tc (closName f) a
    db <- readType tc' (capp f x)
    Right (dpi n da db)
  VLPi f -> do
    let (tc', l, n) = extendL tc (lclosName f)
    db <- readType tc' (lcapp f l)
    Right (dpi n (dv cLvl) db)
  VCPi _ a -> readType tc a
  VU l -> Right (dapp (dv cU) [dlvl tc l])
  _ -> do
    (c, l) <- readCode tc t
    Right (dapp (dv cEl) [dlvl tc l, c])
 where
  whnfFoldedT = id

------------------------------------------------------------------------
-- The program

data Result = Result
  { rJmts      :: [D.Jmt]
  , rDkgf      :: [String]          -- #STRUCTURE lines
  , rFull      :: Int               -- declarations translated in full
  , rAxioms    :: [(Id, String)]    -- definitions given as axioms, and why
  , rSkipped   :: [(Id, String)]    -- declarations left out, and why
  }

translateProgram :: [Unit] -> Result
translateProgram us =
  let tc0 = TC (programCx us) M.empty M.empty [] M.empty []
      (_, out) = units tc0 [] us (Result [] [] 0 [] [])
  in out { rJmts = reverse (rJmts out), rDkgf = reverse (rDkgf out)
         , rAxioms = reverse (rAxioms out), rSkipped = reverse (rSkipped out) }

-- the units of a body; the path is the list of enclosing segments
units :: TC -> [Name] -> [Unit] -> Result -> (TC, Result)
units tc _ [] out = (tc, out)
units tc path (u : us) out = case u of
  ULvl x ->
    let cx = tcCx tc
        tc' = tc { tcCx = cx { cxTh = addVar x (cxTh cx), cxLvls = x : cxLvls cx }
                 , tcPars = if null path then tcPars tc else tcPars tc ++ [PLv x]
                 , tcNames = lname x : tcNames tc }
    in units tc' path us out
  UCstr cs ->
    let cx = tcCx tc
    in units tc { tcCx = addCs cx (map (evalCs (cxEnv cx)) cs) } path us out
  UPar i x a ->
    let cx = tcCx tc
        va = ev cx a
        cx' = cx { cxEnv = case force cx va of
                             VSegT md fs -> EDecl (cxEnv cx) x (VVar x md fs)
                             _ -> cxEnv cx
                 , cxTys = (x, va) : cxTys cx }
    in if null path
         then -- a primitive notion: a constant of its own
           let tcP = tc { tcCx = cx' }
               (out', ok) = case readType tc va of
                 Right t -> (out { rJmts = D.JStatic (qid (gname x)) (closeParams tc t) : rJmts out
                                 , rFull = rFull out + 1 }, True)
                 Left m -> (out { rSkipped = (i, m) : rSkipped out }, False)
               glob' = if ok then M.insert x (Info [] Nothing True Nothing) (tcGlob tc) else tcGlob tc
           in units tcP { tcGlob = glob' } path us out'
         else units tc { tcCx = cx', tcPars = tcPars tc ++ [PTm x va], tcNames = lname x : tcNames tc } path us out
  ULock s -> units tc { tcCx = (tcCx tc) { cxLocks = Set.fromList s } } path us out
  UDir _ -> units tc path us out
  UMod i x k mus -> case k of
    SModule ->
      let cx = tcCx tc
          (tcIn, out1) = units tc { tcCx = cx { cxPSorts = [] } } (path ++ [x]) mus out
          u' = UMod i x k mus
          cx1 = cx { cxEnv = mkGroup (cxEnv cx) [u'], cxLocks = cxLocks (tcCx tcIn)
                   , cxSegSort = (i, cxPSorts (tcCx tcIn)) : cxSegSort (tcCx tcIn) }
          own = drop (length (tcPars tc)) (tcPars tcIn)
          struct = "#STRUCTURE " ++ i ++ " (" ++ unwords [ parName p | p <- own ] ++ ") "
                   ++ unwords [ gname j | UDef j _ _ _ <- mus ]
          out2 = out1 { rDkgf = struct : rDkgf out1 }
      in units tc { tcCx = cx1, tcGlob = tcGlob tcIn } path us out2
    SRecord _ ->
      let cx = tcCx tc
          u' = UMod i x k mus
          cx1 = cx { cxEnv = mkGroup (cxEnv cx) [u'] }
          (glob', out') = recordDecl tc { tcCx = cx1 } i (lookupMod (cxEnv cx1) x) out
      in units tc { tcCx = cx1, tcGlob = glob' } path us out'
  UInst _ _ _ ->
    units tc { tcCx = (tcCx tc) { cxEnv = mkGroup (cxEnv (tcCx tc)) [u] } } path us out
  UDef{} ->
    let (g, rest) = span isGroupUnit (u : us)
        tc1 = tc { tcCx = enterGroup (tcCx tc) g }
        (tc2, out') = foldl (\(t, o) d -> definition d (t, o)) (tc1, out) g
    in units tc2 path rest out'
 where
  parName p = case p of { PTm x _ -> lname x; PLv x -> lname x; PSelf n _ -> n }

-- the type of a lifted constant: the parameters in scope, then t
closeParams :: TC -> DExp -> DExp
closeParams tc t = foldr bind t (paramBinds tc)
 where bind (n, a) b = dpi n a b

paramBinds :: TC -> [(String, DExp)]
paramBinds tc = go tc0 (tcPars tc)
 where
  -- the names of all the parameters are in scope in their types, so that
  -- no binder in a type captures a parameter
  tc0 = tc { tcNames = [ case p of { PTm y _ -> lname y; PLv y -> lname y; PSelf n _ -> n } | p <- tcPars tc ] }
  go _ [] = []
  go t (p : ps) = case p of
    PLv x -> (lname x, dv cLvl) : go t ps
    PSelf n a -> case readType t a of
      Right da -> (n, da) : go t ps
      Left m -> (n, dv ("{|untranslated parameter type: " ++ filter (/= '|') (take 80 m) ++ "|}")) : go t ps
    PTm x a -> case readType t a of
      Right da -> (lname x, da) : go t ps
      Left m -> (lname x, dv ("{|untranslated parameter type: " ++ filter (/= '|') (take 80 m) ++ "|}")) : go t ps

------------------------------------------------------------------------
-- Definitions

definition :: Unit -> (TC, Result) -> (TC, Result)
definition u (tc, out) = case u of
  UDef i _ a b ->
    let tcD = tc { tcNames = map fst (paramBinds tc) }
        ta = ev (tcCx tcD) a
        info = Info (tcPars tc) (dataLams b a) False Nothing
        glob' = M.insert i info (tcGlob tc)
        tcG = tcD { tcGlob = glob' }
        out' = case readType tcG ta of
          Left m -> out { rSkipped = (i, "type: " ++ m) : rSkipped out }
          Right dt ->
            let ty = closeParams tcG dt
            in case dataBody b of
              Just _ -> case dataDecl tcG i ta b of
                Right js -> out { rJmts = reverse js ++ D.JStatic (qid (gname i)) ty : rJmts out
                                , rFull = rFull out + 1 }
                Left m -> out { rJmts = D.JStatic (qid (gname i)) ty : rJmts out
                              , rAxioms = (i, "data: " ++ m) : rAxioms out }
              Nothing | hasSplit b -> case splitRules tcG i ta b of
                Right rs -> out { rJmts = rulesJmt rs ++ D.JDef (qid (gname i)) (D.MTExp ty) D.MENone : rJmts out
                                , rFull = rFull out + 1 }
                Left m -> out { rJmts = D.JStatic (qid (gname i)) ty : rJmts out
                              , rAxioms = (i, "split: " ++ m) : rAxioms out }
              Nothing -> case readNf tcG ta (ev (tcCx tcG) b) of
                Right db -> out { rJmts = D.JDef (qid (gname i)) (D.MTExp ty) (D.MEExp (closeLams tcG db)) : rJmts out
                                , rFull = rFull out + 1 }
                Left m -> out { rJmts = D.JStatic (qid (gname i)) ty : rJmts out
                              , rAxioms = (i, m) : rAxioms out }
        failed = case readType tcG ta of { Left _ -> True; _ -> False }
    in (tc { tcGlob = if failed then tcGlob tc else glob' }, out')
  _ -> (tc, out)
 where
  rulesJmt rs = [D.JRules rs | not (null rs)]

closeLams :: TC -> DExp -> DExp
closeLams tc b = foldr (\(n, a) e -> dlamT n a e) b (paramBinds tc)

-- the body of a data definition: its constructors, after its lambdas
dataBody :: Exp -> Maybe [(Name, Tel)]
dataBody e = case e of
  Lam _ b -> dataBody b
  LLam _ b -> dataBody b
  Sum _ [] cs -> Just (plainCons cs)
  _ -> Nothing

-- the constructors of a data type without indices: their fields (the target
-- indices, which such a type has none of, left out)
plainCons :: [(Name, Tel, [Exp])] -> [(Name, Tel)]
plainCons cs = [(c, tel) | (c, tel, _) <- cs]

-- a data type: the names of its lambdas and its type
dataLams :: Exp -> Exp -> Maybe ([Name], Exp)
dataLams b a = fmap (const (go b, a)) (dataBody b)
 where
  go e = case e of
    Lam x c -> x : go c
    LLam x c -> x : go c
    _ -> []

hasSplit :: Exp -> Bool
hasSplit e = case e of
  Lam _ b -> hasSplit b
  LLam _ b -> hasSplit b
  Split _ _ _ -> True
  _ -> False

-- the constructors of a data type d of type t, body b
dataDecl :: TC -> Id -> Val -> Exp -> T [D.Jmt]
dataDecl tc d t b = go tc t (ev (tcCx tc) b) []
 where
  go tcx ty v binds = case (whnfT tcx ty, v) of
    (VPi a f, VLam cl) -> do
      da <- readType tcx a
      let (tc', x, n) = extend tcx (closName cl) a
      go tc' (capp f x) (capp cl x) (binds ++ [(n, da)])
    (VLPi f, VLLam cl) -> do
      let (tc', l, n) = extendL tcx (lclosName cl)
      go tc' (lcapp f l) (lcapp cl l) (binds ++ [(n, dv cLvl)])
    (VU _, VSum _ _ (_:_) _ _) -> Left "an indexed family: not translated yet"
    (VU _, s@(VSum _ _ _ cs0 r)) -> do
      let cs = plainCons cs0
      (self, l) <- readCode tcx s
      mapM (con tcx self l r binds) cs
    (t', _) -> Left ("data type of type " ++ showT tcx t')
  con tcx self l r binds (c, tel) = do
    fs <- fields tcx tel r
    let res = dapp (dv cEl) [dlvl tcx l, self]
        ty = foldr (\(n, a) e -> dpi n a e) res (binds ++ fs)
    Right (D.JStatic (qid (cname d c)) (closeParams tc ty))
  fields _ [] _ = Right []
  fields tcx ((y, ta) : tel) r = do
    let a = eval r ta
    da <- readType tcx a
    let (tc', w, n) = extend tcx y a
    rest <- fields tc' tel (EVar r y w)
    Right ((n, da) : rest)

------------------------------------------------------------------------
-- Definitions by split: one rewrite rule per path through the branches

-- an argument of the left-hand side: as a pattern and as a term
data LArg = LArg D.Patt DExp

splitRules :: TC -> Id -> Val -> Exp -> T [D.Rule]
splitRules tc f t b = do
  let pars = [ (n, LArg (D.PVar (qid n)) (dv n)) | (n, _) <- paramBinds tc ]
  walk tc (map fst pars) (map snd pars) t b
 where
  head' = dv (gname f)
  lhsTerm args = dapp head' [ e | LArg _ e <- args ]
  walk tcx vars args ty e = case e of
    Lam x body -> case whnfT tcx ty of
      VPi a g -> do
        let (tc', w, n) = extend tcx x a
        walk tc' (vars ++ [n]) (args ++ [LArg (D.PVar (qid n)) (dv n)]) (capp g w) body
      t' -> Left ("lambda at " ++ showT tcx t')
    LLam x body -> case whnfT tcx ty of
      VLPi g -> do
        let (tc', l, n) = extendL tcx x
        walk tc' (vars ++ [n]) (args ++ [LArg (D.PVar (qid n)) (dv n)]) (lcapp g l) body
      t' -> Left ("level lambda at " ++ showT tcx t')
    Split st _ bs -> case whnfT tcx ty of
      VPi dom g -> case whnfT tcx dom of
        VSum _ _ (_:_) _ _ -> Left "a split on an indexed family: not translated yet"
        VSum dst _ _ cs0 r -> do
          let cs = plainCons cs0
          let d = dataId dst
          as <- dataArgs tcx d r
          rss <- mapM (branch tcx vars args d as cs r g st) bs
          Right (concat rss)
        dom' -> Left ("split on " ++ showT tcx dom')
      t' -> Left ("split at " ++ showT tcx t')
    _ -> do
      rhs <- readNf tcx ty (ev (tcCx tcx) e)
      Right [D.RRule (map (D.PBVar . qid) vars) (lhsPatt (gname f) args) rhs]
  branch tcx vars args d as cs r g st (c, (xs, rs, body)) = case lookup c cs of
    Nothing -> Left ("no constructor " ++ c)
    Just tel -> do
      -- the data type's arguments in the pattern: a variable of the left-hand
      -- side as itself (a non-linear pattern), another term in brackets (a
      -- term the argument must be convertible to), else a fresh variable
      let fresh' = [ n | k <- [(1 :: Int) ..], let n = "d" ++ show k ++ "_", n `notElem` tcNames tcx ]
          dpats :: [Either D.Patt String]
          dpats = zipWith (\a n -> case a of
                             D.EIdent (D.QIdent y) | y `elem` vars -> Left (D.PVar (qid y))
                             _ | Just pt <- exp2patt a -> Left (D.PBracket pt)
                             _ -> Right n) as fresh'
          dnames = [ n | Right n <- dpats ]
          tcd = tcx { tcNames = dnames ++ tcNames tcx }
      (tcF, fvs, fnames) <- openFields tcd xs tel r
      let conPatt = pappl (cname d c) (map (either id (D.PVar . qid)) dpats ++ map (D.PVar . qid) fnames)
          conTerm = dapp (dv (cname d c)) (as ++ map dv fnames)
          prefix = lhsTerm args
          vcon = VCon c fvs
      -- the recursive results: the split's own constant applied to the
      -- prefix and the recursive field
      cxR <- recCx (tcCx tcF) st c tel r g fvs rs
      let k0 = cxK (tcCx tcF)
          tys = reverse (take (length rs) (cxTys cxR))
      calls <- mapM (\(RecR j n _ _) -> recCall tcF prefix (fnames !! j) (fieldTypes tcF fvs tel r !! j) n) rs
      let tcR = tcF { tcCx = cxR
                    , tcGens = foldl (\m (k, call, ty) -> M.insert k (call, snd ty) m)
                                     (tcGens tcF) (zip3 [k0 ..] calls tys) }
      walk tcR (vars ++ dnames ++ fnames) (args ++ [LArg conPatt conTerm]) (capp g vcon) body
  -- extend by the fields of a branch
  openFields tcx [] [] _ = Right (tcx, [], [])
  openFields tcx (x : xs) ((y, ta) : tel) r = do
    let a = eval r ta
        (tc', w, n) = extend tcx x a
    (tc'', ws, ns) <- openFields tc' xs tel (EVar r y w)
    Right (tc'', w : ws, n : ns)
  openFields _ _ _ _ = Left "branch arity"
  -- the recursive result of the field x: the split's constant at the
  -- prefix, applied to x; for a field of function type, under its binders
  recCall tcx prefix x a n = go tcx a n []
   where
    go _ _ 0 zs = Right (foldr (\(z, t) e -> dlamT z t e) (D.EApp prefix (dapp (dv x) (map (dv . fst) zs))) zs)
    go t ty k zs = case whnfT t ty of
      VPi dom cl -> do
        dd <- readType t dom
        let (t', w, z) = extend t (closName cl) dom
        go t' (capp cl w) (k - 1) (zs ++ [(z, dd)])
      ty' -> Left ("a recursive field of type " ++ showT t ty')
  -- the types of the fields of a branch
  fieldTypes _ vs tel r = go' vs tel r
   where
    go' (v : vs') ((y, ta) : tel') e = eval e ta : go' vs' tel' (EVar e y v)
    go' _ _ _ = []

lhsPatt :: String -> [LArg] -> D.Patt
lhsPatt h args = foldl D.PApp (D.PVar (qid h)) [ p | LArg p _ <- args ]

-- a term as a pattern, for brackets
exp2patt :: DExp -> Maybe D.Patt
exp2patt e = case e of
  D.EIdent x -> Just (D.PVar x)
  D.EApp f a -> D.PApp <$> exp2patt f <*> exp2patt a
  D.EAbs b body -> D.PBind b <$> exp2patt body
  _ -> Nothing

pappl :: String -> [D.Patt] -> D.Patt
pappl c ps = foldl D.PApp (D.PVar (qid c)) ps

