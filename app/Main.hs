-- unit2dk FILE.seg [-units=N] [-dkgf=FILE.dkgf] > FILE.dk
-- Translates a Unit program (FILE.seg with its imports) to Dedukti: the
-- prelude of the encoding, then the program; -units=N only the first N
-- top-level units.  A summary goes to stderr.
module Main where

import Seg
import Load
import Unit2Dedukti
import Dedukti.PrintDedukti (printTree)
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)
import Data.List (isPrefixOf)

main :: IO ()
main = do
  args <- getArgs
  let files = [ a | a <- args, not ("-" `isPrefixOf` a) ]
      opt o = [ drop (length o + 2) a | a <- args, ("-" ++ o ++ "=") `isPrefixOf` a ]
  case files of
    [f] -> do
      loaded <- loadProgram f
      us <- either (\m -> hPutStrLn stderr m >> exitFailure) return loaded
      let (_, _, fus) = checkUnitsF (programCx us) us
          prog = case opt "units" of
            (n : _) -> take (read n) fus
            [] -> fus
          r = translateProgram prog
      prelude <- readFile (preludePath args)
      putStr prelude
      mapM_ (putStrLn . printTree) (rJmts r)
      case opt "dkgf" of
        (g : _) -> writeFile g (unlines (rDkgf r))
        [] -> return ()
      hPutStrLn stderr (show (rFull r) ++ " translated, " ++ show (length (rAxioms r)) ++ " as axioms, "
                        ++ show (length (rSkipped r)) ++ " left out")
      mapM_ (\(i, m) -> hPutStrLn stderr ("AXIOM " ++ i ++ ": " ++ firstLine m)) (rAxioms r)
      mapM_ (\(i, m) -> hPutStrLn stderr ("LEFT OUT " ++ i ++ ": " ++ firstLine m)) (rSkipped r)
    _ -> hPutStrLn stderr "usage: unit2dk FILE.seg [-units=N] [-dkgf=FILE.dkgf] [-prelude=prelude.dk]"
 where
  firstLine = takeWhile (/= '\n')
  preludePath args = case [ drop 9 a | a <- args, "-prelude=" `isPrefixOf` a ] of
    (p : _) -> p
    [] -> "prelude.dk"
