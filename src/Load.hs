-- Load.hs -- reading a Unit program as the checker does: parse, splice the
-- imported files (each once, depth first, as  module F { .. }), resolve.
-- The same steps as loadFiles in unit/app/Main.hs, which is not part of
-- the library.

module Load (loadProgram) where

import Seg
import SegParse
import Data.IORef

-- the resolved units of the program in a file, with its imports spliced in
loadProgram :: FilePath -> IO (Either String [Unit])
loadProgram f = do
  src <- readFile f
  seen <- newIORef [baseName f]
  case parseUnits src of
    Left msg -> return (Left ("PARSE ERROR\n" ++ msg))
    Right us0 -> do
      rus <- expand seen (dirOf f) us0
      return (either (Left . ("SCOPE ERROR\n" ++)) Right (resolveProgram rus))

dirOf :: FilePath -> FilePath
dirOf p = reverse (dropWhile (/= '/') (reverse p))

baseName :: FilePath -> String
baseName p = takeWhile (/= '.') (reverse (takeWhile (/= '/') (reverse p)))

expand :: IORef [String] -> FilePath -> [RUnit] -> IO [RUnit]
expand seen dir = fmap concat . mapM go
 where
  go u = case u of
    RImport x -> do
      s <- readIORef seen
      if x `elem` s then return [] else do
        modifyIORef seen (x :)
        src <- readFile (dir ++ x ++ ".seg")
        case parseUnits src of
          Left msg -> error ("in " ++ x ++ ".seg: " ++ msg)
          Right us -> do
            us' <- expand seen dir us
            return [RModule False x [] us']
    RModule k x tel us -> do us' <- expand seen dir us
                             return [RModule k x tel us']
    _ -> return [u]
