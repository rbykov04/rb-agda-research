module Main where
import System.IO

main :: IO ()
main = do
  let a = "Hello form haskell" in hPutStrLn stderr a
