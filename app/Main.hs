module Main (main) where

import Coo.REPL.Inside

main :: IO ()
main = do
  putStrLn "Coo!  (feel free to ask for #help)"
  replTop
  return ()
