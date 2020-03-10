
open import IO
open import Codata.Musical.Notation
open import Data.Unit
open import Function

t1 : IO ⊤
t1 = do
  ♯ putStrLn "foo"

t2 : IO ⊤
t2 = do
  l <- ♯ readFiniteFile "test.agda"
  ♯ putStrLn l

main = run (♯ t1 >> ♯ t2)
