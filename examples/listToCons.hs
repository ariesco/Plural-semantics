data Gente = Pepe | Loli | Manolo | Juani
  deriving(Eq)

instance Show Gente where
  show Pepe = "pepe"
  show Loli = "loli"
  show Manolo = "manolo"
  show Juani = "juani"

{-
data Temas =  T1.1 | 
  eq(t1.2, t1.2) -> tt .
  eq(t2.1, t2.1) -> tt .
  eq(t1.3, t1.3) -> tt .
  eq(t3.1, t3.1) -> tt .
  eq(t3, t3) -> tt .
  eq(t4, t4) -> tt .
  eq(t6, t6) -> tt .
  eq(t5, t5) -> tt .

-}
toLowCase :: Char -> Char
toLowCase c = toEnum (fromEnum c + salto)
  where salto = fromEnum 'a' - fromEnum 'A'

--  putStr (montaNeq ["trojan-gold", "treasure-map", "sirens-secret", "chest-code", "item(M)", "combine(X,Y)", "key"])
montaNeq :: [String] -> String
montaNeq es = concat (concatMap (\e -> map (entrada e) (filter (/= e) es)) es)
   where entrada e1 e2 = "    neq(" ++ e1 ++ ", " ++ e2 ++ ") -> tt .\n"

l2cons :: Show a => [a] -> String
l2cons = foldr (\x -> \xsCons -> "cons(" ++ (show x) ++ " ," ++ xsCons ++ ")") "nil"

f :: Show a => [a] -> String
f = show



{-__   __ __  __  ____   ___      _________________________________________
||   || ||  || ||  || ||__      Hugs 98: Based on the Haskell 98 standard
||___|| ||__|| ||__||  __||     Copyright (c) 1994-2005
||---||         ___||           World Wide Web: http://haskell.org/hugs
||   ||                         Bugs: http://hackage.haskell.org/trac/hugs
||   || Version: September 2006 _________________________________________

Haskell 98 mode: Restart with command line option -98 to enable extensions

Hugs> :l listToCons.hs
ERROR "listToCons.hs":2 - Unresolved top-level overloading
*** Binding             : l2cons
*** Outstanding context : Show b

Hugs> :l listToCons.hs
ERROR "listToCons.hs":5 - Unresolved top-level overloading
*** Binding             : f
*** Outstanding context : Show b

GHCi, version 6.8.2: http://www.haskell.org/ghc/  :? for help
Loading package base ... linking ... done.
Prelude> :l listToCons.hs
[1 of 1] Compiling Main             ( listToCons.hs, interpreted )

listToCons.hs:2:45:
    Ambiguous type variable `a1' in the constraint:
      `Show a1' arising from a use of `show' at listToCons.hs:2:45-50
    Possible cause: the monomorphism restriction applied to the following:
      l2cons :: [a1] -> [Char] (bound at listToCons.hs:2:0)
    Probable fix: give these definition(s) an explicit type signature
                  or use -fno-monomorphism-restriction

listToCons.hs:5:4:
    Ambiguous type variable `a' in the constraint:
      `Show a' arising from a use of `show' at listToCons.hs:5:4-7
    Possible cause: the monomorphism restriction applied to the following:
      f :: a -> String (bound at listToCons.hs:5:0)
    Probable fix: give these definition(s) an explicit type signature
                  or use -fno-monomorphism-restriction
Failed, modules loaded: none.




*Main> let x = show in x "hola"
"\"hola\""
-}
