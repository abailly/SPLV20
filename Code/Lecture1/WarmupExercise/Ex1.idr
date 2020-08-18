module Ex1

import Decidable.Equality

-- This is the (simplified) definition of names in Core.TT
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

unInj : (UN s = UN s') -> s = s'
unInj Refl = Refl

mnInjS : (MN s n = MN s' n') -> s = s'
mnInjS Refl = Refl

mnInjI : (MN s n = MN s' n') -> n = n'
mnInjI Refl = Refl

-- 1. Write an Eq instance for Name
-- (sorry, it's not derivable yet!)
Eq Name where
  UN s == UN s' = s == s'
  MN s n == MN s' n' = s == s' && n == n'
  _ == _ = False

-- 2. Sometimes, we need to compare names for equality and use a proof that
-- they're equal. So, implement the following
mutual
 nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
 nameEq x y with (decEq x y)
   nameEq x y | Yes prf = Just prf
   nameEq x y | No _ = Nothing

 -- 3. (Optional, since we don't need this in Idris 2, but it's a good
 -- exercise to see if you can do it!) Implement decidable equality, so you
 -- also have a proof if names are *not* equal.
 DecEq Name where
   decEq (UN x) (UN y) with (decEq x y)
     decEq (UN x) (UN y) | (Yes prf) = rewrite prf in Yes Refl
     decEq (UN x) (UN y) | (No contra) = No (contra . unInj)
   decEq (MN x z) (MN y w) with (decEq x y, decEq z w)
     decEq (MN x z) (MN y w) | ((Yes prf), (Yes v)) = rewrite prf in rewrite v in Yes Refl
     decEq (MN x z) (MN y w) | (No contra, _) = No (contra . mnInjS)
     decEq (MN x z) (MN y w) | (_ , No contra) = No (contra . mnInjI)
   decEq u@(UN _) m@(MN _ _) = No $ \case Refl impossible
   decEq m@(MN _ _) u@(UN _) = No $ \case Refl impossible


namespace Test
  testNeqName : nameEq (UN "foo") (UN "bar") = Nothing
  testNeqName = Refl

  testEqNameUN : nameEq (UN "foo") (UN "foo") = Just Refl
  testEqNameUN = Refl

  testEqNameMN : nameEq (MN "foo" 1) (MN "foo" 1) = Just Refl
  testEqNameMN = Refl
