import Decidable.Equality

%default total

-- This is the (simplified) definition of names in Core.TT
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- 1. Write an Eq instance for Name
-- (sorry, it's not derivable yet!)
Eq Name where
  UN x   == UN y   = x == y
  MN a b == MN c d = a == c && b == d
  _      == _      = False

-- 2. Sometimes, we need to compare names for equality and use a proof that
-- they're equal. So, implement the following 
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN x) (UN y) | Yes refl = Just $ cong UN refl
  nameEq (UN x) (UN y) | _        = Nothing

nameEq (MN x1 y1) (MN x2 y2) with (decEq x1 x2)
  nameEq (MN x1 y1) (MN x2 y2) | Yes r1 with (decEq y1 y2)
    nameEq (MN x1 y1) (MN x2 y2) | Yes r1 | Yes r2 = Just $ cong2 MN r1 r2
    nameEq (MN x1 y1) (MN x2 y2) | Yes r1 | No  _  = Nothing
  nameEq (MN x1 y1) (MN x2 y2) | No _ = Nothing
nameEq _ _ = Nothing

unInjective : UN x = UN y -> x = y
unInjective Refl = Refl

mnInjective1 : MN x1 y1 = MN x2 y2 -> x1 = x2
mnInjective1 Refl = Refl

mnInjective2 : MN x1 y1 = MN x2 y2 -> y1 = y2
mnInjective2 Refl = Refl

Uninhabited (MN a b = UN c) where
  uninhabited Refl impossible

-- 3. (Optional, since we don't need this in Idris 2, but it's a good
-- exercise to see if you can do it!) Implement decidable equality, so you
-- also have a proof if names are *not* equal.
DecEq Name where
  decEq (UN x) (UN y) with (decEq x y)
    decEq (UN x) (UN y) | Yes refl = Yes $ cong UN refl
    decEq (UN x) (UN y) | No c     = No $ c . unInjective

  decEq (MN x1 y1) (MN x2 y2) with (decEq x1 x2)
    decEq (MN x1 y1) (MN x2 y2) | Yes r1 with (decEq y1 y2)
      decEq (MN x1 y1) (MN x2 y2) | Yes r1 | Yes r2 = Yes $ cong2 MN r1 r2
      decEq (MN x1 y1) (MN x2 y2) | Yes r1 | No c  = No $ c . mnInjective2
    decEq (MN x1 y1) (MN x2 y2) | No c = No $ c . mnInjective1
  decEq (UN _) (MN _ _) = No \prf => absurd (sym prf)
  decEq (MN _ _) (UN _) = No absurd
