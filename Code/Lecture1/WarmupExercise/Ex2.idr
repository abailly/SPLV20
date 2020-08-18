import Data.List

data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- In the term representation, we represent local variables as an index into
-- a list of bound names:
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

-- And, sometimes, it's convenient to manipulate variables separately.
-- Note the erasure properties of the following definition (it is just a Nat
-- at run time)
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

-- 1. Remove all references to the most recently bound variable
dropFirst : List (Var (v :: vs)) -> List (Var vs)
dropFirst [] = []
dropFirst (MkVar First :: xs) = ?hole1_1
dropFirst (MkVar (Later x) :: xs) = ?hole1_

-- 2. Add a reference to a variable in the middle of a scope - we'll need
-- something like this later.
-- Note: The type here isn't quite right, you'll need to modify it slightly.
insertName : {outer : List Name} -> {inner : List Name} -> Var (outer ++ inner) -> Var (outer ++ n :: inner)
insertName {outer = []} (MkVar {i = 0} First) = MkVar First
insertName {outer = (x::xs)} (MkVar {i = 0} First) = MkVar First
insertName {outer = []} (MkVar {i = (S k)} p) = MkVar (Later p)
insertName {outer = (x::xs)} {inner = []} (MkVar {i = (S k)} (Later y)) = insertName {outer=x::xs} (MkVar First)
insertName {outer = (x::xs)} {inner = (z :: zs)} (MkVar {i = (S k)} (Later y)) = insertName {outer = (x::xs)} (MkVar (Later y))


data ListLen : List a -> Type where
     MkLen : (n : Nat) -> (n = length xs) -> ListLen xs
