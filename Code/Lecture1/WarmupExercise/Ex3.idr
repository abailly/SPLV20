
-- 1. Prove that appending Nil is the identity
-- (Note: this is defined in Data.List, but have a go yourself!)
appendNilNeutral : (xs : List a) -> xs ++ [] = xs
appendNilNeutral [] = Refl
appendNilNeutral (x :: xs) =
  let hyp = appendNilNeutral xs
  in rewrite hyp in Refl

-- 2. Prove that appending lists is associative.
-- (Note: also defined in Data.List)
appendAssoc : (xs : List a) -> (ys : List a) -> (zs : List a) ->
              xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
appendAssoc [] ys zs = Refl
appendAssoc (x :: xs) ys zs =
  let hyp = appendAssoc xs ys zs
  in rewrite hyp in Refl

-- A tree indexed by the (inorder) flattening of its contents
data Tree : List a -> Type where
     Leaf : Tree []
     Node : Tree xs -> (x : a) -> Tree ys -> Tree (xs ++ x :: ys)

-- 3. Fill in rotateLemma. You'll need appendAssoc.
rotateL : Tree xs -> Tree xs
rotateL Leaf = Leaf
rotateL (Node left n Leaf) = Node left n Leaf
rotateL (Node {xs} left n (Node {xs=xs'} {ys} rightl n' rightr))
    = rewrite appendAssoc xs (n :: xs') (n' :: ys) in
      Node (Node left n rightl) n' rightr


-- 4. Complete the definition of rotateR
rotateR : Tree xs -> Tree xs
rotateR Leaf = Leaf
rotateR n@(Node Leaf _ _) = n
rotateR (Node {ys} (Node {xs} {ys=ys'} leftl n leftr) n' right) =
  rewrite sym (appendAssoc xs (n :: ys') (n':: ys))
  in Node leftl n (Node leftr n' right)
