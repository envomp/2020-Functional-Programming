foldNat : b -> (b -> b) -> Nat -> b
foldNat z s Z = z
foldNat z s (S n) = s (foldNat z s n)

foldList : (a -> b -> b) -> b -> List a -> b
foldList = foldr

data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

createTree : Tree Nat
createTree = Node (Node (Node Leaf 4 Leaf) 2 (Node Leaf 5 Leaf)) 1 (Node Leaf 3 Leaf)

foldTree : b -> (b -> a -> b -> b) -> Tree a -> b
foldTree l n Leaf = l
foldTree l n (Node tl x tr) = n (foldTree l n tl) x (foldTree l n tr)

andList : List Bool -> Bool
andList xs = foldr (\x, y => x && y) True xs

orList  : List Bool -> Bool
orList xs = foldr (\x, y => x || y) False xs

multList : List Nat -> Nat
multList xs = foldr (\x, y => x * y) (S Z) xs

addList  : List Nat -> Nat
addList xs = foldr (\x, y => x + y) Z xs

exp : Nat -> Nat -> Nat
exp base exp = foldNat 1 (\x => x * base) exp

flatten : List (List a) -> List a
flatten xs = foldr (\x, y => x ++ y) [] xs

filter' : List Bool -> List a -> List a
filter' [] xs = xs
filter' (x :: xs) [] = []
filter' (False :: xs) (y :: ys) = filter' xs ys
filter' (True :: xs) (y :: ys) = y :: (filter' xs ys)

filter : (a -> Bool) -> List a -> List a
filter f xs = filter' (foldr (\x, y => (f x) :: y) [] xs) xs

reverseTree : Tree a -> Tree a
reverseTree tree = foldTree Leaf (\left, x, right => Node right x left) tree

andTree : Tree Bool -> Bool
andTree tree = foldTree True (\left, x, right => left && x && right) tree

orTree : Tree Bool -> Bool
orTree tree = foldTree False (\left, x, right => left || x || right) tree

addTree  : Tree Nat -> Nat
addTree tree = foldTree Z (\left, x, right => left + x + right) tree

multTree : Tree Nat -> Nat
multTree tree = foldTree (S Z) (\left, x, right => left * x * right) tree

in_order   : Tree a -> List a
in_order tree = foldTree [] (\left, x, right => left ++ (x :: Nil) ++ right) tree

pre_order  : Tree a -> List a
pre_order tree = foldTree [] (\left, x, right => x :: (left ++ right)) tree

post_order : Tree a -> List a
post_order tree = foldTree [] (\left, x, right => left ++ right ++ (x :: Nil)) tree

breadthFirst' : List (Tree a) -> List a
breadthFirst' [] = []
breadthFirst' (Leaf :: xs) = []
breadthFirst' ((Node x y z) :: xs) = y :: (breadthFirst' (xs ++ [x] ++ [z]))

breadthFirst : Tree a -> List a
breadthFirst tree = breadthFirst' [tree]
