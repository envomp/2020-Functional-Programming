tabulate : List a -> (Nat -> Maybe a)
tabulate [] k = Nothing
tabulate (x :: xs) Z = Just x
tabulate (x :: xs) (S k) = tabulate xs k

recover : (Nat -> Maybe a) -> List a
recover f = recover' f Z
    where
        recover' : (Nat -> Maybe a) -> Nat -> List a
        recover' f k =
            case f k of
                Nothing => []
                (Just x) => x :: (recover' f (S k))

zero_to_nine : (Nat -> Maybe Nat)
zero_to_nine n = if n < 10 then Just n else Nothing

tabTail : (Nat -> Maybe a) -> (Nat -> Maybe a)
tabTail f x = f (x + 1)

tabMap : (a -> b) -> (Nat -> Maybe a) -> (Nat -> Maybe b)
tabMap f g a =
    case g a of
        Nothing => Nothing
        (Just x) => Just (f x)


data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

example_tree : Tree Nat
example_tree = Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) 4 (Node Leaf 5 (Node Leaf 6 Leaf))


in_order : Tree a -> List a
in_order Leaf = []
in_order (Node x y z) = (in_order x) ++ [y] ++ (in_order z)

pre_order : Tree a -> List a
pre_order Leaf = []
pre_order (Node x y z) = [y] ++ (pre_order x) ++ (pre_order z)

post_order : Tree a -> List a
post_order Leaf = []
post_order (Node x y z) = (post_order x) ++ (post_order z) ++ [y]

insert : Nat -> Tree Nat -> Tree Nat
insert k Leaf = Node Leaf k Leaf
insert k (Node x y z) =
    case k > y of
        False => Node (insert k x) y z
        True => Node x y (insert k z)

sort : List Nat -> List Nat
sort xs = in_order (sort' xs Leaf)
    where
        sort' : List Nat -> Tree Nat -> Tree Nat
        sort' [] tree = tree
        sort' (x :: xs) tree = sort' xs (insert x tree)

Path : Type
Path = List Bool

follow : Path -> Tree a -> Maybe a
follow [] Leaf = Nothing
follow [] (Node x y z) = Just y
follow (False :: xs) Leaf = Nothing
follow (False :: xs) (Node x y z) = follow xs x
follow (True :: xs) Leaf = Nothing
follow (True :: xs) (Node x y z) = follow xs z

path_to : Nat -> Tree Nat -> Maybe Path
path_to val Leaf = Nothing
path_to val (Node x y z) =
    case y == val of
        True => Just []
        False => case val > y of
            True => case path_to val z of
                Nothing => Nothing
                (Just xs) => Just (True :: xs)
            False => case path_to val x of
                Nothing => Nothing
                (Just xs) => Just (False :: xs)
