module HW3

import Syntax.PreorderReasoning
import Data.Vect

% default total
% auto_implicits on

data TreeShape : Type where
    LeafShape : TreeShape
    NodeShape : (l : TreeShape) -> (r : TreeShape) -> TreeShape

data Tree : TreeShape -> Type -> Type where
    Leaf : Tree LeafShape a
    Node : (left : Tree l a) -> (this : a) -> (right : Tree r a) -> Tree (NodeShape l r) a


||||||||||||||||||||||||||||||||| Testing ||||||||||||||||||||||||||||||||||||||

createTreeShape : TreeShape
createTreeShape = NodeShape (NodeShape LeafShape LeafShape) (NodeShape LeafShape LeafShape)

createTree1 : Tree (NodeShape (NodeShape ((NodeShape (NodeShape LeafShape LeafShape) (NodeShape LeafShape LeafShape))) LeafShape) (NodeShape LeafShape ((NodeShape (NodeShape LeafShape LeafShape) (NodeShape LeafShape LeafShape))))) Int
createTree1 = Node (Node (Node (Node Leaf 5 Leaf) 4 (Node Leaf 6 Leaf)) 1 Leaf) 2 (Node Leaf 3 (Node (Node Leaf 8 Leaf) 7 (Node Leaf 9 Leaf)))

createTree2 : Tree (NodeShape (NodeShape LeafShape LeafShape) (NodeShape LeafShape LeafShape)) (Tree (NodeShape (NodeShape LeafShape LeafShape) (NodeShape LeafShape LeafShape)) Int)
createTree2 = Node (Node Leaf (Node (Node Leaf 5 Leaf) 4 (Node Leaf 6 Leaf)) Leaf) (Node (Node Leaf 2 Leaf) 1 (Node Leaf 3 Leaf)) (Node Leaf (Node (Node Leaf 8 Leaf) 7 (Node Leaf 9 Leaf)) Leaf)


-- Problem 1: define Eq method for custom Tree type

implementation  Eq a => Eq (Tree shape a) where
	Leaf == Leaf = True
	(Node left_1 this_1 right_1) == (Node left_2 this_2 right_2) =
         left_1 == left_2 && right_1 == right_2 && this_1 == this_2


-- Problem 2: define a default implementation for Either

interface Bifunctor (t : Type -> Type -> Type) where
    bimap : (a -> b) -> (c -> d) -> t a c -> t b d

implementation Bifunctor Either where
	bimap l_f r_f (Left l) = Left (l_f l)
	bimap l_f r_f (Right r) = Right (r_f r)


-- Problem 3: Write Functor, Applicative, and Monad instances for shapely trees

implementation Functor (Tree a) where
	map f Leaf = Leaf
	map f (Node left this right) = Node (map f left) (f this) (map f right)


implementation Applicative (Tree shape) where
    pure {shape = LeafShape} val = Leaf
    pure {shape = (NodeShape l r)} val = Node (pure val) val (pure val)

    (<*>) Leaf Leaf = Leaf
    (<*>) (Node left_1 this_1 right_1) (Node left_2 this_2 right_2) = Node (left_1 <*> left_2) (this_1 this_2) (right_1 <*> right_2)


implementation Monad (Tree shape) where
    join {shape = LeafShape} Leaf = Leaf
    join {shape = (NodeShape l r)} (Node left this right) = Node (join (traverse_tree_left left)) (head this) (join (traverse_tree_right right))
        where
            head  :  Tree (NodeShape l r) a -> a
            head (Node left this right) = this

            left_tail  :  Tree (NodeShape l r) a -> Tree l a
            left_tail (Node left this right)  =  left

            right_tail  :  Tree (NodeShape l r) a -> Tree r a
            right_tail (Node left this right)  =  right

            traverse_tree_left : Tree shape (Tree (NodeShape l r) a) -> Tree shape (Tree l a)
            traverse_tree_left Leaf = Leaf
            traverse_tree_left (Node left this right) = Node (traverse_tree_left left) (left_tail this) (traverse_tree_left right)

            traverse_tree_right : Tree shape (Tree (NodeShape l r) a) -> Tree shape (Tree r a)
            traverse_tree_right Leaf = Leaf
            traverse_tree_right (Node left this right) = Node (traverse_tree_right left) (right_tail this) (traverse_tree_right right)


|||||||||||||||||||||||||||| Helper functions ||||||||||||||||||||||||||||||||||

%hint
pred_equal : {m , n : Nat} -> S m = S n -> m = n
pred_equal Refl = Refl

%hint
plus_zero_right  :  {n : Nat} -> n + 0 = n
plus_zero_right {n = Z}  =  Refl
plus_zero_right {n = (S n)}  =  cong {f = S} plus_zero_right

%hint
plus_zero_left  :  {n : Nat} -> 0 + n = n
plus_zero_left  =  Refl

%hint
plus_succ_left  :  {m , n : Nat} -> (S m) + n = S (m + n)
plus_succ_left  =  Refl

%hint
plus_succ_right  :  {m , n : Nat} -> m + (S n) = S (m + n)
plus_succ_right {m = Z} {n = n}  =  Refl
plus_succ_right {m = (S m)} {n = n}  =  cong {f = S} plus_succ_right

%hint
plus_sym  :  {m , n : Nat} -> m + n = n + m
plus_sym {m = Z} {n = n}  =
	(0 + n)
		={ plus_zero_left }=
	(n)
		={ sym plus_zero_right }=
	(n + 0)
		QED
plus_sym {m = (S m)} {n = n}  =
	(S m + n)
		={ plus_succ_left }=
	(S (m + n))
		={ cong {f = S} plus_sym }=
	(S (n + m))
		={ sym plus_succ_right }=
	(n + S m)
		QED


-- Problem 4: Convince Idris that addition is injective in both its right and left arguments

plus_inj_right : {m, n, k : Nat} -> m + n = m + k -> n = k
plus_inj_right {m = Z} {n = k} {k = k} Refl = Refl
plus_inj_right {m = (S m')} prf = plus_inj_right (pred_equal prf)

plus_succ : {m, n, k : Nat} ->  k + (S m) = n + (S m) -> S (k + m) = S (n + m)
plus_succ {m = m} {n = n} {k = k} prf =
    (S (k + m))
        ={ sym plus_succ_right }=
    (k + (S m))
        ={ prf }=
    (n + (S m))
        ={ plus_succ_right }=
    (S (n + m))
        QED

plus_inj_left : {m, n, k : Nat} -> n + m = k + m -> n = k
plus_inj_left {m = Z} {n = n} {k = k} prf =
    (n)
        ={ sym plus_zero_right }=
    (n + Z)
        ={ prf }=
    (k + Z)
        ={ plus_zero_right }=
    (k)
        QED

plus_inj_left {m = (S m')} prf = plus_inj_left (pred_equal (plus_succ prf))


-- Problem 5: Convince Idris that if the sum of two numbers is even then the sum of the same two numbers in the opposite order is also even

data  Even  :  (n : Nat) -> Type  where
	Z_even   :  Even Z
	SS_even  :  Even n -> Even (S (S n))

four_even  :  Even 4
four_even  =  SS_even (SS_even Z_even)

even_plus_even  :  Even m -> Even n -> Even (m + n)
even_plus_even Z_even n_even  =  n_even
even_plus_even (SS_even m_even) n_even  =  SS_even (even_plus_even m_even n_even)

even_plus_sym : {m , n : Nat} -> Even (m + n) -> Even (n + m)
even_plus_sym {m = m} {n = n} prf = replace plus_sym prf


-- Problem 6: Write a function that cyclically permutes the elements of a vector by a given number of positions

rotate_vect : Nat -> Vect n a -> Vect n a
rotate_vect Z xs = xs
rotate_vect (S k) [] = []
rotate_vect (S k) (x :: xs) = rotate_vect k (reverse (x :: (reverse xs)))
