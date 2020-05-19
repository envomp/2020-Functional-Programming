-----------------------------------------------
-------------------- 1 & 2 --------------------
-----------------------------------------------


unpack: String -> List
pack: List String -> String
sort: List a -> List a
take: Nat -> List
map: f(x)->a List
sum: List
filter: f(x)->bool listOfElems
mod: Number -> Number -> Number
parseInteger: String -> Integer
words: String -> List
repl: String -> (String -> String) -> IO()
zip: List a -> List b -> List (a, b)
zipWith: (f(a, b) -> c) -> List a -> List b -> List c
replicate: Nat -> a -> List a

record Street where
  constructor MkStreet  -- :let myStreet = MkStreet 10 "Akadeemia tee"
  number: Int
  street : String

getStreet: Address -> Street
getStreet x = MkStreet (number x) (street x)

setStreet: Street -> Address -> Address
setStreet (newStreet) (MkAddress a b c _) = (MkAddress a b c newStreet)

-----------------------------------------------
-------------------- 3 & 4 --------------------
-----------------------------------------------

runner_sum: Nat -> IO Nat
runner_sum k = do
              putStrLn "enter a number:"
              a <- getLine
              case the (Maybe Nat) (parsePositive a) of
                Just x => runner_sum (k + x)
                Nothing => pure k
running_sum: IO Nat
running_sum = runner_sum 0

Matrix: (m: Nat) -> (n: Nat) -> Type
Matrix m n = Vect m (Vect n Int)

transposeVector: {n: Nat} -> Vect n t -> Vect n (Vect 1 t)
transposeVector [] = []
transposeVector (x :: xs) = [x] :: transposeVector xs

transposeMatrix: {t: Type} -> {m, n: Nat} -> Matrix m n t -> Matrix n m t
transposeMatrix {m = Z} {n = n} x = replicate n []
transposeMatrix {m = (S k)} {n = n} (x :: xs) = zipWith (++) (transposeVector x) (transposeMatrix xs)

-----------------------------------------------
-------------------- 5 & 6 --------------------
-----------------------------------------------

zero_to_nine : (Nat -> Maybe Nat)
zero_to_nine n = if n < 10 then Just n else Nothing

data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

Path : Type
Path = List Bool

andList : List Bool -> Bool
andList xs = foldr (\a, b => a && b) True xs

foldTree : b -> (b -> a -> b -> b) -> Tree a -> b
foldTree l n Leaf = l
foldTree l n (Node tl x tr) = n (foldTree l n tl) x (foldTree l n tr)

andTree : Tree Bool -> Bool
andTree tree = foldTree True (\left, x, right => left && x && right) tree

-----------------------------------------------
-------------------- 7 & 8 --------------------
-----------------------------------------------

data TreeShape : Type where
  LeafShape : TreeShape
  NodeShape : (l : TreeShape) -> (r : TreeShape) -> TreeShape

data Tree : TreeShape -> Type -> Type where
  Leaf : Tree LeafShape a
  Node : (left : Tree l a) -> (this : a) -> (right : Tree r a) -> Tree (NodeShape l r) a

compute_shape : (tree : ShapelessTree.Tree type) -> TreeShape
compute_shape Leaf = LeafShape
compute_shape (Node left this right) = NodeShape (compute_shape left) (compute_shape right)

learn_shape : (tree : ShapelessTree.Tree type) -> ShapelyTree.Tree (compute_shape tree) type
learn_shape Leaf = Leaf
learn_shape (Node left this right) = Node (learn_shape left) this (learn_shape right)

-----------------------------------------------
-------------------- 9 & 10 -------------------
-----------------------------------------------

implementation  Eq a => Eq (Tree shape a) where       # Eq => a    --  eeldus, et a on võrreldav
	Case == Case	=  True
	_ == _     	=  False


implementation Bifunctor Either where
	bimap l_f r_f (Left l) = Left (l_f l)
	bimap l_f r_f (Right r) = Right (r_f r)


implementation Functor (Tree a) where
	map f Leaf = Leaf
	map f (Node left this right) = Node (map f left) (f this) (map f right)


implementation Applicative (Tree shape) where
    pure {shape = LeafShape} val = Leaf      -- wrappimine
    pure {shape = (NodeShape l r)} val = Node (pure val) val (pure val)

    (<*>) Leaf Leaf = Leaf      # wrappitud funktsiooni rakendamine
    (<*>) (Node left_1 this_1 right_1) (Node left_2 this_2 right_2) = Node (left_1 <*> left_2) (this_1 this_2) (right_1 <*> right_2)

implementation Monad (Tree shape) where       -- dimensionaalsuse vähendamine
    join {shape = LeafShape} Leaf = Leaf
    join {shape = (NodeShape l r)} (Node left this right) = Node (join (traverse_tree_left left)) (head this) (join (traverse_tree_right right))

-----------------------------------------------
------------------- 11 & 12 -------------------
-----------------------------------------------

import Syntax.PreorderReasoning
((m_s + n) + (m_s * n))
  ={ sym plus_assoc }=
(m_s + (n + (m_s * n)))
  QED

reverse_vect  :  Vect n a -> Vect n a
reverse_vect [] = []
reverse_vect (x :: xs) {n = (S n_s)} {a = a} = replace {P = \y => Vect y a} plus_one_is_succ ((reverse_vect xs) ++ [x])

plus_one_is_succ : {a: Nat} -> a + 1 = S a
plus_one_is_succ {a = Z} = Refl
plus_one_is_succ {a = (S k)} = cong {f = S} plus_one_is_succ


implementation [custom] DecEq a => DecEq (Vect n a)  where
  decEq [] []  =  Yes Refl
  decEq (x :: xs) (y :: ys)  =
    case decEq x y of
      Yes prf_h =>
        case decEq xs ys of
          Yes prf_t => Yes (cons_equal prf_h prf_t)
          No contra => No (tails_differ contra)
      No contra => No (heads_differ contra)
