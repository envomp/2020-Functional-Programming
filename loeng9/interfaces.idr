import Data.Vect


% default total
% auto_implicits on




--  use the Show instance for Nat:
verbose_add  :  Nat -> Nat -> String
verbose_add  x y  =  show x ++ " + " ++ show y ++ " = " ++ show (x + y)




-- define an alternate Show instance for List:
implementation [ListShow] Show a => Show (List a)  where
	-- show  :  Show a => List a -> String
	show []  =  "Nil"
	show (x :: xs)  =  show x ++ " :: " ++ show xs




--  use the Eq interface to count occurrences:
multiplicity  :  Eq a => a -> List a -> Nat
multiplicity target list  =  length (filter (target == ) list)


-- redefine the Eq instance for Nat
implementation [NatEq] Eq Nat  where
	-- (==)  :  Nat -> Nat -> Bool
	Z == Z  =  True
	(S m) == (S n)  =  m == n
	_ == _  =  False




-- use an Ord instance to see if a list is sorted:
is_sorted  :  Ord a => List a -> Bool
is_sorted []  =  True
is_sorted (x :: [])  =  True
is_sorted (x :: xs @ (y :: ys))  =  x <= y && sorted xs


-- redefine the Ord instance for Pair:
implementation [Lexicographic] (Ord a , Ord b) => Ord (Pair a b)  where
	compare (x1 , y1) (x2 , y2)  =
		case  compare x1 x2  of
			LT  =>  LT
			EQ  => compare y1 y2
			GT  =>  GT



--  use the Cast interface to convert from Nat to Double:
average  :  Vect (S n) Double -> Double
average xs  =  sum xs / cast (length xs)


--  define a Cast instance from Vect n to List:
implementation Cast (Vect n a) (List a)  where
	-- cast  :  Vect n a -> List a
	cast []  =  []
	cast (x :: xs)  =  x :: cast xs




	-- Algebraic Interfaces


-- use the semigroup instance for strings:
hi  :  String
hi  =  "hello" <+> " " <+> "world"


--  redefine the Semigroup instance for List:
implementation [ListSemigroup] Semigroup (List a)  where
	-- (<+>)  :  List a -> List a -> List a
	(<+>)  =  (++)




--  redefine the Monoid instance for List:
implementation [ListMonoid] Monoid (List a) using ListSemigroup where
	-- neutral  :  List a
	neutral  =  []




	-- Categorical Interfaces


--  redefine the Functor instance for Maybe:
implementation [MaybeFunctor] Functor Maybe  where
	-- map  :  (a -> b) -> (Maybe a -> Maybe b)
	map f Nothing  =  Nothing
	map f (Just x)  =  Just (f x)


--  use the Functor instance for Maybe:
replace_elt  :  (new : a) -> (index : Nat) -> List a -> Maybe (List a)
replace_elt new index []  =  Nothing
replace_elt new Z (x :: xs)  =  Just (new :: xs)
replace_elt new (S n) (x :: xs)  =  map (x :: ) (replace_elt new n xs)


--  redefine the Functor instance for List:
implementation [ListFunctor] Functor List  where
	-- map  :  (a -> b) -> List a -> List b
	map f []  =  []
	map f (x :: xs)  =  f x :: map f xs


--  use the functor instance on lists and maybes:
characterize_grades  :  List (Maybe Nat) -> List (Maybe String)
characterize_grades  =  map (map characterize_grade)
	where
	characterize_grade  :  Nat -> String
	characterize_grade n  =
		case  n >= 50  of
			False  =>  "bad"
			True  =>  "good"




--  use the applicative instance for Vect n:
zip_with  :  (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zip_with f xs ys  =  pure f <*> xs <*> ys
{-
f  :  a -> b -> c
pure f : Vect n (a -> b -> c)
(pure f <*> ) : Vect n a -> Vect n (b -> c)
pure f <*> xs : Vect n (b -> c)
(pure f <*> xs <*> ) : Vect n b -> Vect n c
pure f <*> xs <*> ys : Vect n c
 -}


--  recovering Functor.map from Applicative structure:
map'  :  {t : Type -> Type} -> Applicative t => (f : a -> b) -> t a -> t b
map' f x  =  pure f <*> x
{-
f  :  a -> b
pure f  :  t (a -> b)
(pure f <*> )  :  t a -> t b
pure f <*> x  :  t b
-}




--  redefine the Monad instance for Maybe:
implementation [MaybeMonad] Monad Maybe  where
	-- join  :  Maybe (Maybe a) -> Maybe a
	join Nothing  =  Nothing
	join (Just Nothing)  =  Nothing
	join (Just (Just x))  =  Just x


--  redefine the Monad instance for List:
implementation [ListMonad] Monad List  where
	-- join  :  List (List a) -> List a
	join []  =  []
	join (xs :: xss)  =  xs <+> join xss




{-
	join and >>= are interdefinable.
	to understand this it helps to define the the "kleisli extension"
	of a function f : a -> t b for a monad t:
				:
				t (t a)  t (t b)
				         7  |
				map f /     | join {b}
				   /        v
				t a        t b
				         7
				   f  /
				   /
				 a           b
 -}
extend  :  Monad t => (a -> t b) -> (t a -> t b)
extend f  =  join . map f


--  "bind" is the name of the infix operator (>>=)
--  which is the basis for the syntactic sugar of do notation
--  it is just the same as extend, with its argument swapped:
bind  :  Monad t => t a -> (a -> t b) -> t b
bind  =  flip extend


{-
	if we have >>= (or equivalently, extend) then we can define join:
				t (t a)
				      \
				        \  extend id
				          V
				t a - - - > t a
				      id
 -}
join'  :  Monad t => t (t a) -> t a
join'  =  extend id






--  Writing our own Interfaces:


--  specifying an interface for bifunctors
--  for type constructors that take two parameters:
interface  Bifunctor (t : Type -> Type -> Type)  where
	bimap  :  (a -> b) -> (c -> d) -> t a c -> t b d


--  define the bifunctor instance for Pairs:
implementation Bifunctor Pair  where
	--bimap  :  (a -> b) -> (c -> d) -> (Pair a c -> Pair b d)
	bimap f g (x , y)  =  (f x , g y)




--  interfaces involving zero variiables can act as global constants

interface  Constants  where
	mood  :  String
	grading_difficulty  :  String
	lucky_number  :  Nat


--  we can give them a default implementation:
implementation  Constants  where
	mood  =  "bad"
	grading_difficulty  =  "hard"
	lucky_number  =  7


--  or we can give them a named implementation:
implementation [happy]  Constants  where
	mood  =  "good"
	grading_difficulty  =  "easy"
	lucky_number  =  42


--  we can even write interfaces where the variables
--  range over things that are not types or type constructors:
interface  Length (n : Nat)  where
	numbers  :  Vect n Integer

implementation  Length 2  where
	numbers  =  [7 , 11]

implementation  Length 3  where
	numbers  =  replicate _ 7

--  although in order to use it we need to help Idris
--  by telling it the instance we want
