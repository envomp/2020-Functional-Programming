import Data.Vect

interface   Preorder (a : Type)  where
  leq : a -> a -> Bool


implementation Eq a => Preorder (List a) where
    leq [] ys = True
    leq (x :: xs) ys =
        case elem x ys of
            False => False
            True => leq xs (delete x ys)


implementation [Multiset] Eq a => Eq (List a) where
    xs == ys = leq xs ys


consolidate : List (Maybe a) -> Maybe (List a)
consolidate [] = pure []
consolidate (x :: xs) = pure (++) <*> (pure (\f => f :: []) <*> x) <*> consolidate xs

applicify : {t : Type -> Type} -> Applicative t => (op : a -> a -> a) -> t a -> t a -> t a
applicify op x y = pure op <*> x <*> y

infixl 7 +*
(+*) : Num a => Vect n a -> Vect n a -> Vect n a
(+*) = applicify (+)

infixl 7 +?
(+?) : Num a => Maybe a -> Maybe a -> Maybe a
(+?) = applicify (+)

implementation [wasd] Applicative (List) where
    pure a = a :: []

    (<*>) f [] = []
    (<*>) (y :: ys) (x :: xs) = (y x) :: ((y :: ys) <*> xs)
    (<*>) [] (x :: xs) = []
