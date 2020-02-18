import Data.Vect

pair : (c -> a) -> (c -> b) -> (c -> (a,b))
pair f g x = (f x, g x)

copair: (a -> c) -> (b -> c) -> (Either a b -> c)
copair f g (Left l) = f l
copair f g (Right r) = g r

showw: Either Bool Int -> String
-- show l = copair (\x: Bool => "Bool: " ++ show l) (\x: Int => "Int: " ++ show l)
showw (Left l) = "Bool: " ++ show l
showw (Right r) = "Int: " ++ show r

fourints : Vect 4 Int
fourints = [0, 1, 2, 3]

sixints : Vect 6 Int
sixints = [4, 5, 6, 7, 8, 9]

tenints : Vect 10 Int
tenints = fourints ++ sixints

add : Vect m Int -> Vect m Int -> Vect m Int
add x y = zipWith (+) x y

my_reverse: List ty -> List ty
my_reverse [] = []
my_reverse (x :: xs) = (my_reverse xs) ++ [x]

concatt : Vect m ty -> Vect n ty -> Vect (m+n) ty
concatt [] [] = []
concatt [] (x :: xs) = x :: xs
concatt (x :: xs) [] = x :: concatt xs []
concatt (x :: xs) (y :: ys) = y :: concatt xs (y :: ys)

zerovect: Vect m Int
zerovect {m = Z} = []
zerovect {m = (S k)} = 0 :: zerovect

onevect: Vect m Int
onevect {m = Z} = []
onevect {m = (S k)} = 1 :: zerovect
