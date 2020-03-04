import Data.Vect

Matrix : Nat -> Nat -> Type -> Type
Matrix m n t = Vect m (Vect n t)

--------------------------------------------------------------

add : {m , n : Nat} -> Matrix m n Integer -> Matrix m n Integer -> Matrix m n Integer
add [] [] = []
add (x :: xs) (y :: ys) = (zipWith (+) y x) :: add xs ys

--------------------------------------------------------------

transposeVector : {t : Type} ->  {n : Nat} -> Vect n t -> Vect n (Vect 1 t)
transposeVector [] = []
transposeVector (x :: xs) = [x] :: transposeVector xs

transposeMatrix : {t : Type} -> {m , n : Nat} -> Matrix m n t -> Matrix n m t
transposeMatrix {n = n} [] = replicate n []
transposeMatrix (x :: xs) = zipWith (++) (transposeVector x) (transposeMatrix xs)

--------------------------------------------------------------

sumOfProducts: Vect m Integer -> Vect m Integer -> Integer
sumOfProducts xs ys = sum (zipWith (*) xs ys)

--------------------------------------------------------------

mult : {m : Nat} -> {n : Nat} -> Matrix m n Integer -> {p : Nat} -> Matrix n p Integer -> Matrix m p Integer
mult [] y = []
mult (x :: xs) y = let rest_rows = mult xs y
                       row = map (\i => sumOfProducts x i) (transposeMatrix y)
                   in row :: rest_rows

--------------------------------------------------------------

elem_mult : {m , n : Nat} -> Fin m -> Integer -> Matrix m n Integer -> Matrix m n Integer
elem_mult FZ factor matrix = matrix
elem_mult (FS FZ) factor (row :: others) = (map (\i => i * factor) row) :: others
elem_mult (FS (FS k)) factor (start :: matrix) = start :: (elem_mult (FS k) factor matrix)
