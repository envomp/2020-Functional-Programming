import Data.Vect

addvect : Vect m Int -> Vect m Int -> Vect m Int
-- addvect [] [] = []
-- addvect (x :: xs) (y :: ys) = x + y :: addvect xs ys
addvect = zipWith (+)

-- index 1 [0, 1]

forgetFirst: {k: Nat} -> (Fin (S k) -> ty) -> (Fin k -> ty)
forgetFirst f FZ = f (FS FZ)
forgetFirst f (FS m) = f (FS (FS m))

------

Matrix: (m: Nat) -> (n: Nat) -> Type
Matrix m n = Vect m (Vect n Int)

addMatrix: Matrix m n -> Matrix m n -> Matrix m n
addMatrix = zipWith addvect

-----

allZeros: (m: Nat) -> Vect m Int
allZeros m = replicate m 0

identity: (m: Nat) -> Matrix m m
identity Z = []
identity (S k) = (1 :: allZeros k) :: map (\v => 0 :: v) (identity k)

sumOfProducts: Vect m Int -> Vect m Int -> Int
sumOfProducts xs ys = sum (zipWith (*) xs ys)

-----

vectFromQuery: {m: Nat} -> (Fin m -> Int) -> Vect m Int
vectFromQuery {m = Z} f = []
vectFromQuery {m = (S k)} f = (f 0) :: (vectFromQuery (forgetFirst f))

matrixFromQuery: {m: Nat} -> {n: Nat} -> (Fin m -> Fin n -> Int) -> Matrix m n
matrixFromQuery {m = Z} {n = n} f = []
matrixFromQuery {m = (S k)} {n = n} f = vectFromQuery (f 0) :: (matrixFromQuery (forgetFirst f))

-----

getNth: Fin m -> Vect m ty -> ty
getNth FZ (x :: xs) = x
getNth (FS k) (x :: xs) = getNth k xs

getIJth: (i: Fin m) -> (j: Fin n) -> Matrix m n -> Int
getIJth i j x = getNth j (getNth i x)

getRow: Fin m -> Matrix m n -> Vect n Int
getRow = getNth

getColumn: Fin n -> Matrix m n -> Vect m Int
getColumn k a = vectFromQuery (\l => getIJth l k a)

getIJthProduct: Matrix m n -> Matrix n p -> Fin m -> Fin p -> Int
getIJthProduct a b k l = sumOfProducts (getRow k a) (getColumn l b)

matrixMultiply: Matrix m n -> Matrix n p -> Matrix m p
matrixMultiply a b = matrixFromQuery (getIJthProduct a b)
