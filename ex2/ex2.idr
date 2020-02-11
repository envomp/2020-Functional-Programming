import Data.String

-- 1

myReverse': List ty -> List ty -> List ty
myReverse' acc [] = acc
myReverse' acc (x::xs) = myReverse' (x::acc) xs

myReverse: List ty -> List ty
myReverse x = myReverse' [] x

-- 2

sumlist: List Nat -> Nat
sumlist (x :: []) = x
sumlist (x :: xs) = x + sumlist xs

sumsquares: Nat -> Nat
sumsquares Z = Z
sumsquares (S a) = sumlist (map (\x => x * x) [0..a])

-- 3

interactive_addition: IO ()
interactive_addition = do   input <- getLine
                            print (sum (map (\f => parseInteger f) (words input)))
                            interactive_addition

-- TODO

-- 4

divisors: Integer -> List Integer
divisors 0 = []
divisors k = filter (\n => mod k n == 0) ([(- abs k)..(-1)] ++ [1..(abs k)])

posDivisors: Nat -> List Nat
posDivisors Z = []
posDivisors k = filter (\n => mod k n == Z) ([(S Z)..k])


-- 5

primality: Nat -> Bool
primality Z = False
primality (S Z) = False
primality n = (length (posDivisors n)) == S (S Z)
