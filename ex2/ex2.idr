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
interactive_addition =
    do
        putStr "space-separated numbers to add:"
        line <- getLine
        putStrLn (case (getSum (words line)) of
            Nothing => "???"
            (Just x) => show x)
        interactive_addition

    where
        getSum : List String -> Maybe Integer
        getSum (x :: []) = parseInteger x
        getSum (x :: xs) =
            case getSum xs of
                Nothing => Nothing
                (Just y) =>
                    case parseInteger x of
                        Nothing => Nothing
                        (Just x) => Just (x + y)


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
