import Data.List

-- 1

differences: List Integer -> List Integer
differences [] = []
differences (x :: []) = []
differences (a :: b :: x) = (b - a) :: differences (b :: x)

-- 2

customPack: List Char -> String
customPack (_head :: _tail) = pack ([toUpper _head] ++ _tail)

titlecase: String -> String
titlecase str =  unwords (map (\a => customPack (unpack a)) (words str))

-- 3

interactive_titlecase: IO ()
interactive_titlecase = repl "\n" titlecase
-- :exec interactive_titlecase

-- 4

is_vowel: Char -> Bool
is_vowel x = elem (toUpper x) ['A', 'E', 'I', 'O', 'U']

average: List Nat -> Double
average xs = (cast (sum xs)) / (cast (length xs))

avg_vowels: String -> Double
avg_vowels str = average (map (\c => length(c)) (map(\b => filter(\a => is_vowel a) (unpack b)) (words str)))

-- 5

satInBoth : (Eq t) => (t -> Bool) -> List t -> List t -> List t
satInBoth predicate x y = filter (\f => predicate f) (intersect x y)

-- 6

ack: Nat -> Nat -> Nat
ack Z n = n + 1
ack (S m) Z = ack (m) 1
ack (S m) (S n) = ack m (ack (m + 1) n)

-- 7

min_max': List Integer -> (Integer, Integer) -> (Integer, Integer)
min_max' [] (mi, ma) = (mi, ma)
min_max' (_head :: _tail) (mi, ma) = min_max' _tail ((min _head mi), (max _head ma))

least_greatest: Integer -> List Integer -> (Integer, Integer)
least_greatest default [] = (default, default)
least_greatest default xs = min_max' xs (default, default)

-- 8

sumEvensRecc: Nat -> Nat -> Nat
sumEvensRecc Z Z = Z
sumEvensRecc (S n) Z = sumEvensRecc n (S Z)
sumEvensRecc (S n) m = (sumEvensRecc n Z) + n

sumevens: Nat -> Nat
sumevens n = sumEvensRecc (S n) (mod (S n) (S(S Z)))

-- 9

posDivisors: Nat -> List Nat
posDivisors Z = []
posDivisors k = filter (\n => mod k n == Z) ([(S Z)..k])

primality: Nat -> Bool
primality Z = False
primality (S Z) = False
primality n = (length (posDivisors n)) == S (S Z)

sum_primes: Nat -> Nat
sum_primes Z = Z
sum_primes (S n) = if (primality (S n)) then (sum_primes n + (S n)) else (sum_primes n)
