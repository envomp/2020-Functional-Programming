
module Main

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
interactive_titlecase = do  input <- getLine
                            putStrLn (titlecase input)
                            interactive_titlecase

-- 4

is_vowel: Char -> Bool
is_vowel x = elem (toUpper x) ['A', 'E', 'I', 'O', 'U']

average: List Nat -> Double
average xs = (cast (sum xs)) / (cast (length xs))

avg_vowels: String -> Double
avg_vowels str = map(\b => filter(\a => is_vowel a)  (unpack b)) (words str)
