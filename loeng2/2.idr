-- :let a = 2
-- :let the (List Int) = []
-- :let xs (List Int) = [3,5,7]
-- a :: xs -- [2, 3, 5, 7]
-- 1 :: 2 :: 3 :: [] -- [1, 2, 3]
-- length [1, 2] -- 2

-- [1..5] -- [1, 2, 3, 4, 5]
-- [1.3..7] -- [1, 3, 5, 7]
-- [5..1] -- [5, 4, 3, 2, 1]

len : List Int -> Int
len [] = 0
len (x :: xs) = 1 + (len xs)

repeat : ty -> Nat -> (List ty)
repeat x Z = []
repeat x (S k) = x :: (repeat x k)


stutter: (List ty) -> Nat -> (List ty)
stutter [] k = []
stutter (x :: xs) k = (repeat x k) ++ (stutter xs k)

record Address where
  constructor MkAddress
  number: Int
