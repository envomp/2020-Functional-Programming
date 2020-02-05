
myReverse: List ty -> List ty
myReverse [] = [] -- not needed, as the function head cant handle an empty List
myReverse (elem :: toReverse) = myReverse toReverse ++ [elem]

revString: String -> String
revString x = pack (myReverse (unpack x))

palindrome: String -> Bool
palindrome x = revString x == x

cycle: List ty -> Nat -> List ty
cycle stack Z = []
cycle stack (S x) = (cycle stack x) ++ stack

deal: List ty -> (List ty, List ty)
deal a = (evens a) (odds a)

odds: List ty -> List ty
odds [] = []
odds (elem :: toDeal) = if (mod elem 2 == 1) then (odds toDeal ++ [num]) else (odds toDeal)

evens: List ty -> List ty
evens [] = []
evens (num :: toDeal) = if ((mod num 2) == 0)
                        then ((evens toDeal) ++ [num])
                        else (evens toDeal)


top_three : List a -> List a
top_three array = a :: b :: c :: sort array && [a, b, c]
