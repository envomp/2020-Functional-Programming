
-- 1

myReverse: List ty -> List ty
myReverse [] = [] -- not needed, as the function head cant handle an empty List
myReverse (elem :: toReverse) = myReverse toReverse ++ [elem]

-- 2

revString: String -> String
revString x = pack (myReverse (unpack x))

-- 3

palindrome: String -> Bool
palindrome x = revString x == x

-- 4

cycle: List ty -> Nat -> List ty
cycle stack Z = []
cycle stack (S x) = (cycle stack x) ++ stack

-- 5

odds: List ty -> List ty
odds [] = []
odds (a :: b :: xs) = (a :: odds xs)
odds (a :: xs) = [a]

evens: List ty -> List ty
evens [] = []
evens (a :: b :: xs) = (b :: evens xs)
evens (a :: xs) = []

deal: List ty -> (List ty, List ty)
deal a = ((evens a), (odds a))

-- 6

top_three : List Integer -> List Integer
top_three array = take 3 (myReverse (sort array))

-- 7

unzipLeft: List (ty, ty') -> List ty
unzipLeft ((a, b) :: []) = [a]
unzipLeft ((a, b) :: array) = unzipLeft array ++ [a]


unzipRight: List (ty, ty') -> List ty'
unzipRight ((a, b) :: []) = [b]
unzipRight ((a, b) :: array) = unzipRight array ++ [b]


myUnzip: List (ty, ty') -> (List ty, List ty')
myUnzip array = ((unzipLeft array), (unzipRight array))

-- 8

record Street where
  constructor MkStreet
  number: Int
  street : String


record Address where
  constructor MkAddress
  country: String
  city: String
  postcode: Integer
  street': Street

  -- :let myStreet = MkStreet 10 "Akadeemia tee"
  -- :let myAddress = MkAddress "Country" "City" 123 myStreet

getStreet: Address -> Street
getStreet (MkAddress _ _ _ street) = street

setStreet: Street -> Address -> Address
setStreet (newStreet) (MkAddress a b c _) = (MkAddress a b c newStreet)
