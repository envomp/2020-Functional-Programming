import Data.String
import IO

running_sum : IO Nat
running_sum = ask 0
    where
        ask : Nat -> IO Nat
        ask cur_sum =
            do
                putStrLn "Enter a number:"
                input <- getLine
                case the (Maybe Nat) (parsePositive input) of
                    Nothing => pure cur_sum
                    (Just x) => ask (cur_sum + x)

in_sequence : List (IO ()) -> IO ()
in_sequence (x :: []) = x
in_sequence (x :: (y :: xs)) =
    do
        x
        in_sequence (y :: xs)

collect_results : List (IO a) -> IO (List a)
collect_results [] = pure []
collect_results (x :: xs) =
    do
        head <- x
        tail <- collect_results xs
        pure (head :: tail)

once_definitely : String -> String -> (String -> Maybe a) -> IO a
once_definitely x y f =
    do
        putStrLn x
        input <- getLine
        case f input of
            Nothing =>
                do
                    putStrLn y
                    once_definitely x y f
            (Just x) => pure x

ensure_palindrome : Nat -> Maybe Nat
ensure_palindrome val =
    case (show val) == reverse (show val) of
        False => Nothing
        True => Just val

ensure_odd : Nat -> Maybe Nat
ensure_odd k =
    case (mod k 2) == 1 of
        False => Nothing
        True => Just k

ensure_prime : Nat -> Maybe Nat
ensure_prime Z = Nothing
ensure_prime (S Z) = Nothing
ensure_prime (S (S k)) = ensure_prime' (S (S Z)) (S (S k))
    where
        ensure_prime' : Nat -> Nat -> Maybe Nat
        ensure_prime' k j =
            if (k == j)
            then (Just j)
            else (
                if ((mod j k) == 0)
                then (Nothing)
                else (ensure_prime' (S k) j)
            )

unify_properties : List (Nat -> Maybe Nat) -> (Nat -> Maybe Nat)
unify_properties [] k = Just k
unify_properties (x :: xs) k =
    case x k of
          Nothing => Nothing
          (Just x) => unify_properties xs x

calc_sum : Nat -> Nat -> Integer -> Nat
calc_sum cur sum 4 = sum
calc_sum cur sum cnt =
    case (unify_properties [ensure_odd, ensure_prime, ensure_palindrome]) cur of
        Nothing => calc_sum (S cur) sum cnt
        (Just x) => calc_sum (S cur) (sum + x) (cnt + 1)
