import Data.String
import IO

-- printIfNeeded : Int -> Maybe Int -> IO Int
-- printIfNeeded sum maybe_int = case maybe_int of
--     Just x  => askInputRec (sum + x)
--     Nothing => putStrLn ("your sum is " ++ (show sum))
--
-- askInputRec : Int -> IO Int
-- askInputRec x = do putStrLn "enter a number:"
--                    number <- getLine
--                    printIfNeeded x (parseInteger number)
--
-- running_sum : IO Int
-- running_sum = askInputRec 0

--------------------------------------------------------

in_sequence : List (IO ()) -> IO ()
in_sequence (x :: []) = x
in_sequence (x :: xs) = do x
                           in_sequence xs

--------------------------------------------------------

collect_results : List (IO a) -> IO (List a) -> IO (List a)
collect_results [] ys = ys
collect_results (x :: xs) ys = do io_move <- x
                                  collect_results xs (io_move :: ys)

collect_sequence : List (IO a) -> IO (List a)
collect_sequence x = collect_results x (pure [])
