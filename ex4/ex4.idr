import Data.String

printIfNeeded : Int -> Maybe Int -> IO Int
printIfNeeded sum maybe_int = case maybe_int of
    Just x  -> askInputRec (sum + x)
    Nothing -> putStrLn ("your sum is " ++ (show sum))

askInputRec : Int -> IO Int
askInputRec x = do putStrLn "enter a number:"
                   number <- getLine
                   printIfNeeded x (parseInteger number)

running_sum : IO Int
running_sum = askInputRec 0

--------------------------------------------------------
