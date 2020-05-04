

consolidate : List (Maybe a) -> Maybe (List a)
consolidate [] = pure []
consolidate (x :: xs) = map (++) Nothing <*> consolidate xs
