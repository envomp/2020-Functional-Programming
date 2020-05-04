import Data.Vect

concat_list : List a -> List a -> List a
concat_list [] ys = ys
concat_list (x :: xs) ys = x :: concat_list xs ys

concat_vect : Vect m a -> Vect n a -> Vect (m + n) a
concat_vect [] ys = ys
concat_vect (x :: xs) ys = x :: concat_vect xs ys


zip_list : List a -> List b -> List (Pair a b)
zip_list [] [] = []
zip_list [] (y :: ys) = []
zip_list (x :: xs) [] = []
zip_list (x :: xs) (y :: ys) = (x, y) :: zip_list xs ys

replace_elt_list : (new : a) -> (index : Nat) -> List a -> Maybe (List a)
replace_elt_list new index [] = Nothing
replace_elt_list new Z (x :: xs) = Just (new :: xs)
replace_elt_list new (S k) (x :: xs) = case replace_elt_list new k xs of
                                            Nothing => Nothing
                                            (Just new_tail) => Just (x :: new_tail)


replace_elt_vect : (new : a) -> (index :Fin n) -> Vect n a -> Vect n a
replace_elt_vect new FZ (x :: xs)  =  new :: xs
replace_elt_vect new (FS n) (x :: xs)  =  x :: replace_elt_vect new n xs

forget_shape : Vect length a -> List a
forget_shape [] = []
forget_shape (x :: xs) = x :: forget_shape xs

learn_shape : (list : List a) -> Vect (length list) a
learn_shape [] = []
learn_shape (x :: xs) = x :: learn_shape xs
