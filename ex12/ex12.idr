import Syntax.PreorderReasoning
import Data.Vect

And  :  (a : Type) -> (b : Type) -> Type
And  =  Pair

Or  :  (a : Type) -> (b : Type) -> Type
Or  =  Either

contradiction  :  a -> (Not a) -> b
contradiction a_true a_false  =  void (a_false a_true)

contrapositive : (a -> b) -> Not b -> Not a
contrapositive f not_b = \x => not_b (f x)

dni : a -> Not $ Not a
dni x = \not_a => not_a x

tne : Not $ Not $ Not a -> Not a
tne x = \a => x (\not_a => x (\still_not_a => not_a a))

dm1 : Or (Not a) (Not b) -> Not (And a b)
dm1 (Left l) = \(a, b) => l a
dm1 (Right r) = \(a, b) => r b

dm2 : And (Not a) (Not b) -> Not (Or a b)
dm2 (not_a, not_b) = \a_or_b =>
    case a_or_b of
        (Left a) => not_a a
        (Right b) => not_b b

%hint
cons_equal : {xs, ys : Vect n a} -> x = y -> xs = ys -> x::xs = y::ys
cons_equal Refl Refl = Refl

%hint
decons_equal : {xs, ys : Vect n a} -> x::xs = y::ys -> And (x = y) (xs = ys)
decons_equal Refl = (Refl, Refl)

%hint
heads_differ : {xs, ys : Vect n a} -> Not (x = y) -> Not (x::xs = y::ys)
heads_differ diff_head = \Refl => diff_head Refl

%hint
tails_differ : {xs, ys : Vect n a} -> Not (xs = ys) -> Not (x::xs = y::ys)
tails_differ diff_tail = \Refl => diff_tail Refl

%hint
decons_differ : DecEq a => {xs, ys : Vect n a} -> Not (x::xs = y::ys) -> Or (Not (x = y)) (Not (xs = ys))
decons_differ not_same_vec = Left (\same_head => not_same_vec (cons_equal same_head ?G_4))


implementation [custom] DecEq a => DecEq (Vect n a) where
    decEq [] [] = Yes Refl
    decEq (x :: xs) (y :: ys) = Yes (cons_equal ?G_6 ?G_7)

    -- ()
    --     ={ ?G }=
    -- ()
    --     ={ ?G }=
    -- ()
    --     QED


    -- (m + (0 + p))
    --     ={ ?G }=
    -- (m + p)
    --     ={ ?G }=
    -- ((m + 0) + p)
    --     QED
