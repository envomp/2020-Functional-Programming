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


tails_differ' : {xs, ys : Vect n a} -> Not (x::xs = y::ys) -> (x = y) -> Not (xs = ys)
tails_differ' diff_list same_head = \same_tail => diff_list (cons_equal same_head same_tail)

%hint
decons_differ : DecEq a => {xs, ys : Vect n a} -> Not (x::xs = y::ys) -> Or (Not (x = y)) (Not (xs = ys))
decons_differ not_eq {x = x} {y = y} {xs = xs} {ys = ys} =
    case decEq x y of
        (Yes prf) => Right (tails_differ' not_eq prf)
        (No contra) => Left contra


implementation [custom] DecEq a => DecEq (Vect n a) where
    decEq [] [] = Yes Refl
    decEq (x :: xs) (y :: ys) =
        case decEq x y of
            (Yes prf_head) =>
                case decEq xs ys of
                    (Yes prf_tail) => Yes (cons_equal prf_head prf_tail)
                    (No contra_tail) => No (tails_differ contra_tail)
            (No contra_head) => No (heads_differ contra_head)
