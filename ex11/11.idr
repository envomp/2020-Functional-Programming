import Data.Vect
import Syntax.PreorderReasoning

%hint
times_zero_left : {n : Nat} -> 0 * n = 0
times_zero_left = Refl

%hint
times_zero_right : {n : Nat} -> n * 0 = 0
times_zero_right {n = Z} = Refl
times_zero_right {n = (S k)} = times_zero_right {n = k}

%hint
plus_zero_left  :  {n : Nat} -> 0 + n = n
plus_zero_left  =  Refl

%hint
plus_zero_right  :  {n : Nat} -> n + 0 = n
plus_zero_right {n = Z}  =  Refl
plus_zero_right {n = (S n)}  =  cong {f = S} plus_zero_right

%hint
plus_succ_left  :  {m , n : Nat} -> (S m) + n = S (m + n)
plus_succ_left  =  Refl


%hint
plus_succ_right  :  {m , n : Nat} -> m + (S n) = S (m + n)
plus_succ_right {m = Z} {n = n}  =  Refl
plus_succ_right {m = (S m)} {n = n}  =  cong {f = S} plus_succ_right

%hint
plus_sym  :  {m , n : Nat} -> m + n = n + m
plus_sym {m = Z} {n = n}  =
	(0 + n)
		={ plus_zero_left }=
	(n)
		={ sym plus_zero_right }=
	(n + 0)
		QED
plus_sym {m = (S m)} {n = n}  =
	(S m + n)
		={ plus_succ_left }=
	(S (m + n))
		={ cong {f = S} plus_sym }=
	(S (n + m))
		={ sym plus_succ_right }=
	(n + S m)
		QED

%hint
times_succ_left : {m , n : Nat} -> (S m) * n = (m * n) + n
times_succ_left {m = m} {n = n} =
    ((S m) * n)
        ={ Refl }=
    (n + m * n)
        ={ plus_sym }=
    (m * n + n)
        QED

times_succ_right : {m , n : Nat} -> m * (S n) = m + (m * n)
times_succ_right {m = Z} {n = n} = Refl
times_succ_right {m = (S k)} {n = n} = ?Refl_2

times_one_left : {n : Nat} -> 1 * n = n
times_one_left {n = Z} = Refl
times_one_left {n = (S k)} = times_one_left

times_one_right : {n : Nat} -> n * 1 = n
times_one_right {n = Z} = Refl
times_one_right {n = (S k)} = times_one_right

times_sym : {m , n : Nat} -> m * n = n * m
times_sym {m = Z} {n = n} =
    (0)
        ={ sym times_zero_right }=
    (mult n 0)
        QED

times_sym {m = (S k)} {n = n} =
    (n + k * n)
        ={ cong {f = (n + )} times_sym }=
    (n + n * k)
        ={ sym times_succ_right }=
    (n * (S k))
        QED

succ_is_plus_one : {n : Nat} -> S n = n + 1
succ_is_plus_one {n = Z} = Refl
succ_is_plus_one {n = (S k)} = cong {f = S} succ_is_plus_one

twisted_cons : a -> Vect n a -> Vect (n + 1) a
twisted_cons {n = n} x xs = replace {P = \t => Vect t a} succ_is_plus_one (x :: xs)

reverse_vect : Vect n a -> Vect n a
reverse_vect xs = reverse xs
