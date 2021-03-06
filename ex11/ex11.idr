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
plus_assoc  :  {m , n , p : Nat} -> m + (n + p) = (m + n) + p
plus_assoc {m = m} {n = Z} {p = p}  =
	(m + (0 + p))
		={ cong {f = (m + )} plus_zero_left }=
	(m + p)
		={ cong {f = ( + p)} (sym plus_zero_right) }=
	((m + 0) + p)
		QED
plus_assoc {m = m} {n = (S n)} {p = p}  =
	(m + (S n + p))
		={ cong {f = (m + )} plus_succ_left }=
	(m + S (n + p))
		={ plus_succ_right }=
	(S (m + (n + p)))
		={ cong {f = S} plus_assoc }=
	(S ((m + n) + p))
		={ sym plus_succ_left }=
	(S(m + n) + p)
		={ cong {f = ( + p)} (sym plus_succ_right) }=
	((m + S n) + p)
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
times_succ_right {m = (S m)} {n = n} = cong {f = S} wasda where
	wasda : n + (m * (S n)) = m + (n + (m * n))
	wasda =
		(n + (m * (S n)))
			={ cong {f = (n +)} times_succ_right }=
		(n + (m + (m * n)))
			={ plus_assoc }=
		((n + m) + (m * n))
			={ cong {f = (+ (m * n))} plus_sym }=
		((m + n) + (m * n))
			={ sym plus_assoc }=
		(m + (n + (m * n)))
			QED

times_one_left : {n : Nat} -> 1 * n = n
times_one_left {n = n} = plus_zero_right

times_one_right : {n : Nat} -> n * 1 = n
times_one_right {n = n} =
	(n * 1)
		={ times_succ_right }=
	(n + (n * 0))
		={ cong {f = (n + )} times_zero_right }=
	(n + 0)
		={ plus_zero_right }=
	(n)
		QED

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
reverse_vect [] = []
reverse_vect (x :: xs) = replace {P = \t => Vect t a} (sym succ_is_plus_one) ((reverse_vect xs) ++ [x])
