import Syntax.PreorderReasoning

data  Even  :  (n : Nat) -> Type  where
	Z_even   :  Even Z
	SS_even  :  Even n -> Even (S (S n))

%hint
pp_even  :  Even (S (S n)) -> Even n
pp_even (SS_even n_even)  =  n_even

%hint
even_plus_even  :  Even m -> Even n -> Even (m + n)
even_plus_even Z_even n_even  =  n_even
even_plus_even (SS_even m_even) n_even  =  SS_even (even_plus_even m_even n_even)

%hint
even_times_even  :  Even m -> Even n -> Even (m * n)
even_times_even Z_even n_even  =  Z_even
even_times_even (SS_even m_even) n_even  =
	even_plus_even n_even (even_plus_even n_even (even_times_even m_even n_even))


data Positive : Nat -> Type where
    One_positive : Positive (S Z)
    S_positive : Positive n -> Positive (S n)

%hint
even_times_one : Even n -> Even (n * 1)
even_times_one Z_even = Z_even
even_times_one (SS_even x) = SS_even (even_times_one x)

%hint
pow_even_pos : Even m -> Positive n -> Even (power m n)
pow_even_pos base One_positive = even_times_one base
pow_even_pos base (S_positive pow) = even_times_even base (pow_even_pos base pow)


data  LEQ  :  (m : Nat) -> (n : Nat) -> Type  where
	Z_leq  :  LEQ Z n
	S_leq  :  LEQ m n -> LEQ (S m) (S n)

%hint
leq_refl  :  LEQ n n
leq_refl {n = Z}  =  Z_leq
leq_refl {n = (S n)}  =  S_leq leq_refl

leq_trans  :  LEQ l m -> LEQ m n -> LEQ l n
leq_trans Z_leq _  =  Z_leq
leq_trans {l = S l} (S_leq l_leq_m) {m = S m} (S_leq m_leq_n) {n = S n}  =
	S_leq (leq_trans l_leq_m m_leq_n)


interface  Preorder  (rel : a -> a -> Type)  where
	reflexive  :  {x : a} -> rel x x
	transitive :  {x , y , z : a} -> rel x y -> rel y z -> rel x z

implementation  Preorder LEQ  where
	reflexive  =  leq_refl
	transitive  =  leq_trans

%hint
leq_pred  :  LEQ (S m) (S n) -> LEQ m n
leq_pred (S_leq m_leq_n)  =  m_leq_n

%hint
succ_larger  :  LEQ n (S n)
succ_larger {n = Z}  =  Z_leq
succ_larger {n = S n}  =  S_leq succ_larger

%hint
pred_smaller  :  LEQ (S m) n -> LEQ m n
pred_smaller sm_leq_n  =  transitive succ_larger sm_leq_n

%hint
zero_plus_right : LEQ (m + 0) (m + n)
zero_plus_right {m = Z} = Z_leq
zero_plus_right {m = (S m)} = S_leq zero_plus_right

%hint
zero_plus_left  :  LEQ (0 + n) (m + n)
zero_plus_left {n = Z} = Z_leq
zero_plus_left {n = (S n)} {m = Z} = S_leq leq_refl
zero_plus_left {n = (S n)} {m = (S m)} = S_leq (pred_smaller zero_plus_left)

%hint
plus_mono_right : LEQ i j -> LEQ (m + i) (m + j)
plus_mono_right Z_leq = zero_plus_right
plus_mono_right (S_leq prf) {i = S i} {j = S j} {m = Z} = S_leq prf
plus_mono_right (S_leq prf) {i = S i} {j = S j} {m = (S m)} = S_leq (plus_mono_right (S_leq prf))

%hint
plus_mono_left : LEQ i j -> LEQ (i + n) (j + n)
plus_mono_left Z_leq = zero_plus_left
plus_mono_left (S_leq prf) = S_leq (plus_mono_left prf)

%hint
plus_mono : LEQ i j -> LEQ m n -> LEQ (i + m) (j + n)
plus_mono x y = leq_trans (plus_mono_left x) (plus_mono_right y)
