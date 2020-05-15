Name : Type
Name = String

Val : Type
Val = Double

Context : Type
Context = List (Name, Val)


data Expr : Type where
    Num : Val -> Expr
    Add : Expr -> Expr -> Expr
    Mul : Expr -> Expr -> Expr
    Sub : Expr -> Expr -> Expr
    Div : Expr -> Expr -> Expr
    Var : Name -> Expr

Show Expr where
  show (Num x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
  show (Var x) = x

ex : Expr
ex = Add (Num 2) (Mul (Num 3) (Div (Sub (Num 13) (Var "x")) (Num 5)))

co : Context
co = [("x", 3)]

size : Expr -> Nat
size (Num x) = Z
size (Add x y) = S (size x) + (size y)
size (Mul x y) = S (size x) + (size y)
size (Sub x y) = S (size x) + (size y)
size (Div x y) = S (size x) + (size y)
size (Var x) = Z

applicify : {t : Type -> Type} -> Applicative t => (op : a -> a -> a) -> t a -> t a -> t a
applicify op x y = pure op <*> x <*> y

infixl 7 +?
(+?) : Num a => Maybe a -> Maybe a -> Maybe a
(+?) = applicify (+)

infixl 7 *?
(*?) : Num a => Maybe a -> Maybe a -> Maybe a
(*?) = applicify (*)

find : Name -> Context -> Maybe Val
find x [] = Nothing
find x ((compare_x, val) :: ys) =
    case x == compare_x of
        False => find x ys
        True => Just val

eval : Context -> Expr -> Maybe Val
eval cont (Num x) = Just x
eval cont (Add x y) = (eval cont x) +? (eval cont y)
eval cont (Mul x y) = (eval cont x) *? (eval cont y)
eval cont (Sub x y) = pure (-) <*> (eval cont x) <*> (eval cont y)
eval cont (Div x y) = pure (/) <*> (eval cont x) <*> (eval cont y)
eval cont (Var x) = find x cont
