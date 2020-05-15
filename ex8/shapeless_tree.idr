module ShapelessTree

% default total
% auto_implicits on
% access public export


data Tree : Type -> Type where
    Leaf : Tree a
    Node : (left : Tree a) -> (this : a) -> (right : Tree a) -> Tree a

zip_tree : Tree a -> Tree b -> Tree (Pair a b)
zip_tree Leaf Leaf = Leaf
zip_tree Leaf (Node left this right) = Leaf
zip_tree (Node left this right) Leaf = Leaf
zip_tree (Node left_1 this_1 right_1) (Node left_2 this_2 right_2) = Node (zip_tree left_1 left_2) (this_1, this_2) (zip_tree right_1 right_2)


data Path : Type where
    Here : Path
    Left : (path : Path) -> Path
    Right : (path : Path) -> Path


replace_node : (new : a) -> Path -> Tree a -> Maybe (Tree a)
replace_node new path Leaf = Nothing
replace_node new Here (Node left this right) = Just (Node left new right)
replace_node new (Left path) (Node left this right) =
    case replace_node new path left of
        Nothing => Nothing
        (Just new_left) => Just (Node new_left this right)
replace_node new (Right path) (Node left this right) =
    case replace_node new path right of
        Nothing => Nothing
        (Just new_right) => Just (Node left this new_right)

tree_graft : (branch : Tree a) -> (stalk : Tree a) -> (path : Path) -> Maybe (Tree a)
tree_graft branch Leaf Here = Just branch
tree_graft branch Leaf (Left path) = Nothing
tree_graft branch Leaf (Right path) = Nothing
tree_graft branch (Node left this right) Here = Nothing
tree_graft branch (Node left this right) (Left path) =
    case tree_graft branch left path of
         Nothing => Nothing
         (Just new_left) => Just (Node new_left this right)
tree_graft branch (Node left this right) (Right path) =
    case tree_graft branch right path of
         Nothing => Nothing
         (Just new_right) => Just (Node left this new_right)
