module ShapelyTree

% default total
% auto_implicits on
% access public export


data TreeShape : Type where
    LeafShape : TreeShape
    NodeShape : (l : TreeShape) -> (r : TreeShape) -> TreeShape

data Tree : TreeShape -> Type -> Type where
    Leaf : Tree LeafShape a
    Node : (left : Tree l a) -> (this : a) -> (right : Tree r a) -> Tree (NodeShape l r) a

data PathTo : (target_shape : TreeShape) -> (tree_shape : TreeShape) -> Type where
    Here : PathTo target_shape target_shape
    Left : (path : PathTo target_shape l) -> PathTo target_shape (NodeShape l r)
    Right : (path : PathTo target_shape r) -> PathTo target_shape (NodeShape l r)

replace_node : (new : a) -> PathTo (NodeShape l r) shape -> Tree shape a -> Tree shape a
replace_node new Here (Node left this right) = Node left new right
replace_node new (Left path) (Node left this right) = Node (replace_node new path left) this right
replace_node new (Right path) (Node left this right) = Node left this  (replace_node new path right)


shape_graft : (branch_shape : TreeShape) -> (stalk_shape : TreeShape) -> (path : PathTo LeafShape stalk_shape) -> TreeShape
shape_graft branch_shape LeafShape Here = branch_shape
shape_graft branch_shape (NodeShape l r) (Left path) = NodeShape (shape_graft branch_shape l path) r
shape_graft branch_shape (NodeShape l r) (Right path) = NodeShape l (shape_graft branch_shape r path)


tree_graft : (branch : Tree branch_shape a) -> (stalk : Tree stalk_shape a) -> (path : PathTo LeafShape stalk_shape) -> Tree (shape_graft branch_shape stalk_shape path) a
tree_graft branch Leaf Here = branch
tree_graft branch (Node left this right) (Left path) = Node (tree_graft branch left path) this right
tree_graft branch (Node left this right) (Right path) = Node left this (tree_graft branch right path)
