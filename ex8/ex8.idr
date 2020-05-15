import shapeless_tree
import shapely_tree


zipwith_shapeless_tree : (a -> b -> c) -> Tree a -> Tree b -> Tree c
zipwith_shapeless_tree f Leaf right = Leaf
zipwith_shapeless_tree f left Leaf = Leaf
zipwith_shapeless_tree f (Node left1 this1 right1) (Node left2 this2 right2) =
    Node (zipwith_shapeless_tree f left1 left2) (f this1 this2) (zipwith_shapeless_tree f right1 right2)

zipwith_shapely_tree : (a -> b -> c) -> Tree shape a -> Tree shape b -> Tree shape c
zipwith_shapely_tree f Leaf Leaf = Leaf
zipwith_shapely_tree f (Node left1 this1 right1) (Node left2 this2 right2) =
    Node (zipwith_shapely_tree f left1 left2) (f this1 this2) (zipwith_shapely_tree f right1 right2)

zip_tree : Tree shape a -> Tree shape b -> Tree shape (Pair a b)
zip_tree Leaf Leaf = Leaf
zip_tree (Node left1 this1 right1) (Node left2 this2 right2) =
    Node (zip_tree left1 left2) (this1, this2) (zip_tree right1 right2)

unzip_left : Tree shape (Pair a b) -> Tree shape a
unzip_left Leaf = Leaf
unzip_left (Node left (a, b) right) = Node (unzip_left left) a (unzip_left right)

unzip_right : Tree shape (Pair a b) -> Tree shape b
unzip_right Leaf = Leaf
unzip_right (Node left (a, b) right) = Node (unzip_right left) b (unzip_right right)

unzip_tree : Tree shape (Pair a b) -> Pair (Tree shape a) (Tree shape b)
unzip_tree tree = (unzip_left tree, unzip_right tree)

forget_shape : ShapelyTree.Tree shape type -> ShapelessTree.Tree type
forget_shape Leaf = Leaf
forget_shape (Node left this right) = Node (forget_shape left) this (forget_shape right)

compute_shape : (tree : ShapelessTree.Tree type) -> TreeShape
compute_shape Leaf = LeafShape
compute_shape (Node left this right) = NodeShape (compute_shape left) (compute_shape right)

learn_shape : (tree : ShapelessTree.Tree type) -> ShapelyTree.Tree (compute_shape tree) type
learn_shape Leaf = Leaf
learn_shape (Node left this right) = Node (learn_shape left) this (learn_shape right)

calculate_reflected_shape : TreeShape -> TreeShape
calculate_reflected_shape LeafShape = LeafShape
calculate_reflected_shape (NodeShape l r) = NodeShape (calculate_reflected_shape r) (calculate_reflected_shape l)

reflect_tree : Tree shape type -> Tree (calculate_reflected_shape shape) type
reflect_tree Leaf = Leaf
reflect_tree (Node left this right) = Node (reflect_tree right) this (reflect_tree left)

calculate_post_prune : TreeShape -> TreeShape -> TreeShape
calculate_post_prune LeafShape _ = LeafShape
calculate_post_prune _ LeafShape = LeafShape
calculate_post_prune (NodeShape l r) (NodeShape x y) = NodeShape (calculate_post_prune l x) (calculate_post_prune r y)

prune_tree : (template_shape : TreeShape) -> Tree tree_shape type -> Tree (calculate_post_prune template_shape tree_shape) type
prune_tree LeafShape _ = Leaf
prune_tree (NodeShape l r) Leaf = Leaf
prune_tree (NodeShape l r) (Node left this right) = Node (prune_tree l left) this (prune_tree r right)
