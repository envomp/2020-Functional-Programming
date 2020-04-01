
import Data.String

---------------- Part One ----------------

data RoseTree : Type -> Type where
    Rose : a -> List (RoseTree a) -> RoseTree a


exampleTree : RoseTree String
exampleTree = Rose "6" [Rose "7" [Rose "4" [], Rose "3" [], Rose "8" [ Rose "9" [], Rose "10" []]]]


exampleIntTree : RoseTree Integer
exampleIntTree = Rose 6 [Rose 7 [Rose 4 [], Rose 3 [], Rose 8 [ Rose 9 [], Rose 10 []]]]


draw : RoseTree String -> List String
draw (Rose x ts') = lines x ++ drawSubTrees ts'
    where
        shift : String -> String -> List String -> List String
        shift first other more = zipWith (++) (first :: (replicate (length more) other)) more
        drawSubTrees : List (RoseTree String) -> List String
        drawSubTrees [] = []
        drawSubTrees [t] = "|" :: shift "'- " "   " (draw t)
        drawSubTrees (t :: ts) = "|" :: shift "+- " "|  " (draw t) ++ drawSubTrees ts


Show a => Show (RoseTree a) where
    show t = unlines (draw (stringify t))
        where
            stringify : RoseTree a -> RoseTree String
            stringify (Rose x xs) = Rose (show x) (map stringify xs)


foldRoseTree : (a -> List b -> b) -> List b -> RoseTree a -> b
foldRoseTree f e (Rose x xs) = f x (foldRoseList f e xs)
    where
        foldRoseList : (a -> List b -> b) -> List b -> List (RoseTree a) -> List b
        foldRoseList f e [] = e
        foldRoseList f e (x :: xs) = (foldRoseTree f e x) :: (foldRoseList f e xs)


mapRoseTree : (a -> b) -> RoseTree a -> RoseTree b
mapRoseTree f a = (foldRoseTree (\val, children => Rose (f val) children) [] a)

--  mapRoseTree (\x => show x) exampleIntTree -- Rose "6" [Rose "7" [Rose "4" [], Rose "3" [], Rose "8" [Rose "9" [], Rose "10" []]]] : RoseTree String

flattenRose : RoseTree a -> List a
flattenRose a = foldRoseTree (\val, children => [val] ++ concat children) [] a

--  flattenRose exampleTree -- ["6", "7", "4", "3", "8", "9", "10"] : List String

reverseRose : RoseTree a -> RoseTree a
reverseRose a = foldRoseTree (\val, children => Rose val (reverse children)) [] a

--  reverseRose exampleTree -- Rose "6" [Rose "7" [Rose "8" [Rose "10" [], Rose "9" []], Rose "3" [], Rose "4" []]] : RoseTree String

sumRose : RoseTree Nat -> Nat
sumRose a = sum (flattenRose a)

--  sumRose (mapRoseTree (\x => fromIntegerNat x) exampleIntTree) -- 47 : Nat

maxList : Nat -> List Nat -> Nat
maxList y (x :: []) = max y x
maxList y (x :: xs) = max (max y x) (maxList y xs)


maxRose : RoseTree Nat -> Nat
maxRose a = maxList Z (flattenRose a)

--  maxRose (mapRoseTree (\x => fromIntegerNat x) exampleIntTree) -- 10 : Nat

---------------- Part Two ----------------

data Tree : Type -> Type where
    Leaf : Tree a
    Node : Tree a -> a -> Tree a -> Tree a


KVStore : Type -> Type
KVStore a = Tree (Nat, a)


foldTree : b -> (b -> a -> b -> b) -> Tree a -> b
foldTree l n Leaf = l
foldTree l n (Node tl x tr) = n (foldTree l n tl) x (foldTree l n tr)


insertNode : KVStore a -> KVStore a -> KVStore a
insertNode node Leaf = node
insertNode Leaf node = node
insertNode (Node l_ (k, v_) r_) (Node left (rk, rv) right) =
     if (k < rk)
        then Node (insertNode (Node l_ (k, v_) r_) left) (rk, rv) right
        else if (k > rk)
             then Node left (rk, rv) (insertNode (Node l_ (k, v_) r_) right)
             else (Node left (rk, rv) right) -- no duplicates

insert : (Nat, a) -> KVStore a -> KVStore a
insert (k, v) Leaf = Node Leaf (k, v) Leaf
insert (k, v) (Node left (rk, rv) right) =
    if (k < rk)
        then Node (insert (k, v) left) (rk, rv) right
        else if (k > rk)
             then Node left (rk, rv) (insert (k, v) right)
             else (Node left (rk, rv) right) -- no duplicates


treeToRoseTree : Tree (Nat, String) -> Maybe (RoseTree String)
treeToRoseTree Leaf = Nothing
treeToRoseTree (Node left (k, v) right) = Just (Rose (show k ++ " => " ++ v) ((new left) ++ (new right)))
    where
        new : Tree (Nat, String) -> List (RoseTree String)
        new side = case treeToRoseTree side of
                        Nothing => []
                        Just x => [x]


drawStore : KVStore String -> IO ()
drawStore tree = case treeToRoseTree tree of
                      Nothing => putStr "."
                      Just x => putStr (show x)


exampleStore : KVStore String
exampleStore = insert (7, "apple") $
               insert (6 , "papaya") $
               insert (4 , "mango") $
   	           insert (3 , "orange") $
 		       insert (7 , "cabbage") $
               insert (10 , "pineapple") $
               insert (5 , "banana") Leaf

--  :exec drawStore exampleStore
--  "5 => banana"
--  |
--  +- "3 => orange"
--  |  |
--  |  '- "4 => mango"
--  |
--  '- "10 => pineapple"
--     |
--     '- "7 => cabbage"
--        |
--        '- "6 => papaya"

delete : Nat -> KVStore String -> KVStore String
delete key Leaf = Leaf
delete key (Node left (rk, rv) right) = if (key == rk)
                                           then  insertNode left right
                                           else  if (key < rk)
                                                 then Node (delete key left) (rk, rv) right
                                                 else Node left (rk, rv) (delete key right)

--   :exec drawStore (delete 5 exampleStore)
--  "10 => pineapple"
--  |
--  '- "7 => cabbage"
--     |
--     '- "6 => papaya"
--        |
--        '- "3 => orange"
--           |
--           '- "4 => mango"


data BoardState : Type where
  Delete : BoardState
  Insert : BoardState
  Repeat : BoardState
  Finish : BoardState

validator : List String -> BoardState
validator [] = Repeat
validator ("done" :: []) = Finish
validator (x :: []) = Repeat
validator ("." :: (y :: [])) = case parsePositive y of
                                    Nothing => Repeat
                                    Just x => Delete
validator (x :: (y :: [])) = case parsePositive x of
                                    Nothing => Repeat
                                    Just x => Insert
validator (x :: (y :: xs)) = Repeat


-- actAccordingly : BoardState -> List String -> KVStore String -> IO (KVStore String)
-- actAccordingly Repeat x tree = edit tree
-- actAccordingly Finish x tree = tree
-- actAccordingly Delete x tree = tree

-- kys : RoseTree String -> IO (RoseTree String)
-- kys tree = pure tree

deleteNode' : List String -> KVStore String -> KVStore String
deleteNode' ("." :: [k]) tree = case parsePositive k of
                                    Nothing => tree
                                    Just key => delete (cast key) tree


insertNode' : List String -> KVStore String -> KVStore String
insertNode' (k :: [val]) tree = case parsePositive k of
                                    Nothing => tree
                                    Just key => insert ((cast key), val) tree

edit : KVStore String -> IO ()
edit tree = do putStr "The current state is:\n"
               drawStore tree
               putStr "\nPlease enter a command: "
               command <- getLine
               case validator (words command) of
                    Repeat => edit tree
                    Finish => putStr "\n"
                    Delete => edit (deleteNode' (words command) tree)
                    Insert => edit (insertNode' (words command) tree)
