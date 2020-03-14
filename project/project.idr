------------------------------------------------
-- Functional Programming Assignment Skeleton --
------------------------------------------------

import Data.String -- we need this!

-----------------------------------------------
-- Part One: Representaiton, valid, get, set --
-----------------------------------------------

||| Current state of game
data Game_state : Type where
  Black_wins : Game_state
  White_wins : Game_state
  Draw : Game_state
  Continues : Game_state

||| The game has two players, one who plays with the white pieces, the other the black pieces. We refer to the players by the colour of their pieces.
data Player : Type where
  White : Player
  Black : Player

||| Possible contents of a space on the board. Each space contains either Nothing, a White piece, or a Black piece.
Space : Type
Space = Maybe Player

||| Your representation of the board. The is going to involve Spaces.
Board : Type
Board = List (List Space)

||| Board positions, according to the indexing scheme detailed in the provided section, with the code that draws the board. (Possibly also with the assignment?).
Position : Type
Position = (Nat, Nat)

||| Functions to generate boards and rows
create_row : Nat -> List Space
create_row Z = []
create_row (S n) = Nothing :: (create_row n)

create_board : Nat -> Board
create_board Z = []
create_board (S n) = (create_row 9) :: (create_board n)

||| A function that determines whether or not a given pair of Nats actually indexes a position on the game board, according to our coordinate scheme.
valid : Position -> Bool
valid (x, y) = if (
                    y == 0 && 4 <= x && x <= 8
                  ||
                    y == 1 && 3 <= x && x <= 8
                  ||
                    y == 2 && 2 <= x && x <= 8
                  ||
                    y == 3 && 1 <= x && x <= 8
                  ||
                    y == 4 && 0 <= x && x <= 8
                  ||
                    y == 5 && 0 <= x && x <= 7
                  ||
                    y == 6 && 0 <= x && x <= 6
                  ||
                    y == 7 && 0 <= x && x <= 5
                  ||
                    y == 8 && 0 <= x && x <= 4
                  )
                  then True
                  else False

||| Get the contents of the given position, on the given board. Note that this only makes sense if the position is valid.
row_index : Nat -> List Space -> Space
row_index n [] = Nothing
row_index Z (elem :: row) = elem
row_index (S n) (elem :: row) = row_index n row

board_index : Nat -> Board -> List Space
board_index n [] = []
board_index Z (pos :: board) = pos
board_index (S n) (pos :: board) = board_index n board

get_from_board : Board -> Position -> Space
get_from_board board (x, y) = if (valid (x, y))
                      then row_index x (board_index y board)
                      else Nothing

||| Given a valid position, a board, and the thing we want to occupy that position (a Space), returns the result of putting that thing in the appropriate position (which is a board).
insert_row : Nat -> List Space -> Space -> List Space
insert_row Z (p :: board) new = new :: board
insert_row (S n) (p :: board) new = p :: insert_row n board new

insert_board : Position -> Board -> Space -> Board
insert_board (x, Z) (row :: board) space = (insert_row x row space) :: board
insert_board (x, (S y)) (row :: board) space = row :: insert_board (x, y) board space

set_on_board : Board -> Position -> Space -> Board
set_on_board board (x, y) space = insert_board (x, y) board space

--------------------------------------------
-- Part Two: winning_move and losing_move --
--------------------------------------------

check_3_xs : List Space -> Player -> Nat -> Bool
check_3_xs xs _ (S (S (S Z))) = True
check_3_xs [] _ n = False
check_3_xs (Nothing :: rest) player n = check_3_xs rest player Z
check_3_xs ((Just White) :: rest) White n = check_3_xs rest White (S n)
check_3_xs ((Just White) :: rest) Black n = check_3_xs rest Black Z
check_3_xs ((Just Black) :: rest) Black n = check_3_xs rest Black (S n)
check_3_xs ((Just Black) :: rest) White n = check_3_xs rest White Z

check_3_ys : Board -> Player -> Bool
check_3_ys [] _ = False
check_3_ys (row :: rest) player = if (check_3_xs row player Z)
                                then True
                                else check_3_ys rest player

check_4_xs : List Space -> Player -> Nat -> Bool
check_4_xs _ _ (S (S (S (S Z)))) = True
check_4_xs [] _ n = False
check_4_xs (Nothing :: rest) player n = check_4_xs rest player Z
check_4_xs ((Just White) :: rest) White n = check_4_xs rest White (S n)
check_4_xs ((Just White) :: rest) Black n = check_4_xs rest Black Z
check_4_xs ((Just Black) :: rest) Black n = check_4_xs rest Black (S n)
check_4_xs ((Just Black) :: rest) White n = check_4_xs rest White Z

check_4_ys : Board -> Player -> Bool
check_4_ys [] _ = False
check_4_ys (row :: rest) player = if (check_4_xs row player Z)
                                then True
                                else check_4_ys rest player

||| Transpose matrix
transpose_list : List Space -> Board
transpose_list [] = []
transpose_list (x :: xs) = [x] :: transpose_list xs

transpose_matrix : Board -> Board
transpose_matrix [] = replicate 9 []
transpose_matrix (x :: xs) = zipWith (++) (transpose_list x) (transpose_matrix xs)

||| If a player plays one of their pieces at the given position on the given board, do they win the game? Note that the position supplied must be valid for this to make sense.
winning_move : Position -> Player -> Board -> Bool
winning_move (x, y) player board = (check_4_ys board player) || (check_4_ys (transpose_matrix board) player)

||| If a player plays one of their pieces at the given position on the given board, do they lose the game? Note that the position supplied must be valid for this to make sense.
losing_move : Position -> Player -> Board -> Bool
losing_move (x, y) player board = (check_3_ys board player) || (check_3_ys (transpose_matrix board) player)

-----------------------
-- Drawing The Board --
-----------------------

-- The draw_ functions are provided to help you with your assignment. In particular, once
-- you have implemented `valid : Position -> Bool` and `get_from_board : Board -> Position -> Space`,
-- you can draw `b : Board` by executing `draw_board valid get_from_board b`. For example, if b is
-- the empty board, this results in:

-- 0:      - - - - -
-- 1:     - - - - - -
-- 2:    - - - - - - -
-- 3:   - - - - - - - -
-- 4:  - - - - - - - - -
-- 5:   - - - - - - - -
-- 6:    - - - - - - -   \
-- 7:     - - - - - -   \ \
-- 8:      - - - - -   \ \ \
--                    \ \ \ \
--           \ \ \ \ \ \ \ \ \
--           :0:1:2:3:4:5:6:7:8


||| (draw_spaces n) is the string composed of n spaces.
draw_spaces : Nat -> String
draw_spaces n = pack (replicate n ' ')

||| (draw_guides n) is the string containing n copies of " \\".
draw_guides : Nat -> String
draw_guides n = concat (replicate n " \\")

||| draw_nothing is the empty string. The exists for the sake of consistent form.
draw_nothing : String
draw_nothing = ""

||| (draw_player p) is the single-character string reprsenting player p on the board.
draw_player : Player -> String
draw_player White = "w"
draw_player Black = "b"

||| (draw_space s) is the single-character string representing space s on the board.
draw_space : Space -> String
draw_space Nothing = "-"
draw_space (Just x) = draw_player x

||| (draw_row xs) draws the spaces in the given row, with spaces in between.
draw_row : List Space -> String
draw_row = concat . (intersperse " ") . (map draw_space)

||| Once you have implemented get_from_board and valid (see part one), (draw_board get_from_board valid b) displays board b as specified at the beginning of this section.
draw_board : (get_from_board : Board -> Position -> Space) -> (valid : Position -> Bool) -> Board -> IO ()
draw_board get_from_board valid b =
  (putStr . unlines)
  ((zipWith3 (\x, y => (++) (x ++ y))
             left_things row_strings right_things)
    ++ bottom_things)
  where
  valid_positions : List (List Position)
  valid_positions = map (filter valid)
                      (map (\i => zip (replicate 9 i) [0..8]) [0..8])

  row_strings : List String
  row_strings = map (draw_row . map (get_from_board b)) valid_positions

  left_things : List String
  left_things = [ "0:" ++ draw_spaces 6
                , "1:" ++ draw_spaces 5
                , "2:" ++ draw_spaces 4
                , "3:" ++ draw_spaces 3
                , "4:" ++ draw_spaces 2
                , "5:" ++ draw_spaces 3
                , "6:" ++ draw_spaces 4
                , "7:" ++ draw_spaces 5
                , "8:" ++ draw_spaces 6 ]

  right_things : List String
  right_things = [ draw_nothing
                 , draw_nothing
                 , draw_nothing
                 , draw_nothing
                 , draw_nothing
                 , draw_nothing
                 , draw_spaces 2 ++ draw_guides 1
                 , draw_spaces 2 ++ draw_guides 2
                 , draw_spaces 2 ++ draw_guides 3 ]

  bottom_things : List String
  bottom_things = [ draw_spaces 18 ++ draw_guides 4
                  , draw_spaces 9  ++ draw_guides 9
                  , draw_spaces 10 ++ ":0:1:2:3:4:5:6:7:8"
                  ]

---------------------------------
-- Part 3: An Interactive Game --
---------------------------------

||| Finally, implement a playable game of four-not-three using what you have built so far.

maybe_tuple : Maybe Nat -> Maybe Nat -> Board -> Maybe (Nat, Nat)
maybe_tuple Nothing Nothing _ = Nothing
maybe_tuple Nothing (Just x) _ = Nothing
maybe_tuple (Just x) Nothing _ = Nothing
maybe_tuple (Just x) (Just y) board = if (valid (x, y))
                                      then Just (x, y)
                                      else Nothing

validate_input : List (Maybe Nat) -> Board -> Maybe (Nat, Nat)
validate_input [] _ = Nothing
validate_input (x :: []) _ = Nothing
validate_input (x :: y :: []) board = maybe_tuple x y board
validate_input (x :: y :: z :: m) _ = Nothing

mapper : String -> Board -> Maybe (Nat, Nat)
mapper str board = validate_input (map (\a => parsePositive a) (words str)) board

check_state : Board -> Position -> Game_state
check_state board position = if (winning_move position White board) || (losing_move position Black board)
                                   then White_wins
                                   else if (losing_move position White board) || (winning_move position Black board)
                                      then Black_wins
                                      else Continues

game_loop : Bool -> Board -> Game_state -> IO ()
game_loop _ board Draw = do draw_board get_from_board valid board
                            putStrLn "It's a Draw!"

game_loop _ board White_wins = do draw_board get_from_board valid board
                                  putStrLn "White player wins!"

game_loop _ board Black_wins = do draw_board get_from_board valid board
                                  putStrLn "Black player wins!"

game_loop True board Continues = do draw_board get_from_board valid board
                                    putStrLn "Player B ?:"
                                    io_move <- getLine
                                    case mapper io_move board of
                                         Just (x, y) => do putStrLn ("your move was x=" ++ show x ++ " y=" ++ show y)
                                                           case get_from_board board (x, y) of
                                                                Nothing => game_loop False (set_on_board board (x, y) (Just Black)) (check_state (set_on_board board (x, y) (Just Black)) (x, y))
                                                                Just x => do putStrLn "And it was occupied!"
                                                                             game_loop True board Continues
                                         Nothing => do putStrLn "Please select valid coordinates as follows 'x y'."
                                                       game_loop True board Continues

game_loop False board Continues = do draw_board get_from_board valid board
                                     putStrLn "Player W ?:"
                                     io_move <- getLine
                                     case mapper io_move board of
                                          Just (x, y) => do putStrLn ("your move was x=" ++ show x ++ " y=" ++ show y)
                                                            case get_from_board board (x, y) of
                                                                 Nothing => game_loop True (set_on_board board (x, y) (Just White)) (check_state (set_on_board board (x, y) (Just White)) (x, y))
                                                                 Just x => do putStrLn "And it was occupied!"
                                                                              game_loop False board Continues
                                          Nothing => do putStrLn "Please select valid coordinates as follows 'x y'."
                                                        game_loop False board Continues

new_game : IO ()
new_game = game_loop True (create_board 9) Continues


-- Once you have implemented new_game, you can compile this file with "idris <file_name> -o game" to obtain an executable!
main : IO ()
main = new_game
