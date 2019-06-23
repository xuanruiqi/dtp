module RedBlack

type color = 
  | Red 
  | Black

val incr_black : nat -> color -> nat
let incr_black d c = 
  match c with
  | Red -> d
  | Black -> d + 1

val color_valid : color -> color -> Tot bool
let color_valid c c' =
  match c, c' with
  | Red, Red -> false
  | _, _ -> true

val inv : color -> color
let inv c =
  match c with
  | Red -> Black
  | Black -> Red

type tree : nat -> color -> Type = 
  | Leaf : tree 0 Black
  | Node : #d:nat -> #cl:color -> #cr:color -> c:color{color_valid c cl /\ color_valid c cr} ->
           tree d cl -> int -> tree d cr -> tree (incr_black d c) c

val rnode : #d:nat -> tree d Black -> int -> tree d Black -> tree d Red
let rnode #d (l:tree d Black) v r = Node Red l v r

val bnode : #d:nat -> #cl: color -> #cr:color -> tree d cl -> int -> tree d cr -> tree (d+1) Black
let bnode #d #cl #cr (l:tree d cl) v (r:tree d cr) = Node Black l v r

type ins_tree : nat -> color -> Type = 
  | Fix : #d:nat -> tree d Black -> int -> tree d Black -> int -> tree d Black -> ins_tree d Red
  | T : #d:nat -> #c:color -> pc:color -> tree d c -> ins_tree d pc

val ins_tree_color : #d:nat -> #c:color -> ins_tree d c -> color
let ins_tree_color #d #c (t:ins_tree d c) = 
  match t with
  | Fix _ _ _ _ _ -> Red
  | T _ _ -> Black

val fix_color : #d:nat -> #c:color -> ins_tree d c -> color
let fix_color #d #c (t:ins_tree d c) = 
  match t with
  | Fix _ _ _ _ _ -> Black
  | T #_ #c _ _ -> c

val fix_ins_tree : #d:nat -> #c:color -> t:ins_tree d c -> (tree (incr_black d (inv (ins_tree_color t))) (fix_color t))
let fix_ins_tree #d #c (t:ins_tree d c) =
  match t with
  | Fix a x b y c -> bnode (rnode a x b) y c
  | T _ t -> t

val balance_l : #d:nat -> #cl:color -> #cr:color -> l:ins_tree d cl -> int -> tree d cr -> c:color{color_valid c (ins_tree_color l) /\ color_valid c cr} -> (ins_tree (incr_black d c) c)
let balance_l #d #cl #cr (l:ins_tree d cl) v r c = 
  match c with
  | Black ->
    (match l with 
     | Fix a x b y c -> T Black (rnode (bnode a x b) y (bnode c v r))
     | T _ l -> T Black (bnode l v r))
  | Red ->
    (match l with
     | T _ (Node Red a x b) -> Fix a x b v r
     | T _ l -> T Red (rnode l v r))

val balance_r : #d:nat -> #cl:color -> #cr:color -> tree d cl -> int -> r:ins_tree d cr -> c:color{color_valid c cl /\ color_valid c (ins_tree_color r)} -> (ins_tree (incr_black d c) c)
let balance_r #d #cl #cr l v (r:ins_tree d cr) c =
  match c with
  | Black ->
    (match r with
     | Fix a x b y c -> T Black (rnode (bnode l v a) x (bnode b y c))
     | T _ r -> T Black (bnode l v r))
  | Red ->
    (match r with
     | T _ (Node Red a x b) -> Fix l v a x b
     | T _ r -> T Red (rnode l v r))


val size : #d:nat -> #c:color -> t:tree d c -> Tot nat (decreases t)
let rec size #_ #_ t = 
  match t with
  | Leaf -> 1
  | Node _ l v r -> size l + size r + 1


val ins : #d:nat -> #c:color -> int -> t:tree d c -> Tot (ins_tree d c) (decreases (size t))
let rec ins #_ #_ x t =
  match t with
  | Leaf -> T Black (rnode Leaf x Leaf)
  | Node c l v r ->
    if x < v then 
      balance_l (ins x l) v r c
    else if x = v then
      T _ t
    else
      balance_r l v (ins x r) c

val blacken : #d:nat -> #c:color -> tree d c -> (tree (incr_black d (inv c)) Black)
let blacken #d #c (t:tree d c) = 
  match t with
  | Leaf -> Leaf
  | Node _ l v r -> bnode l v r

val insert : #d:nat -> int -> tree d Black -> (d':nat & tree d' Black)
let insert #d x t =
  match ins x t with
  | T #_ #c _ t' -> (| incr_black d (inv c), blacken t' |)




