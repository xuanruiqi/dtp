||| This file implements a ``Tanaka-Garrigue''-style dependently-typed red-black tree
|||
||| The original implementation and reasoning was initially developed in Coq by 
||| K. Tanaka and J. Garrigue (and me) while trying to formalize dynamic bit vectors.
|||
||| I rewrote the dependently-typed development in Idris for a clearer 
||| presentation, as the original was largely unreadable and very complicated.

module RedBlack

import Data.Vect

%default total

-- Color and color functions
public export
data Color = Red | Black

ColorValid : Color -> Color -> Type
ColorValid Red Red = Void
ColorValid _ _ = ()

validAnyBlack : (c : Color) -> ColorValid c Black
validAnyBlack Red = ()
validAnyBlack Black = ()

incrBlack : Nat -> Color -> Nat
incrBlack d Red = d
incrBlack d Black = S d

inv : Color -> Color
inv Red = Black
inv Black = Red

-- Red-black tree as an indexed inductive family
-- Invariants: 
-- (1) no red node has a red child
-- (2) every path to a leaf has the same ``black-depth''
export
data Tree : Nat -> Color -> Type -> Type where
  Leaf : Tree 0 Black a
  Node : {d : Nat} -> {cl : Color} -> {cr : Color} -> (c : Color) -> 
         ColorValid c cl -> ColorValid c cr -> 
         Tree d cl a -> a -> Tree d cr a -> Tree (incrBlack d c) c a

export
empty : Tree 0 Black a
empty = Leaf

RNode : Tree d Black a -> a -> Tree d Black a -> Tree d Red a
RNode l v r = Node Red () () l v r

BNode : Tree d cl a -> a -> Tree d cr a -> Tree (incrBlack d Black) Black a
BNode l v r = Node Black () () l v r

export
member : Ord a => a -> Tree d c a -> Bool
member x Leaf = False
member x (Node _ _ _ l v r) with (compare x v)
  | LT = member x l
  | EQ = True
  | GT = member x r


size : Tree d c a -> Nat
size Leaf = 0
size (Node _ _ _ l v r) = S (size l + size r)

inOrderVec : (t : Tree d c a) -> Vect (size t) a
inOrderVec Leaf = Nil
inOrderVec (Node _ _ _ l v r) = rewrite plusSuccRightSucc (size l) (size r) 
                                in      inOrderVec l ++ (v :: (inOrderVec r))


-- We need an intermediate representation for a potentially malformed tree which may occur in insertion
data InsTree : Nat -> Color -> Type -> Type where
  Fix : {d : Nat} -> Tree d Black a -> a -> Tree d Black a -> a ->
        Tree d Black a -> InsTree d Red a
  T : {d : Nat} -> {c : Color} -> (pc : Color) -> Tree d c a -> InsTree d pc a


insTreeColor : InsTree d c a -> Color
insTreeColor (Fix _ _ _ _ _) = Red
insTreeColor (T _ _) = Black

fixColor : InsTree d c a -> Color
fixColor (Fix _ _ _ _ _) = Black
fixColor (T {c = c} _ _) = c

fixInsTree : (t : InsTree d c a) -> Tree (incrBlack d (inv (insTreeColor t))) (fixColor t) a
fixInsTree (Fix t1 a t2 b t3) = BNode (RNode t1 a t2) b t3
fixInsTree (T _ t) = t


balanceL : (c : Color) -> (l : InsTree d cl a) -> a -> (r : Tree d cr a) -> 
           ColorValid c (insTreeColor l) -> ColorValid c cr -> InsTree (incrBlack d c) c a
balanceL Black (Fix t1 a t2 b t3) c t4 _ _ = T Black (RNode (BNode t1 a t2) b (BNode t3 c t4))
balanceL Black (T _ l) v r _ _ = T Black (BNode l v r)
balanceL {cl = Black} {cr = Black} Red (T _ (Node {cl = Black} {cr = Black} Red _ _ t1 a t2)) b t3 _ _ = Fix t1 a t2 b t3
balanceL {cr = Red} Red (T _ (Node Red _ _ _ _ _)) _ _ _ _ impossible
balanceL {cl = Black} {cr = Black} Red (T {c = Black} _ l) v r _ _ = T Red (RNode l v r)
balanceL {cr = Red} Red (T _ _) _ _ _ _ impossible


balanceR : (c : Color) -> (l : Tree d cl a) -> a -> (r : InsTree d cr a) -> 
           ColorValid c cl -> ColorValid c (insTreeColor r) -> InsTree (incrBlack d c) c a
balanceR Black t1 a (Fix t2 b t3 c t4) _ _ = T Black (RNode (BNode t1 a t2) b (BNode t3 c t4))
balanceR Black l v (T _ r) _ _ = T Black (BNode l v r)
balanceR {cl = Black} {cr = Black} Red t1 a (T _ (Node {cl = Black} {cr = Black} Red _ _ t2 b t3)) _ _ = Fix t1 a t2 b t3
balanceR {cl = Red} Red _ _ (T _ (Node Red _ _ _ _ _)) _ _ impossible
balanceR {cl = Black} {cr = Black} Red l v (T {c = Black} _ r) _ _ = T Red (RNode l v r)
balanceR {cl = Red} Red _ _ (T _ _) _ _ impossible


ins : Ord a => a -> Tree d c a -> InsTree d c a
ins x Leaf = T Black (RNode Leaf x Leaf)
ins x (Node c validL validR l v r) with (compare x v) 
  | LT with (ins x l) proof insL
    ins x (Node Black _ validR l v r) | _ | Fix _ _ _ _ _ = balanceL Black (ins x l) v r () validR
    ins x (Node c _ validR l v r)     | _ | T _ _         = balanceL c (ins x l) v r leftValidPrf validR
      where leftValidPrf = rewrite (sym insL) in (validAnyBlack c)
  | EQ = T c (Node c validL validR l v r)
  | GT with (ins x r) proof insR 
    ins x (Node Black validL _ l v r) | _ | Fix _ _ _ _ _ = balanceR Black l v (ins x r) validL ()
    ins x (Node c validL _ l v r)     | _ | T _ _         = balanceR c l v (ins x r) validL rightValidPrf
      where rightValidPrf = rewrite (sym insR) in (validAnyBlack c)

export
insert : Ord a => a -> Tree d c a -> (d : Nat ** (c : Color ** Tree d c a))
insert x t = (_ ** (_ ** fixInsTree (ins x t)))
