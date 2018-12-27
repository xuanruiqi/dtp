module Set

import RedBlack

export
data Set : Type -> Type where
  MkSet : {d : Nat} -> {c : RedBlack.Color} -> (a : Type) -> 
          Tree d c a -> Set a

export
empty : Ord a => Set a
empty = MkSet _ RedBlack.empty

export
member : Ord a => a -> Set a -> Bool
member x (MkSet _ t) = RedBlack.member x t

export
add : Ord a => a -> Set a -> Set a
add x (MkSet _ t) = MkSet _ (snd (snd (RedBlack.insert x t)))

export
fromList : Ord a => List a -> Set a
fromList = foldr add empty
