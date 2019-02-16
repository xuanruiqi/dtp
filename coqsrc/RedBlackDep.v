Require Import Structures.Orders Nat.
Require Import CpdtTactics.
From Equations Require Import Equations.

Set Implicit Arguments.

Module Tree (X : OrderedTypeFull').

  Include X.
    
  Inductive color := Red | Black.
  Derive NoConfusion for color.
  
  Definition color_valid c1 c2 :=
    match c1, c2 with
    | Red, Red => False
    | _, _ => True
    end.
  
  Lemma valid_any_black c : color_valid c Black.
  Proof. case c; crush. Qed.
  
  Definition incr_black d c :=
    match c with
    | Red => d
    | Black => S d
    end.

  Definition inv c :=
    match c with
    | Red => Black
    | Black => Red
    end.
  
  Inductive tree : nat -> color -> Type :=
  | Leaf : tree 0 Black
  | Node : forall d cl cr c, color_valid c cl -> color_valid c cr ->
                        tree d cl -> t -> tree d cr -> tree (incr_black d c) c.
  
  Equations RNode {d} (l : tree d Black) (v : t) (r : tree d Black) :
    tree d Red :=
    RNode l v r := Node Red _ _ l v r.

  
  Equations BNode {d cl cr} (l : tree d cl) (v : t) (r : tree d cr) :
    tree (S d) Black :=
    BNode l v r := Node Black _ _ l v r.
  
  
  Inductive ins_tree : nat -> color -> Type :=
  | T : forall d c pc, tree d c -> ins_tree d pc
  | Fix : forall d,
      tree d Black -> t -> tree d Black -> t -> tree d Black -> ins_tree d Red.
  
  
  Definition ins_tree_color {d c} (t : ins_tree d c) :=
    match t with
    | Fix _ _ _ _ _ => Red
    | T _ _ => Black
    end.

  Definition fix_color {d c} (t : ins_tree d c) :=
    match t with
    | Fix _ _ _ _ _ => Black
    | @T _ c _ _ => c
    end.

  Definition fix_ins_tree {d c} (t : ins_tree d c) :
    tree (incr_black d (inv (ins_tree_color t))) (fix_color t) :=
    match t with
    | Fix t1 a t2 b t3 => BNode (RNode t1 a t2) b t3
    | T _ t => t
    end.
  
  Equations balanceL {d cl cr} (c : color) (l : ins_tree d cl)
    (v : t) (r : tree d cr)
    (valid_l : color_valid c (ins_tree_color l))
    (valid_r : color_valid c cr) :
    ins_tree (incr_black d c) c :=
    balanceL Black l v r _ _ with l => {
      | Fix t1 a t2 b t3 := T Black (RNode (BNode t1 a t2) b (BNode t3 v r));
      | T _ l' := T Black (BNode l' v r)
    };
    balanceL (cr := Black) Red l v r _ _ with l => {
      | T _ l' with l' => {
        | Node (cl := Black) (cr := Black)  Red _ _ t1 a t2 :=
          Fix t1 a t2 v r;
        | Leaf := T Red (RNode l' v r);
        | Node Black _ _ _ _ _  := T Red (RNode l' v r)
        }
    }.

  Equations balanceR {d cl cr} (c : color) (l : tree d cl)
    (v : t) (r : ins_tree d cr)
    (valid_l : color_valid c cl)
    (valid_r : color_valid c cr) :
    ins_tree (incr_black d c) c :=
    balanceR Black l v r _ _ with r => {
      | Fix t1 a t2 b t3 := T Black (RNode (BNode l v t1) a (BNode t2 b t3));
      | T _ r' := T Black (BNode l v r')
    };
    balanceR (cl := Black) Red l v r _ _ with r => {
      | T _ r' with r' => {
        | Node (cl := Black) (cr := Black)  Red _ _ t1 a t2 :=
          Fix l v t1 a t2;
        | Leaf := T Red (RNode l v r');
        | Node Black _ _ _ _ _  := T Red (RNode l v r')
        }
    }.

  
  Equations? ins {d c} (v : t) (tr : tree d c) : ins_tree d c :=
    ins x Leaf := T Black (RNode Leaf x Leaf);
    ins x (Node c _ _ l v r) with (compare x v) => {
      | Lt := balanceL c (ins x l) v r _ _;
      | Eq := T c (Node c _ _ l v r);
      | Gt := balanceR c l v (ins x r) _ _
    }.
  
  Proof.
    cbv. destruct c; destruct (ins tr tr0 x l); crush.
  Qed.

  Equations blacken {d c} (tr : tree d c) : tree (incr_black d (inv c)) Black :=
    blacken Leaf := Leaf;
    blacken (Node c _ _ l v r) with c => {
      | Black := BNode l v r;
      | Red := BNode l v r
    }.

  Notation "{< x >}" := (sigmaI _ _ x).
  Import Sigma_Notations.

  Equations insert {d} (x : t) (tr : tree d Black) : &{d' : nat & tree d' Black} :=
    insert x tr with (ins x tr) := {
      | T _ t' => {<blacken t'>}
    }.
  
End Tree.