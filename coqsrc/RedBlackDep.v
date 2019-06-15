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
  | Node : forall d cl cr c,
      color_valid c cl -> color_valid c cr ->
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
  Derive Signature for ins_tree.
  
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
    blacken (Node Black _ _ l v r) := BNode l v r;
    blacken (Node Red _ _ l v r) := BNode l v r.

  Equations insert {d} (x : t) (tr : tree d Black) : {d' : nat & tree d' Black} :=
    insert x tr with (ins x tr) := {
      | T _ t' => existT _ _ (blacken t')
    }.

  Inductive tree_ml :=
  | LeafML : tree_ml
  | NodeML : color -> tree_ml -> t -> tree_ml -> tree_ml.

  Fixpoint from_dep {d c} (t : tree d c) :=
    match t with
    | Leaf => LeafML
    | Node c _ _ l v r => NodeML c (from_dep l) v (from_dep r)
    end.
  
  Definition insert_ml {d} (x : t) (tr : tree d Black) : tree_ml :=
    match insert x tr with
    | existT _ _ res => from_dep res
    end.

  Inductive del_tree : nat -> color -> Type :=
  | Stay : forall {d c} pc, color_valid c (inv pc) -> tree d c -> del_tree d pc
  | Down : forall {d}, tree d Black -> del_tree (S d) Black.
  Derive Signature for del_tree.
  
  Fail Equations balright {d cl cr} c
    (l : tree d cl) (v : t) (r : del_tree d cr) 
    (valid_l : color_valid c cl)
    (valid_r : color_valid c cr) :
    del_tree (incr_black d c) c :=
    balright (cl := Black) Red l v (@Stay _ Black _ _ r) _ _ := Stay Red _ (RNode l v r);
    balright (cl := Black) Red l v (@Stay _ Red Red _ _) _ !;
    balright (cl := Black) Red (@Node _ _ Black ?(Black) _ _ t1 x t2) y (Down t3) _ _ :=
      Stay Red _ (BNode t1 x (RNode t2 y t3));
    balright (cl := Black) Red (@Node _ _ Red ?(Black) _ _ t1 x (Node _ _ _ t2 y t3))
      z (Down t4) _ _ :=
      Stay Red _ (RNode (BNode t1 x t2) y (BNode t3 z t4));
    balright Black l v (Stay _ _ r) _ _ := Stay Black _ (BNode l v r);
    balright Black (@Node _ _ Red Black _ _ t1 x (Node _ _ _ t2 y t3)) z (Down t4) _ _ :=
      Stay Black _ (BNode t1 x (BNode t2 y (BNode t3 z t4)));
    balright Black (@Node _ Black Black Red _ _ t1 x (@Node _ _ Black _ _ _ t2 y t3))
      z (Down t4) _ _ :=
      Stay Black _ (BNode t1 x (BNode t2 y (RNode t3 z t4)));
    balright Black (@Node _ Black Black Red _ _ t1 x (@Node _ _ Red _ _ _ t2 y 
                    (@Node _ Black Black _ _ _ t3 z t4))) w (Down t5) _ _ :=
      Stay Black _ (BNode t1 x (RNode (BNode t2 y t3) z (BNode t4 w t5)));
    balright Black (@Node _ _ Black Black _ _ t1 x t2) y (Down t3) _ _ :=
      Down (BNode t1 x (RNode t2 y t3)).

End Tree.

Extraction Tree.
