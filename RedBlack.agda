-- Copyright 2019, Xuanrui Qi
-- Original algorithm by: Jacques Garrigue, Xuanrui Qi & Kazunari Tanaka
open import Data.Nat hiding (compare)
open import Data.Nat.Properties
open import Relation.Binary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; sym; inspect; [_])
open Eq.≡-Reasoning
open import Data.Product
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

module RedBlack
  {c r} {A : Set c} {_<_ : Rel A r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

  open IsStrictTotalOrder isStrictTotalOrder

  data Color : Set where
    Red : Color
    Black : Color

  incr-Black : ℕ → Color → ℕ
  incr-Black d Black = suc d
  incr-Black d Red   = d

  color-valid : Color → Color → Set
  color-valid Red Red = ⊥
  color-valid _ _ = ⊤

  inv : Color → Color
  inv Red = Black
  inv Black = Red

  valid-*-Black : ∀ c → color-valid c Black
  valid-*-Black Red = tt
  valid-*-Black Black = tt

  data Tree : ℕ → Color → Set c where
    Leaf : Tree 0 Black
    Node : ∀ {d cₗ cᵣ} c → color-valid c cₗ → color-valid c cᵣ →
           Tree d cₗ → A → Tree d cᵣ → Tree (incr-Black d c) c

  RNode : ∀ {d} → Tree d Black → A → Tree d Black → Tree d Red
  RNode = Node Red tt tt

  BNode : ∀ {d cₗ cᵣ} → Tree d cₗ → A → Tree d cᵣ → Tree (suc d) Black
  BNode = Node Black tt tt

  -- Insertion algorithm
  data InsTree : ℕ → Color → Set c where
    Fix : ∀ {d} → Tree d Black → A → Tree d Black → A → Tree d Black → InsTree d Red
    T : ∀ {d c} cₚ → Tree d c → InsTree d cₚ

  InsTree-color : ∀ {d c} → InsTree d c → Color
  InsTree-color (Fix _ _ _ _ _) = Red
  InsTree-color (T _ _) = Black

  fix-color : ∀ {d c} → InsTree d c → Color
  fix-color (Fix _ _ _ _ _) = Black
  fix-color (T {c = c} _ _) = c

  fix-InsTree : ∀ {d c} → (t : InsTree d c) → Tree (incr-Black d (inv (InsTree-color t))) (fix-color t)
  fix-InsTree (Fix t₁ x t₂ y t₃) = BNode (RNode t₁ x t₂) y t₃
  fix-InsTree (T _ t) = t

  balanceₗ : ∀ {d cₗ cᵣ} c → (l : InsTree d cₗ) → A → Tree d cᵣ → color-valid c (InsTree-color l) → color-valid c cᵣ → InsTree (incr-Black d c) c  
  balanceₗ Black (Fix t₁ x t₂ y t₃) z t₄ _ _ = T Black (RNode (BNode t₁ x t₂) y (BNode t₃ z t₄))
  balanceₗ Black (T _ l) v r _ _ = T Black (BNode l v r)
  balanceₗ {cᵣ = Black} Red (T _ (Node {cₗ = Black} {cᵣ = Black} Red _ _ t₁ x t₂)) y t₃ _ _ = Fix t₁ x t₂ y t₃
  balanceₗ {cᵣ = Black} Red (T {c = Black} _ l) v r _ _ = T Red (RNode l v r)
  

  balanceᵣ : ∀ {d cₗ cᵣ} c → Tree d cₗ → A → (r : InsTree d cᵣ) → color-valid c cₗ → color-valid c (InsTree-color r) → InsTree (incr-Black d c) c
  balanceᵣ Black t₁ x (Fix t₂ y t₃ z t₄) _ _ = T Black (RNode (BNode t₁ x t₂) y (BNode t₃ z t₄))
  balanceᵣ Black l v (T _ r) _ _ = T Black (BNode l v r)
  balanceᵣ {cₗ = Black} Red t₁ x (T _ (Node {cₗ = Black} {cᵣ = Black} Red _ _ t₂ y t₃)) _ _ = Fix t₁ x t₂ y t₃
  balanceᵣ {cₗ = Black} Red l v (T {c = Black} _ r) _ _ = T Red (RNode l v r)

  ins : ∀ {d c} → A → Tree d c → InsTree d c
  ins x Leaf = T Black (RNode Leaf x Leaf)
  ins x (Node c _ _ l v r) with (compare x v)
  ins x (Node c _ _ l v r)    | tri< x<v _ _ with ins x l | inspect (ins x) l
  ins x (Node Black _ validᵣ l v r) | _ | Fix _ _ _ _ _   | [ insₗ ] = balanceₗ Black (ins x l) v r tt tt
  ins x (Node c     _ validᵣ l v r) | _ | T _ _           | [ insₗ ] = balanceₗ c (ins x l) v r validₗ validᵣ
    where
      validₗ = subst (λ t → color-valid c (InsTree-color t)) (sym insₗ) (valid-*-Black c)
  ins x t@(Node c _ _ l v r)  | tri≈ _ x≡v _ = T _ t
  ins x (Node c _ _ l v r)    | tri> _ _ x>v with ins x r | inspect (ins x) r
  ins x (Node Black validₗ _ l v r) | _ | Fix _ _ _ _ _   | [ insᵣ ] = balanceᵣ Black l v (ins x r) tt tt
  ins x (Node c     validₗ _ l v r) | _ | T _ _           | [ insᵣ ] = balanceᵣ c l v (ins x r) validₗ validᵣ
    where
      validᵣ = subst (λ t → color-valid c (InsTree-color t)) (sym insᵣ) (valid-*-Black c) 

  blacken : ∀ {d c} → Tree d c → Tree (incr-Black d (inv c)) Black
  blacken Leaf = Leaf
  blacken (Node Black _ _ l v r) = BNode l v r
  blacken (Node Red _ _ l v r) = BNode l v r

  insert : ∀ {d} → A → Tree d Black → ∃ (λ d' → Tree d' Black)
  insert {d = d} x t with ins x t
  ... | T {c = c} _ t' = (incr-Black d (inv c) , blacken t')

  -- Deletion algorithm
  data DelTree : ℕ → Color → Set c where
    Stay : ∀ {d c} cₚ → color-valid c (inv cₚ) → Tree d c → DelTree d cₚ
    Down : ∀ {d} → Tree d Black → DelTree (suc d) Black

  bal-right : ∀ {d cₗ cᵣ} c → Tree d cₗ → A → DelTree d cᵣ → color-valid c cₗ → color-valid c cᵣ → DelTree (incr-Black d c) c
  bal-right {cₗ = Black} Red l v (Stay {c = Black} _ _ r) _ _ = Stay Red tt (RNode l v r)
  bal-right {cₗ = Black} Red l v (Stay {c = Red} Red _ _) _ ()
  bal-right Red (Node {cᵣ = Black} Black _ _ t₁ x t₂) y (Down t₃) _ _ = Stay Red tt (BNode t₁ x (RNode t₂ y t₃))
  bal-right Red (Node {cᵣ = Red} Black _ _ t₁ x (Node _ _ _ t₂ y t₃)) z (Down t₄) _ _ = Stay Red tt (RNode (BNode t₁ x t₂) y (BNode t₃ z t₄))
  bal-right Black l v (Stay _ _ r) _ _ = Stay Black tt (BNode l v r)
  bal-right Black (Node {cᵣ = Red} Black _ _ t₁ x (Node _ _ _ t₂ y t₃)) z (Down t₄) _ _ = Stay Black tt (BNode (BNode t₁ x t₂) y (BNode t₃ z t₄))
  bal-right Black (Node {cₗ = Black} {cᵣ = Black} Red _ _ t₁ x (Node {cᵣ = Black} _ _ _ t₂ y t₃)) z (Down t₄) _ _ =
    Stay Black tt (BNode t₁ x (BNode t₂ y (RNode t₃ z t₄)))
  bal-right Black (Node {cₗ = Black} {cᵣ = Black} Red _ _ t₁ x (Node {cᵣ = Red} _ _ _ t₂ y (Node {cₗ = Black} {cᵣ = Black} _ _ _ t₃ z t₄))) w (Down t₅) _ _ =
    Stay Black tt (BNode t₁ x (RNode (BNode t₂ y t₃) z (BNode t₄ w t₅)))
  bal-right Black (Node {cᵣ = Black} Black _ _ t₁ x t₂) y (Down t₃) _ _ = Down (BNode t₁ x (RNode t₂ y t₃))
  
  bal-left : ∀ {d cₗ cᵣ} c → DelTree d cₗ → A → Tree d cᵣ → color-valid c cₗ → color-valid c cᵣ → DelTree (incr-Black d c) c
  bal-left {cₗ = Black} {cᵣ = Black} Red (Stay {c = Black} _ _ l) v r _ _ = Stay Red tt (RNode l v r)
  bal-left {cₗ = Black} {cᵣ = Black} Red (Stay {c = Red} _ () l) v r _ _
  bal-left {cₗ = Black} {cᵣ = Black} Red (Down t₁) x (Node {cₗ = Red} _ _ _ (Node {cₗ = Black} {cᵣ = Black} _ _ _ t₂ y t₃) z t₄) _ _ =
    Stay Red tt (RNode (BNode t₁ x t₂) y (BNode t₃ z t₄))
  bal-left {cₗ = Black} {cᵣ = Black} Red (Down t₁) x (Node {cₗ = Black} _ _ _ t₂ y t₃) _ _ = Stay Red tt (BNode (RNode t₁ x t₂) y t₃)
  bal-left Black (Stay _ _ l) v r _ _ = Stay Black tt (BNode l v r)
  bal-left {cᵣ = Black} Black (Down t₁) x (Node {cₗ = Red} Black _ _ (Node {cₗ = Black} {cᵣ = Black} _ _ _ t₂ y t₃) z t₄) _ _ =
    Stay Black tt (BNode (BNode t₁ x t₂) y (BNode t₃ z t₄))
  bal-left {cᵣ = Red} Black (Down t₁) x (Node {cₗ = Black} {cᵣ = Black} _ _ _ (Node {cₗ = Red} Black _ _ (Node {cₗ = Black} {cᵣ = Black} _ _ _ t₂ y t₃) z t₄) w t₅) _ _ =
    Stay Black tt (BNode (BNode t₁ x t₂) y (RNode (BNode t₃ z t₄) w t₅))
  bal-left {cᵣ = Red} Black (Down t₁) x (Node {cₗ = Black} {cᵣ = Black} _ _ _ (Node {cₗ = Black} _ _ _ t₂ y t₃) z t₄) _ _ =
    Stay Black tt (BNode (BNode (RNode t₁ x t₂) y t₃) z t₄) 
  bal-left {cᵣ = Black} Black (Down t₁) x (Node {cₗ = Black} _ _ _ t₂ y t₃) _ _ = Down (BNode (RNode t₁ x t₂) y t₃)
