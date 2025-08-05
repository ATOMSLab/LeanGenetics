/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.NNReal.Defs

open scoped BigOperators NNReal List

/-  This file implements Felsenstein’s pruning algorithm for computing the likelihood of a
     rooted phylogenetic tree under a finite‑state continuous‑time substitution model
     and proves that the likelihood computed at an internal node is monotone with
     respect to component‑wise increases of each child‑node likelihood vector. -/

namespace Bio.Phylo

/-! ### 0.  Basic finite state type -/

/-- A discrete character state (e.g. nucleotide or amino‑acid).  Internally this
    is just `Fin m`.  The parameter `m` is kept explicit to make matrices and
    vectors first‑class Lean terms that carry their dimension. -/
abbrev State (m : ℕ) := Fin m

/-! ### 1.  Markov model primitives -/

/-- Transition probabilities **P(child = j ∣ parent = i)**.
    Stored as non‑negative reals (`ℝ≥0`) so that inequalities are in‑built. -/
abbrev Matrix (m : ℕ) := State m → State m → ℝ≥0

/-- Likelihood vector ℓ : the probability (up to a scaling constant) of observing
    the data in the descendance of a node *given* that the node itself is in a
    particular state. -/
abbrev LikVec (m : ℕ) := State m → ℝ≥0

variable {m : ℕ} (hm : 0 < m)

instance : Fintype (State m) := Fin.fintype m

/-! ### 2.  Tree structure -/

/-- A rooted (ordered) tree whose leaves are labelled by observed states.  For a
    multi‑sequence alignment each *site* induces one such tree. -/
inductive Tree (m : ℕ) : Type
  | leaf (obs : Fin m)
  | node (children : List (Tree m))
  deriving Repr

namespace Tree

/-- Convenience accessor returning the list of children (empty on leaves). -/
@[simp] def children {m} : Tree m → List (Tree m)
  | leaf _    => []
  | node cs   => cs

end Tree

/-- Predicate stating that `t` is a leaf, i.e. `Tree.leaf o` for some `o`. -/
def IsLeaf (t : Tree m) : Prop :=
  ∃ o, t = Tree.leaf o

/-- Predicate stating that `t` is a node, i.e. `Tree.node cs` for some `cs`. -/
def IsNode (t : Tree m) : Prop :=
  ∃ cs, t = Tree.node cs

/-! ### 3.  Felsenstein pruning -/

/-- **Felsenstein pruning.**  For each node it returns a likelihood vector whose
    `s`‑th component is the conditional likelihood of the observed data in the
    subtree, given that the node is in state `s`. -/
def prune (P : Matrix m) : Tree m → LikVec m
  | .leaf s => fun t => if t = s then (1 : ℝ≥0) else 0
  | .node cs =>
      let childLikelihoods := cs.map (prune P)
      fun t =>
        let factors : List ℝ≥0 :=
          childLikelihoods.map (fun ℓ => ∑ s, ℓ s * P t s)
        factors.prod  -- `List.prod` multiplies all elements, neutral element 1

/- ### 4.  Auxiliary arithmetic lemmas -/

section Arithmetic
open Finset

/-- *Convex‑sum monotonicity.*  Increasing the coefficients of a non‑negative
    linear form increases the value of the form. -/
lemma sum_mul_mono {P : Matrix m} {ℓ₁ ℓ₂ : LikVec m} (hℓ : ∀ s, ℓ₁ s ≤ ℓ₂ s)
    (t : State m) :
    (∑ s, ℓ₁ s * P t s) ≤ (∑ s, ℓ₂ s * P t s) := by
  have h_term : ∀ s, ℓ₁ s * P t s ≤ ℓ₂ s * P t s := by
    intro s; exact mul_le_mul_of_nonneg_right (hℓ s) (by simp)
  exact Finset.sum_le_sum (fun s _ => h_term s)

/-- A product of non-negative elements is non-negative. -/
theorem list_prod_nonneg {α} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    {l : List α} (h : ∀ a ∈ l, 0 ≤ a) : 0 ≤ l.prod := by
  induction l with
  | nil => simp [List.prod]
  | cons head tail ih =>
      simp only [List.prod_cons]
      apply mul_nonneg
      · exact h head (by simp)
      · exact ih (fun a ha => h a (List.mem_cons_of_mem head ha))

/-- *List‑product monotonicity.*  If every factor of a product increases,
    the product itself increases. -/
lemma List.prod_mono {α} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    {xs ys : List α} (h_nonneg : ∀ x ∈ xs, 0 ≤ x) (h : List.Forall₂ (· ≤ ·) xs ys) : xs.prod ≤ ys.prod := by
  induction h with
  | nil => simp
  | cons hxy hrest ih =>
      simp only [List.prod_cons]
      apply mul_le_mul
      · exact hxy
      · exact ih (fun z hz => h_nonneg z (List.mem_cons_of_mem _ hz))
      · exact list_prod_nonneg (fun z hz => h_nonneg z (List.mem_cons_of_mem _ hz))
      · exact le_trans (h_nonneg _ (by simp)) hxy

end Arithmetic

/-! ### 5.  Main monotonicity theorem -/

open Tree

/-- A convenience predicate : `t₁`’s likelihood vector is component-wise
    ≤ the one of `t₂`. -/
def PruneLe (P : Matrix m) (t₁ t₂ : Tree m) : Prop :=
  ∀ s, prune P t₁ s ≤ prune P t₂ s

/--  Inductive predicate capturing the *point-wise* monotonicity assumption
     at the leaves together with the requirement that the two compared trees
     have the same topology. -/
inductive PruneMono (P : Matrix m) : Tree m → Tree m → Prop where
  | leaf  {l₁ l₂ : Tree m} (h₁ : IsLeaf l₁) (h₂ : IsLeaf l₂)
          (hle : PruneLe P l₁ l₂) :
      PruneMono P l₁ l₂
  | node  {cs₁ cs₂ : List (Tree m)}
          (h_rec : List.Forall₂ (PruneMono P) cs₁ cs₂) :
      PruneMono P (Tree.node cs₁) (Tree.node cs₂)

/-! ### 5A.  Node-level helper lemmas -/

/-- 1.  Every “factor” `∑ t, ℓ t * P s t` is non-negative (because we work in
        `ℝ≥0`).  Pack this once and for all. -/
private lemma factors_nonneg (P : Matrix m) (s : State m) (cs : List (Tree m)) :
    ∀ x ∈ (cs.map (fun c ↦ ∑ t, prune P c t * P s t)), (0 : ℝ≥0) ≤ x := by
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨c, _, rfl⟩
  exact Finset.sum_nonneg (by
    intro _ _; exact mul_nonneg (by simp) (by simp))

/-- 2.  If child–likelihood vectors are pair-wise `≤`, then the corresponding
        factors are `≤` as well.  This is the heart of the monotone step. -/
private lemma factors_le  (P : Matrix m) (s : State m)
    {cs₁ cs₂ : List (Tree m)} :
    List.Forall₂ (PruneLe P) cs₁ cs₂ →
    List.Forall₂ (· ≤ ·)
      (cs₁.map (fun c ↦ ∑ t, prune P c t * P s t))
      (cs₂.map (fun c ↦ ∑ t, prune P c t * P s t)) := by
  intro h
  induction h with
  | nil        => simp
  | cons h_le h_rest ih =>
      simp [List.map_cons, sum_mul_mono h_le s, ih]

/- ### 5B.  Main monotonicity theorem -/

/- Helper that converts a proof
    `List.Forall₂ (PruneMono P) cs₁ cs₂`
    into a proof
    `List.Forall₂ (fun t₁ t₂ ↦ M t₁ t₂) cs₁ cs₂`. -/
mutual
  /-- A custom induction principle for `PruneMono` proofs, defined by mutual
      recursion with `PruneMono.induction_on_list`. -/
  @[elab_as_elim]
  def PruneMono.induction
      {P : Matrix m}
      {M : Tree m → Tree m → Prop}
      (h_leaf :
          ∀ {l₁ l₂} (_ : IsLeaf l₁) (_ : IsLeaf l₂)
            (_ : PruneLe P l₁ l₂), M l₁ l₂)
      (h_node :
          ∀ {cs₁ cs₂}
            (_ : List.Forall₂ (PruneMono P) cs₁ cs₂)
            (_ : List.Forall₂ (fun t₁ t₂ ↦ M t₁ t₂) cs₁ cs₂),
            M (Tree.node cs₁) (Tree.node cs₂))
      {t₁ t₂ : Tree m} (h : PruneMono P t₁ t₂) : M t₁ t₂ :=
    match h with
    | .leaf h₁ h₂ hle => h_leaf h₁ h₂ hle
    | .node h_rec =>
        h_node h_rec (PruneMono.induction_on_list h_leaf h_node h_rec)

  /-- A helper for `PruneMono.induction` that handles the recursive step over
      a list of `PruneMono` proofs. -/
  def PruneMono.induction_on_list
      {P : Matrix m}
      {M : Tree m → Tree m → Prop}
      (h_leaf :
          ∀ {l₁ l₂} (_ : IsLeaf l₁) (_ : IsLeaf l₂)
            (_ : PruneLe P l₁ l₂), M l₁ l₂)
      (h_node :
          ∀ {cs₁ cs₂}
            (_ : List.Forall₂ (PruneMono P) cs₁ cs₂)
            (_ : List.Forall₂ (fun t₁ t₂ ↦ M t₁ t₂) cs₁ cs₂),
            M (Tree.node cs₁) (Tree.node cs₂))
      {cs₁ cs₂ : List (Tree m)}
      (h_rec : List.Forall₂ (PruneMono P) cs₁ cs₂)
      : List.Forall₂ (fun t₁ t₂ ↦ M t₁ t₂) cs₁ cs₂ :=
    match h_rec with
    | .nil => .nil
    | .cons hd tl =>
      .cons (PruneMono.induction h_leaf h_node hd) (PruneMono.induction_on_list h_leaf h_node tl)
end

/--  The pruning operator is monotone w.r.t. the point-wise order on
     likelihood vectors provided the hypotheses encoded in `PruneMono`. -/
theorem prune_mono (P : Matrix m)
    {t₁ t₂ : Tree m} (h : PruneMono P t₁ t₂) : PruneLe P t₁ t₂ := by
  /-  We use the *custom* eliminator. We define the motive `M` explicitly
      to be `PruneLe P` and then apply the induction. The goal in each
      branch of the induction will be to prove `PruneLe P t₁ t₂`, which
      we solve by introducing the state `s` and proving the inequality. -/
  refine PruneMono.induction (P := P) (M := PruneLe P) (t₁ := t₁) (t₂ := t₂) ?_ ?_ h
  · -- h_leaf
    intro l₁ l₂ h₁ h₂ hle
    exact hle
  · -- h_node
    intro cs₁ cs₂ h_rec ih
    intro s
    have h_nonneg :
        ∀ x ∈ (cs₁.map (fun c ↦ ∑ t, prune P c t * P s t)),
          (0 : ℝ≥0) ≤ x :=
      factors_nonneg P s cs₁
    have h_factor : List.Forall₂ (· ≤ ·)
        (cs₁.map (fun c ↦ ∑ t, prune P c t * P s t))
        (cs₂.map (fun c ↦ ∑ t, prune P c t * P s t)) :=
      factors_le P s ih
    simpa [prune] using List.prod_mono h_nonneg h_factor

theorem prune_perm_children (P : Matrix m)
    {cs₁ cs₂ : List (Tree m)} (hperm : cs₁ ~ cs₂) :
    prune P (.node cs₁) = prune P (.node cs₂) := by
  funext s
  simp [prune]
  apply List.Perm.prod_eq (List.Perm.map (fun c => ∑ t, prune P c t * P s t) hperm)

abbrev Prior (m : ℕ) := State m → ℝ≥0

def siteLikelihood (P : Matrix m) (π : Prior m) (t : Tree m) : ℝ≥0 :=
  ∑ s, π s * prune P t s

theorem siteLikelihood_mono (P : Matrix m) (π : Prior m)
    {t₁ t₂ : Tree m} (h : PruneMono P t₁ t₂) :
    siteLikelihood P π t₁ ≤ siteLikelihood P π t₂ := by
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left (prune_mono (P := P) h s) (by simp)

example (P : Matrix m) (cs : List (Tree m)) (σ : List (Tree m)) :
  σ ~ cs → prune P (.node σ) = prune P (.node cs) := prune_perm_children P
