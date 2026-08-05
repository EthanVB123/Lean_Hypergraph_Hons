-- Hypergraph Colourings

import Mathlib.Combinatorics.Hypergraph.Basic

namespace HypergraphColouring

open Set
open Hypergraph

variable {α β : Type*} {x y : α} {s t : Set α} {H : Hypergraph α}

/--
@[ext]
structure HyperColouring (α: Type*) (n : Nat) where
    /-- The original hypergraph -/
    hypergraph: Hypergraph α
    /-- The colouring function -/
    colouring: α → Fin n
-/

abbrev HyperColouring (α : Type*) (n : Nat) := α → Fin n

lemma no_zero_colouring (H: Hypergraph α) (c : HyperColouring α 0) : H.vertexSet = ∅ := by
    ext v
    simp only [mem_empty_iff_false, iff_false]
    exact Fin.elim0 (c v)

def MonochromaticEdge {n} (c : HyperColouring α n) (edge : Set α) : Prop :=
    ∃ x ∈ edge, ∀ y ∈ edge, c x = c y

def ProperColouring {n} (H : Hypergraph α) (c : HyperColouring α n) : Prop :=
    ∀ e ∈ H.edgeSet, ¬ MonochromaticEdge c e

lemma empty_hypergraph_is_properly_coloured {n} (H : Hypergraph α) (c : HyperColouring α n) :
    ¬ H.IsNonempty → ProperColouring H c := by
    intro h
    simp [IsNonempty] at h
    have hv := h.2
    have emptyedges : H.edgeSet = ∅ := by simpa using Set.not_nonempty_iff_eq_empty.mp hv
    simp [ProperColouring]
    intro c hc
    simp [emptyedges] at hc

lemma one_colouring_implies_monochromatic (h : H.IsNonempty) (c : HyperColouring α 1) :
    ¬ IsTrivial H → ∀ e ∈ H.edgeSet, MonochromaticEdge c e := by
    intro h' e he
    simp [MonochromaticEdge]
    simp [IsTrivial] at h'
    simp [IsNonempty] at h
    have l : e.Nonempty := sorry
    have o1 : ∀ m , c m = 0 := by
        intro m
        exact Fin.fin_one_eq_zero (c m)
    rcases l with ⟨v, hv⟩
    refine ⟨ v, hv, ?_ ⟩
    intro y hy
    rw [o1 v, o1 y]


def adjacency_set (H : Hypergraph α) (v : α) : Set α :=
    { w | H.Adj v w }

def adjacency_finset (H : Hypergraph α) (v : α) [Fintype (adjacency_set H v)] : Finset α :=
    (adjacency_set H v).toFinset



end HypergraphColouring
