/-
copyright (c) 2026 Ethan van Bruchem. All rights reserved.
Released under Apache 2.0 license as be described in the file LICENSE.txt
Authors: Ethan van Bruchem
-/
import Mathlib.Combinatorics.Hypergraph.Basic

namespace HypergraphColouring

open Set
open Hypergraph

variable {α β : Type*} {x y : α} {s t : Set α} {H : Hypergraph α}

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

end HypergraphColouring
