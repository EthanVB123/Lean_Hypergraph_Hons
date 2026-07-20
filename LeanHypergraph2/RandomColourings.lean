import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace RandomColouring

open Set
open Hypergraph
open MeasureTheory
open ProbabilityTheory
open ENNReal

variable {α : Type*} {H : Hypergraph α} {n : Nat}
variable [Fintype ↑V(H)]
variable [NeZero n]
variable [DecidableEq ↑V(H)]
/-- does this need to be a variable? -/
abbrev RandomVertexColouring (H : Hypergraph α) (n : Nat) := ↑H.vertexSet → Fin n
variable [MeasurableSpace (RandomVertexColouring H n)]

noncomputable def UniformRandomVertexColouringMeasure
    (H : Hypergraph α) (n : Nat) [Fintype (H.vertexSet)] [NeZero n] :
    Measure (RandomVertexColouring H n) :=
    uniformOn Set.univ

#check UniformRandomVertexColouringMeasure

local notation "Ω" => RandomVertexColouring H n
local notation "ℙ" => UniformRandomVertexColouringMeasure H n

instance randomVertexColouringMeasure_isProbabilityMeasure
    (H : Hypergraph α) (n : Nat) [Fintype (H.vertexSet)] [NeZero n] :
    IsProbabilityMeasure (UniformRandomVertexColouringMeasure H n) := by
    apply ProbabilityTheory.isProbabilityMeasure_uniformOn
    · simp
    · refine ⟨fun _ => (0 : Fin n), trivial⟩

instance randomVertexColouring_isFinite :
    Fintype (RandomVertexColouring H n) := inferInstance

lemma number_of_colourings : Fintype.card (Ω) = n ^ (Fintype.card (↑V(H))) := by simp


theorem RTP_uniform (v : H.vertexSet) :
    ℙ {c : Ω | c v = 0} = 1 / n := by
        sorry

#check Fintype.card_fun
#synth Fintype (Fin 3 → Fin 4)
end RandomColouring
