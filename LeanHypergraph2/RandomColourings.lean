import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace RandomColouring

open Set
open Hypergraph
open MeasureTheory
open ProbabilityTheory
open ENNReal

variable {α β : Type*} {x y : α} {s t : Set α} {H : Hypergraph α} {n : Nat}
variable [Fintype (H.vertexSet)]
variable [NeZero n]
abbrev RandomVertexColouring (H : Hypergraph α) (n : Nat) := H.vertexSet → Fin n
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

/-- RTP colour of a vertex has uniform distribution -/
theorem RTP_uniform (v : H.vertexSet) :
    ℙ {c : Ω | c v = 0} = 1 / n := by
    sorry


end RandomColouring
