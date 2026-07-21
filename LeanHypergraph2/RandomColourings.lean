import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace RandomColouring

open Set
open Hypergraph
open MeasureTheory
open ProbabilityTheory
open ENNReal

variable {H : Hypergraph α} {n : Nat}
variable [Fintype ↑V(H)]
variable [NeZero n]
variable [DecidableEq ↑V(H)]
/-- does this need to be a variable? -/
abbrev RandomVertexColouring (H : Hypergraph α) (n : Nat) := ↑H.vertexSet → Fin n

noncomputable def UniformRandomVertexColouringMeasure
    (H : Hypergraph α) (n : Nat) [Fintype (H.vertexSet)] [NeZero n] :
    Measure (RandomVertexColouring H n) :=
    uniformOn Set.univ

noncomputable def UniformColourMeasure (n : Nat) : Measure (Fin n) :=
    uniformOn Set.univ

noncomputable def UniformProductVertexColouringMeasure : Measure (RandomVertexColouring H n) :=
    Measure.pi (fun _ : H.vertexSet => UniformColourMeasure n)

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

lemma product_measure_point_probability (c : Ω) :
    UniformProductVertexColouringMeasure {c} = (n : ℝ≥0∞)⁻¹ ^ Fintype.card (↑V(H)) := by
    rw [UniformProductVertexColouringMeasure]
    sorry

#check Measure.ext_iff_singleton

lemma product_of_vertex_functions_is_all_colourings :
    Set.univ.pi (fun _ : H.vertexSet => (Set.univ : Set (Fin n))) = (Set.univ : Set (RandomVertexColouring H n)) := by
    ext c
    simp

lemma uniform_measure_is_pi_measure :
    UniformRandomVertexColouringMeasure H n = UniformProductVertexColouringMeasure := by
    unfold UniformRandomVertexColouringMeasure UniformProductVertexColouringMeasure
    rw [← product_of_vertex_functions_is_all_colourings]
    rw [uniformOn_pi (f := fun _ : H.vertexSet => (Set.univ : Set (Fin n)))]
    simp [UniformColourMeasure]

theorem RTP_uniform (v : H.vertexSet) :
    ℙ {c : Ω | c v = 0} = 1 / n := by
        sorry

end RandomColouring
