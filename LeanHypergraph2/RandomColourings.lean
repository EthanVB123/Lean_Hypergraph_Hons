import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic

namespace RandomColouring

open Set
open Hypergraph
open MeasureTheory
open ProbabilityTheory
open ENNReal

variable {H : Hypergraph α} {n : Nat}
variable {v : H.vertexSet} {i : Fin n}
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
local notation "ℙΠ" => UniformProductVertexColouringMeasure

instance randomVertexColouringMeasure_isProbabilityMeasure
    (H : Hypergraph α) (n : Nat) [Fintype (H.vertexSet)] [NeZero n] :
    IsProbabilityMeasure (UniformRandomVertexColouringMeasure H n) := by
    apply ProbabilityTheory.isProbabilityMeasure_uniformOn
    · simp
    · refine ⟨fun _ => (0 : Fin n), trivial⟩

instance randomVertexColouring_isFinite :
    Fintype (RandomVertexColouring H n) := inferInstance

instance ColouringMeasure_isSigmaFinite :
    SigmaFinite ℙ := inferInstance

lemma number_of_colourings : Fintype.card (Ω) = n ^ (Fintype.card (↑V(H))) := by simp

#check Measure.ext_iff_singleton

lemma product_of_vertex_functions_is_all_colourings :
    Set.univ.pi (fun _ : H.vertexSet => (Set.univ : Set (Fin n))) = (Set.univ : Set (RandomVertexColouring H n)) := by
    ext c
    simp

lemma uniform_measure_is_pi_measure :
    ℙ = ℙΠ := by
    unfold UniformRandomVertexColouringMeasure UniformProductVertexColouringMeasure
    rw [← product_of_vertex_functions_is_all_colourings]
    rw [uniformOn_pi (f := fun _ : H.vertexSet => (Set.univ : Set (Fin n)))]
    simp [UniformColourMeasure]

def colourAt (v : H.vertexSet) : Ω → Fin n := fun ω => ω v

lemma expand_colouring_filter :
    {c : Ω | c v = i} = Set.pi ({v} : Finset (H.vertexSet))
    (fun w => if w = v then ({i} : Set (Fin n)) else Set.univ) := by
  ext c
  simp

theorem each_vertex_has_uniform_colouring:
    ℙ {c : Ω | c v = i} = 1 / n := by
    rw [uniform_measure_is_pi_measure]
    rw [expand_colouring_filter]
    unfold UniformProductVertexColouringMeasure
    unfold UniformColourMeasure
    rw [Measure.pi_pi_finset]
    simp
    rw [uniformOn_univ]
    simp

lemma colourAt_uniform:
    ℙ {c : Ω | colourAt v c = i} = 1 / n := by
    unfold colourAt
    rw [each_vertex_has_uniform_colouring]

lemma colourAt_independent:
    ProbabilityTheory.iIndepFun (fun v => colourAt v) ℙ := by
    rw [uniform_measure_is_pi_measure]
    unfold UniformProductVertexColouringMeasure
    unfold colourAt
    unfold UniformColourMeasure
    change ProbabilityTheory.iIndepFun (fun v ω => (id : Fin n → Fin n) (ω v)) (Measure.pi (fun _ => uniformOn Set.univ))
    apply ProbabilityTheory.iIndepFun_pi
    intro v
    exact aemeasurable_id



end RandomColouring
