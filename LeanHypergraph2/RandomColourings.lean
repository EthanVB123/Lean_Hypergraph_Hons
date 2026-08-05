import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic

import LeanHypergraph2.HypergraphColourings

namespace RandomColouring

open Set
open Hypergraph
open MeasureTheory
open ProbabilityTheory
open ENNReal

variable {H : Hypergraph α} {n : Nat}
variable {v w : H.vertexSet} {i j : Fin n}
variable {e : E(H)}
variable [Fintype ↑V(H)]
variable [NeZero n]
variable [DecidableEq ↑V(H)]
/-- does this need to be a variable? -/
abbrev RandomVertexColouring (H : Hypergraph α) (n : Nat) := HypergraphColouring.HyperColouring ↑H.vertexSet n

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

noncomputable instance edge_fintype (e : H.edgeSet) : Fintype e := by
  have hsub : e.val ⊆ H.vertexSet := by
    apply H.subset_vertexSet_of_mem_edgeSet' e.property
  have hfin : (e : Set α).Finite :=
    (Set.toFinite H.vertexSet).subset hsub
  exact hfin.fintype

noncomputable instance edge_set_fintype : Fintype ↑E(H) := by
  have hsub : ∀ e : ↑E(H), e.val ⊆ ↑V(H) := by
    intro e
    apply H.subset_vertexSet_of_mem_edgeSet' e.property
  have hedgeinpow : ∀ e : ↑E(H), e.val ∈ Set.powerset ↑V(H) := by
    intro e
    exact hsub e
  have hsubpow : ↑E(H) ⊆ Set.powerset ↑V(H) := by
    intro e he
    exact hedgeinpow ⟨e,he⟩
  have hpowfin : (Set.powerset ↑V(H)).Finite := by
    exact (Set.toFinite ↑V(H)).powerset
  have hfin : (H.edgeSet : Set (Set α)).Finite := by
    exact hpowfin.subset hsubpow
  exact hfin.fintype

lemma number_of_colourings : Fintype.card (Ω) = n ^ (Fintype.card (↑V(H))) := by simp

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

lemma colourAt_uniform (v : H.vertexSet) (i : Fin n):
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

lemma colourAt_measurable : ∀ v : H.vertexSet, Measurable (colourAt (n := n) v) := by
    intro v
    exact measurable_pi_apply v


lemma colourAt_indep
    (hvw : v ≠ w) :
    ProbabilityTheory.IndepFun (colourAt v) (colourAt w) ℙ := by
    exact colourAt_independent.indepFun hvw

lemma two_vertices_restricted_proba (hvw : v ≠ w) : ℙ {c : Ω | colourAt v c = i ∧ colourAt w c = j} = (1 / n) * (1 / n) := by
  rw [show {c : Ω | colourAt v c = i ∧ colourAt w c = j} = colourAt v ⁻¹' {i} ∩ colourAt w ⁻¹' {j} by rfl]
  rw [ProbabilityTheory.IndepFun.measure_inter_preimage_eq_mul (colourAt_indep hvw)]
  · rw [show colourAt v ⁻¹' {i} = {c | colourAt v c = i} by rfl]
    rw [show colourAt w ⁻¹' {j} = {c | colourAt w c = j} by rfl]
    rw [colourAt_uniform v i, colourAt_uniform w j]
  · exact MeasurableSet.singleton i
  · exact MeasurableSet.singleton j

lemma edge_restricted_proba : ℙ {c : Ω | ∀ ve ∈ e, colourAt ve c = i} = (1 / n) ^ (Fintype.card e) := by

lemma two_vertices_same_colour (hvw : v ≠ w):
  ℙ {c : Ω | colourAt v c = colourAt w c} = 1 / n := by
    have h_event : {c : Ω | colourAt v c = colourAt w c} = ⋃ i : Fin n, {c : Ω | colourAt v c = i ∧ colourAt w c = i} := by
      ext c
      constructor
      · intro hc
        refine Set.mem_iUnion.mpr ⟨colourAt v c, ?_⟩
        exact ⟨rfl, hc.symm⟩
      · intro h
        rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
        exact hi.1.trans hi.2.symm
    rw [h_event]
    sorry




def IsNUniform (n : Nat) : Prop :=
  ∀ e : H.edgeSet, Fintype.card e = n


def HasPropertyB (H : Hypergraph α): Prop :=
  ∃ c : RandomVertexColouring H 2, HypergraphColouring.ProperColouring H c

theorem erdos_propertyB (h_uniform : IsNUniform (H := H) k) (max_edges : Fintype.card E(H) < 2 ^ (k - 1)) :
  HasPropertyB H := by

  sorry




end RandomColouring
