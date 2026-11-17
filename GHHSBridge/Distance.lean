/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GHHSBridge.OfMeasure

/-!
# The GHHS cut distance in kernel terms

This file states the cut distance of GHHS (Discrete Analysis 2023:8) for Latinons on
the ground space `I` in their own kernel terms, and proves that it equals the cut
distance `latinonCutDistance` of the measure representation.

* Section 2.4.1 of GHHS: for `X : I × I → ℝ`, `‖X‖_□ = sup_{S,T} |∫_{S×T} X|`
  (`graphonCut`). The relabelling is `W^{φ,ψ}(x, y) = W(φ x, ψ y)`, with `φ, ψ` in the
  set `S` of invertible measure-preserving maps (`relabelKernel`, `LatinonRelabel`).
* Definition 4.1: for a distribution-valued signed bigraphon,
  `‖W‖_{□,◻} = sup_{R,C,V} |∫_{R×C} W(x,y)(V)|`, with `V` an interval. For a difference
  `W − U` this is `kernelCut W U`. The symbol sets of `LatinonBox` are the measurable
  order-connected subsets of `I`, that is, the intervals of `I`.
* Definition 4.2: `O(x, y) = 1` if `x < y` and `0` otherwise; `O^f(x, y) = O(f x, f y)`
  is `orderGraphon f`.
* Definition 4.3, formula (2):
  `δ_□(L₁, L₂) = inf_{φ,ψ ∈ S} ‖O^f − O^{gφ}‖_□ + ‖O^f − O^{gψ}‖_□ + ‖W − U^{φ,ψ}‖_{□,◻}`
  (`ghhsCutDistance`).

The main result is `ghhsCutDistance_eq`: for GHHS Latinons `L₁, L₂`,
`ghhsCutDistance L₁ L₂ = latinonCutDistance L₁.toLatinonMeasure L₂.toLatinonMeasure`.
This is the distance part (2.1) of Proposition 2.3 of the Latinon preprint.
-/

@[expose] public section

noncomputable section

namespace GHHSBridge

open MeasureTheory ProbabilityTheory LatinonEntropy
open scoped unitInterval ENNReal

/-! ### Cut norms in GHHS form -/

/-- GHHS cut norm of a real function on `I × I` (Section 2.4.1). -/
def graphonCut (X : I × I → ℝ) : ℝ :=
  cutValueSup (fun R : LatinonRectangle =>
    |∫ p in R.rows ×ˢ R.cols, X p ∂unitSquareVolume|)

/-- GHHS Definition 4.1 for the difference `K − K'` of two distribution-valued bigraphons. -/
def kernelCut (K K' : Kernel (I × I) I) : ℝ :=
  cutValueSup (fun B : LatinonBox =>
    |∫ p in B.rows ×ˢ B.cols, ((K p).real B.symbols - (K' p).real B.symbols) ∂unitSquareVolume|)

/-- GHHS Definition 4.2 composed with an order map: `O^f(x, y) = O(f x, f y)`. -/
def orderGraphon (f : I → I) : I × I → ℝ :=
  (orderRelation f).indicator (fun _ => (1 : ℝ))

theorem orderGraphon_apply (f : I → I) (p : I × I) :
    orderGraphon f p = if f p.1 < f p.2 then 1 else 0 := by
  simp [orderGraphon, orderRelation, Set.indicator_apply]

/-- GHHS relabelling `W^{φ,ψ}(x, y) = W(φ x, ψ y)`. -/
def relabelKernel (K : Kernel (I × I) I) (e f : LatinonRelabel) : Kernel (I × I) I :=
  K.comap (Prod.map e f)
    ((e.measurable.comp measurable_fst).prodMk (f.measurable.comp measurable_snd))

instance (K : Kernel (I × I) I) [IsMarkovKernel K] (e f : LatinonRelabel) :
    IsMarkovKernel (relabelKernel K e f) := by
  unfold relabelKernel
  infer_instance

/-- GHHS Definition 4.3, the cost of one pair `(φ, ψ)` in formula (2). -/
def ghhsAlignmentCost (L₁ L₂ : GHHSLatinon) (e f : LatinonRelabel) : ℝ :=
  graphonCut (fun p => orderGraphon L₁.order p - orderGraphon (L₂.order ∘ e) p) +
    graphonCut (fun p => orderGraphon L₁.order p - orderGraphon (L₂.order ∘ f) p) +
    kernelCut L₁.kernel (relabelKernel L₂.kernel e f)

/-- **GHHS Definition 4.3**, the cut distance of Latinons, on the ground space `I`. -/
def ghhsCutDistance (L₁ L₂ : GHHSLatinon) : ℝ :=
  sInf (Set.range (fun p : LatinonRelabel × LatinonRelabel => ghhsAlignmentCost L₁ L₂ p.1 p.2))

/-! ### The order terms -/

theorem integrable_orderGraphon {f : I → I} (hf : Measurable f) (μ : Measure (I × I))
    [IsFiniteMeasure μ] : Integrable (orderGraphon f) μ :=
  (integrable_const (1 : ℝ)).indicator (orderRelation_measurable f hf)

theorem setIntegral_orderGraphon {f : I → I} (hf : Measurable f) (R : LatinonRectangle) :
    ∫ p in R.rows ×ˢ R.cols, orderGraphon f p ∂unitSquareVolume = orderBox f R := by
  unfold orderGraphon orderBox
  rw [integral_indicator_const _ (orderRelation_measurable f hf), smul_eq_mul, mul_one,
    measureReal_restrict_apply (orderRelation_measurable f hf), Set.inter_comm]

theorem graphonCut_orderGraphon_sub {f g : I → I} (hf : Measurable f) (hg : Measurable g) :
    graphonCut (fun p => orderGraphon f p - orderGraphon g p) = orderCut f g := by
  unfold graphonCut orderCut
  congr 1
  funext R
  rw [integral_sub (integrable_orderGraphon hf _) (integrable_orderGraphon hg _),
    setIntegral_orderGraphon hf R, setIntegral_orderGraphon hg R]

/-! ### The symbol term -/

theorem integrable_kernel_real (K : Kernel (I × I) I) [IsMarkovKernel K] {V : Set I}
    (hV : MeasurableSet V) (μ : Measure (I × I)) [IsFiniteMeasure μ] :
    Integrable (fun p => (K p).real V) μ :=
  (integrable_const (1 : ℝ)).mono' (K.measurable_coe hV).ennreal_toReal.aestronglyMeasurable
    (ae_of_all _ fun p => by
      rw [Real.norm_of_nonneg measureReal_nonneg]
      exact (probability_real_set_bounds (K p) V).2)

/-- `∫_{R×C} K(x,y)(V) = ν_K (R × C × V)`. -/
theorem setIntegral_kernel_real (K : Kernel (I × I) I) [IsMarkovKernel K] {R C V : Set I}
    (hR : MeasurableSet R) (hC : MeasurableSet C) (hV : MeasurableSet V) :
    ∫ p in R ×ˢ C, (K p).real V ∂unitSquareVolume =
      (unitSquareVolume ⊗ₘ K).real ((R ×ˢ C) ×ˢ V) := by
  simp only [measureReal_def]
  rw [Measure.compProd_apply_prod (hR.prod hC) hV,
    integral_toReal (K.measurable_coe hV).aemeasurable (ae_of_all _ fun p => measure_lt_top _ _)]

/-- Change of variables: relabelling the kernel relabels `ν_K` on boxes. -/
theorem compProd_relabelKernel_box (K : Kernel (I × I) I) [IsMarkovKernel K]
    (e f : LatinonRelabel) {R C V : Set I}
    (hR : MeasurableSet R) (hC : MeasurableSet C) (hV : MeasurableSet V) :
    (unitSquareVolume ⊗ₘ relabelKernel K e f) ((R ×ˢ C) ×ˢ V) =
      (unitSquareVolume ⊗ₘ K) (((e.symm ⁻¹' R) ×ˢ (f.symm ⁻¹' C)) ×ˢ V) := by
  have hR' : MeasurableSet (e.symm ⁻¹' R) := hR.preimage e.symm.measurable
  have hC' : MeasurableSet (f.symm ⁻¹' C) := hC.preimage f.symm.measurable
  rw [Measure.compProd_apply_prod (hR.prod hC) hV,
    Measure.compProd_apply_prod (hR'.prod hC') hV]
  have hmp : MeasurePreserving (Prod.map e f) unitSquareVolume unitSquareVolume :=
    e.preserves.prod f.preserves
  have hemb : MeasurableEmbedding (Prod.map e f) :=
    e.equiv.measurableEmbedding.prodMap f.equiv.measurableEmbedding
  have hpre : Prod.map e f ⁻¹' ((e.symm ⁻¹' R) ×ˢ (f.symm ⁻¹' C)) = R ×ˢ C := by
    ext p
    simp [LatinonRelabel.symm_apply_apply]
  rw [← hmp.setLIntegral_comp_preimage_emb hemb (fun p => K p V), hpre]
  rfl

theorem compProd_relabelKernel_real_box (K : Kernel (I × I) I) [IsMarkovKernel K]
    (e f : LatinonRelabel) {R C V : Set I}
    (hR : MeasurableSet R) (hC : MeasurableSet C) (hV : MeasurableSet V) :
    (unitSquareVolume ⊗ₘ relabelKernel K e f).real ((R ×ˢ C) ×ˢ V) =
      (unitSquareVolume ⊗ₘ K).real (((e.symm ⁻¹' R) ×ˢ (f.symm ⁻¹' C)) ×ˢ V) := by
  simpa only [measureReal_def] using
    congrArg ENNReal.toReal (compProd_relabelKernel_box K e f hR hC hV)

/-- The symbol term of formula (2) in kernel terms equals the distribution cut of the
measure representation. -/
theorem kernelCut_relabel_eq_measureCut (L₁ L₂ : GHHSLatinon) (e f : LatinonRelabel) :
    kernelCut L₁.kernel (relabelKernel L₂.kernel e f) =
      measureCut L₁.measure (relabelLatinonMeasure L₂.measure e f) := by
  unfold kernelCut measureCut
  congr 1
  funext B
  obtain ⟨⟨R, C, hR, hC⟩, V, hV, -⟩ := B
  change |∫ p in R ×ˢ C, ((L₁.kernel p).real V - (relabelKernel L₂.kernel e f p).real V)
      ∂unitSquareVolume| =
    |(unitSquareVolume ⊗ₘ L₁.kernel).real ((R ×ˢ C) ×ˢ V) -
      (relabelLatinonMeasure (unitSquareVolume ⊗ₘ L₂.kernel) e f).real ((R ×ˢ C) ×ˢ V)|
  rw [integral_sub (integrable_kernel_real L₁.kernel hV _)
      (integrable_kernel_real (relabelKernel L₂.kernel e f) hV _),
    setIntegral_kernel_real L₁.kernel hR hC hV,
    setIntegral_kernel_real (relabelKernel L₂.kernel e f) hR hC hV,
    compProd_relabelKernel_real_box L₂.kernel e f hR hC hV,
    relabelLatinonMeasure_real_box _ e f R C V hR hC hV]

/-! ### Equality of the distances -/

theorem ghhsAlignmentCost_eq (L₁ L₂ : GHHSLatinon) (e f : LatinonRelabel) :
    ghhsAlignmentCost L₁ L₂ e f =
      latinonAlignmentCost L₁.toLatinonMeasure L₂.toLatinonMeasure e f := by
  have h₁ := L₁.order_measurePreserving.measurable
  have h₂ := L₂.order_measurePreserving.measurable
  unfold ghhsAlignmentCost latinonAlignmentCost
  rw [graphonCut_orderGraphon_sub h₁ (h₂.comp e.measurable),
    graphonCut_orderGraphon_sub h₁ (h₂.comp f.measurable),
    kernelCut_relabel_eq_measureCut]
  rfl

/-- **Distance part of Proposition 2.3.** The GHHS cut distance of two GHHS Latinons
equals the cut distance of their measure representations. -/
theorem ghhsCutDistance_eq (L₁ L₂ : GHHSLatinon) :
    ghhsCutDistance L₁ L₂ = latinonCutDistance L₁.toLatinonMeasure L₂.toLatinonMeasure := by
  unfold ghhsCutDistance latinonCutDistance
  simp only [ghhsAlignmentCost_eq]

/-- The same statement read from the measure side. -/
theorem latinonCutDistance_eq_ghhs (W V : LatinonMeasure) :
    latinonCutDistance W V = ghhsCutDistance (ofLatinonMeasure W) (ofLatinonMeasure V) := by
  rw [ghhsCutDistance_eq, toLatinonMeasure_ofLatinonMeasure, toLatinonMeasure_ofLatinonMeasure]

/-- Changing the kernel on a null set does not change the measure representation. -/
theorem toLatinonMeasure_eq_of_ae {L L' : GHHSLatinon}
    (hK : ∀ᵐ p ∂unitSquareVolume, L.kernel p = L'.kernel p) (ho : L.order = L'.order) :
    L.toLatinonMeasure = L'.toLatinonMeasure :=
  latinonMeasure_ext (measure_eq_of_ae_kernel_eq hK) ho

/-- The GHHS cut distance does not see null modifications of the kernels, consistent
with the identification of Latinons up to null sets in GHHS. -/
theorem ghhsCutDistance_congr_ae {L₁ L₁' L₂ L₂' : GHHSLatinon}
    (h₁ : ∀ᵐ p ∂unitSquareVolume, L₁.kernel p = L₁'.kernel p) (o₁ : L₁.order = L₁'.order)
    (h₂ : ∀ᵐ p ∂unitSquareVolume, L₂.kernel p = L₂'.kernel p) (o₂ : L₂.order = L₂'.order) :
    ghhsCutDistance L₁ L₂ = ghhsCutDistance L₁' L₂' := by
  rw [ghhsCutDistance_eq, ghhsCutDistance_eq, toLatinonMeasure_eq_of_ae h₁ o₁,
    toLatinonMeasure_eq_of_ae h₂ o₂]

end GHHSBridge
