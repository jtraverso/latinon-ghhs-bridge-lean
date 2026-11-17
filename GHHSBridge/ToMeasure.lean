/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GHHSBridge.Defs

/-!
# From GHHS Latinons to Latinon measures

For a GHHS Latinon `(K, f)` on `I`, the measure `ν_K = λ² ⊗ K` has uniform pair
marginals, so it is a `LatinonEntropy.LatinonMeasure` with the same order map.

* The `(x, y)` marginal is uniform because each `K (x, y)` is a probability measure.
* The `(x, z)` marginal is uniform because, for almost every row `x`, the second
  marginal of the row permuton gives `∫ K (x, y) (U) dy = λ (U)`.
* The `(y, z)` marginal is uniform by the same argument on columns.

This is the direction "kernel ⇒ measure" of Proposition 2.3 of the Latinon preprint.
-/

@[expose] public section

noncomputable section

namespace GHHSBridge

open MeasureTheory ProbabilityTheory LatinonEntropy
open scoped unitInterval ENNReal

variable {K : Kernel (I × I) I} {f : I → I}

/-- The symbol marginal of the row measure at `x` is `U ↦ ∫ K (x, y) (U) dy`. -/
theorem rowMeasure_map_snd_apply [IsMarkovKernel K] (hf : Measurable f) (x : I)
    {U : Set I} (hU : MeasurableSet U) :
    (rowMeasure K f x).map Prod.snd U = ∫⁻ y, K (x, y) U := by
  unfold rowMeasure
  rw [Measure.map_map measurable_snd (by fun_prop)]
  have hcomp : (Prod.snd ∘ fun p : I × I => (f p.1, p.2)) = Prod.snd := rfl
  have hpre : (Prod.snd ⁻¹' U : Set (I × I)) = Set.univ ×ˢ U := by
    ext p; simp
  rw [hcomp, Measure.map_apply measurable_snd hU, hpre,
    Measure.compProd_apply_prod MeasurableSet.univ hU]
  simp [Kernel.comap_apply]

/-- The symbol marginal of the column measure at `y` is `U ↦ ∫ K (x, y) (U) dx`. -/
theorem colMeasure_map_snd_apply [IsMarkovKernel K] (hf : Measurable f) (y : I)
    {U : Set I} (hU : MeasurableSet U) :
    (colMeasure K f y).map Prod.snd U = ∫⁻ x, K (x, y) U := by
  unfold colMeasure
  rw [Measure.map_map measurable_snd (by fun_prop)]
  have hcomp : (Prod.snd ∘ fun p : I × I => (f p.1, p.2)) = Prod.snd := rfl
  have hpre : (Prod.snd ⁻¹' U : Set (I × I)) = Set.univ ×ˢ U := by
    ext p; simp
  rw [hcomp, Measure.map_apply measurable_snd hU, hpre,
    Measure.compProd_apply_prod MeasurableSet.univ hU]
  simp [Kernel.comap_apply]

namespace GHHSLatinon

/-- Rows: for almost every `x`, `∫ K (x, y) (U) dy = λ (U)`. -/
theorem ae_row_lintegral (L : GHHSLatinon) {U : Set I} (hU : MeasurableSet U) :
    ∀ᵐ x ∂(volume : Measure I), ∫⁻ y, L.kernel (x, y) U = volume U := by
  filter_upwards [L.row_permuton] with x hx
  rw [← rowMeasure_map_snd_apply L.order_measurePreserving.measurable x hU, hx.2]

/-- Columns: for almost every `y`, `∫ K (x, y) (U) dx = λ (U)`. -/
theorem ae_col_lintegral (L : GHHSLatinon) {U : Set I} (hU : MeasurableSet U) :
    ∀ᵐ y ∂(volume : Measure I), ∫⁻ x, L.kernel (x, y) U = volume U := by
  filter_upwards [L.col_permuton] with y hy
  rw [← colMeasure_map_snd_apply L.order_measurePreserving.measurable y hU, hy.2]

theorem measure_xy (L : GHHSLatinon) {S T : Set I}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    L.measure ((S ×ˢ T) ×ˢ Set.univ) = volume S * volume T := by
  rw [L.measure_rectangle hS hT MeasurableSet.univ]
  simp only [measure_univ, lintegral_const, one_mul, Measure.restrict_apply_univ]
  exact Measure.prod_prod S T

theorem measure_xz (L : GHHSLatinon) {S U : Set I}
    (hS : MeasurableSet S) (hU : MeasurableSet U) :
    L.measure ((S ×ˢ Set.univ) ×ˢ U) = volume S * volume U := by
  rw [L.measure_rectangle hS MeasurableSet.univ hU, unitSquareVolume,
    ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod _ (L.kernel.measurable_coe hU).aemeasurable]
  have hae : ∀ᵐ x ∂(volume : Measure I).restrict S,
      ∫⁻ y, L.kernel (x, y) U = volume U :=
    ae_restrict_of_ae (L.ae_row_lintegral hU)
  rw [lintegral_congr_ae hae, setLIntegral_const, mul_comm]

theorem measure_yz (L : GHHSLatinon) {T U : Set I}
    (hT : MeasurableSet T) (hU : MeasurableSet U) :
    L.measure ((Set.univ ×ˢ T) ×ˢ U) = volume T * volume U := by
  rw [L.measure_rectangle MeasurableSet.univ hT hU, unitSquareVolume,
    ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod_symm _ (L.kernel.measurable_coe hU).aemeasurable]
  have hae : ∀ᵐ y ∂(volume : Measure I).restrict T,
      ∫⁻ x, L.kernel (x, y) U = volume U :=
    ae_restrict_of_ae (L.ae_col_lintegral hU)
  rw [lintegral_congr_ae hae, setLIntegral_const, mul_comm]

/-- **Kernel ⇒ measure.** A GHHS Latinon defines a Latinon measure `ν_K = λ² ⊗ K`
with the same order map. -/
def toLatinonMeasure (L : GHHSLatinon) : LatinonMeasure where
  measure := L.measure
  order := L.order
  order_preserving := L.order_measurePreserving
  xy_uniform _ _ hS hT := L.measure_xy hS hT
  xz_uniform _ _ hS hU := L.measure_xz hS hU
  yz_uniform _ _ hT hU := L.measure_yz hT hU

@[simp] theorem toLatinonMeasure_measure (L : GHHSLatinon) :
    L.toLatinonMeasure.measure = L.measure := rfl

@[simp] theorem toLatinonMeasure_order (L : GHHSLatinon) :
    L.toLatinonMeasure.order = L.order := rfl

end GHHSLatinon

end GHHSBridge
