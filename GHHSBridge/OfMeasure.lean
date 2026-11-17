/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GHHSBridge.ToMeasure
public import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# From Latinon measures to GHHS Latinons, and the round trips

For a Latinon measure `W`, the conditional symbol kernel `latinonSymbolKernel W`
(the disintegration of `W` over its `(x, y)` marginal) together with the order map
of `W` is a GHHS Latinon (Definition 3.5).

* The first marginal of every row and column measure is uniform because the order
  map preserves Lebesgue measure.
* The second marginal of the row measure at `x` is the row average
  `U ↦ ∫ K (x, y) (U) dy`. The uniform `(x, z)` marginal of `W` says that
  `λ ⊗ (row average) = λ ⊗ λ`, and uniqueness of disintegration gives that the row
  average is `λ` for almost every `x`. Columns are the same with the `(y, z)`
  marginal.

The round trips: `toLatinonMeasure ∘ ofLatinonMeasure` is the identity, and
`ofLatinonMeasure ∘ toLatinonMeasure` returns the same order map and a kernel that
agrees with the original one almost everywhere on `I × I`. This is the
identification part of Proposition 2.3 of the Latinon preprint, on the ground
space `I`.
-/

@[expose] public section

noncomputable section

namespace GHHSBridge

open MeasureTheory ProbabilityTheory LatinonEntropy
open scoped unitInterval ENNReal

variable {K : Kernel (I × I) I} {f : I → I}

/-! ### Row and column averages as kernels -/

/-- The row average `x ↦ ∫ K (x, y) dy`, as a kernel on `I`. -/
def rowAvg (K : Kernel (I × I) I) : Kernel I I :=
  K ∘ₖ (Kernel.deterministic id measurable_id ×ₖ Kernel.const I (volume : Measure I))

/-- The column average `y ↦ ∫ K (x, y) dx`, as a kernel on `I`. -/
def colAvg (K : Kernel (I × I) I) : Kernel I I :=
  K ∘ₖ (Kernel.const I (volume : Measure I) ×ₖ Kernel.deterministic id measurable_id)

instance [IsMarkovKernel K] : IsMarkovKernel (rowAvg K) := by
  unfold rowAvg; infer_instance

instance [IsMarkovKernel K] : IsMarkovKernel (colAvg K) := by
  unfold colAvg; infer_instance

theorem rowAvg_apply [IsMarkovKernel K] (x : I) {U : Set I} (hU : MeasurableSet U) :
    rowAvg K x U = ∫⁻ y, K (x, y) U := by
  unfold rowAvg
  rw [Kernel.comp_apply' _ _ _ hU, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, lintegral_prod _ (K.measurable_coe hU).aemeasurable]
  exact lintegral_dirac (id x) (fun a => ∫⁻ y, K (a, y) U)

theorem colAvg_apply [IsMarkovKernel K] (y : I) {U : Set I} (hU : MeasurableSet U) :
    colAvg K y U = ∫⁻ x, K (x, y) U := by
  unfold colAvg
  rw [Kernel.comp_apply' _ _ _ hU, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, lintegral_prod_symm _ (K.measurable_coe hU).aemeasurable]
  exact lintegral_dirac (id y) (fun b => ∫⁻ x, K (x, b) U)

/-! ### Rectangles of `λ² ⊗ K` with a full side -/

theorem compProd_rect_xz [IsMarkovKernel K] {S U : Set I}
    (hS : MeasurableSet S) (hU : MeasurableSet U) :
    (unitSquareVolume ⊗ₘ K) ((S ×ˢ Set.univ) ×ˢ U) = ∫⁻ x in S, ∫⁻ y, K (x, y) U := by
  rw [Measure.compProd_apply_prod (hS.prod MeasurableSet.univ) hU, unitSquareVolume,
    ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod _ (K.measurable_coe hU).aemeasurable]

theorem compProd_rect_yz [IsMarkovKernel K] {T U : Set I}
    (hT : MeasurableSet T) (hU : MeasurableSet U) :
    (unitSquareVolume ⊗ₘ K) ((Set.univ ×ˢ T) ×ˢ U) = ∫⁻ y in T, ∫⁻ x, K (x, y) U := by
  rw [Measure.compProd_apply_prod (MeasurableSet.univ.prod hT) hU, unitSquareVolume,
    ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod_symm _ (K.measurable_coe hU).aemeasurable]

/-! ### The first marginals -/

theorem rowMeasure_map_fst [IsMarkovKernel K] (hf : MeasurePreserving f volume volume)
    (x : I) : (rowMeasure K f x).map Prod.fst = volume := by
  have hfm := hf.measurable
  unfold rowMeasure
  rw [Measure.map_map measurable_fst (by fun_prop)]
  have hcomp : (Prod.fst ∘ fun p : I × I => (f p.1, p.2)) = f ∘ Prod.fst := rfl
  have hfst : ((volume : Measure I) ⊗ₘ K.comap (fun y => (x, y)) (by fun_prop)).map
      Prod.fst = volume := Measure.fst_compProd _ _
  rw [hcomp, ← Measure.map_map hf.measurable measurable_fst, hfst, hf.map_eq]

theorem colMeasure_map_fst [IsMarkovKernel K] (hf : MeasurePreserving f volume volume)
    (y : I) : (colMeasure K f y).map Prod.fst = volume := by
  have hfm := hf.measurable
  unfold colMeasure
  rw [Measure.map_map measurable_fst (by fun_prop)]
  have hcomp : (Prod.fst ∘ fun p : I × I => (f p.1, p.2)) = f ∘ Prod.fst := rfl
  have hfst : ((volume : Measure I) ⊗ₘ K.comap (fun x => (x, y)) (by fun_prop)).map
      Prod.fst = volume := Measure.fst_compProd _ _
  rw [hcomp, ← Measure.map_map hf.measurable measurable_fst, hfst, hf.map_eq]

/-! ### Uniqueness of disintegration: averages are Lebesgue almost everywhere -/

/-- If `λ ⊗ κ = λ ⊗ λ`, then `κ x = λ` for almost every `x`. -/
theorem ae_eq_volume_of_compProd_eq (κ : Kernel I I) [IsFiniteKernel κ]
    (h : (volume : Measure I).prod volume = volume ⊗ₘ κ) :
    ∀ᵐ x ∂(volume : Measure I), κ x = volume := by
  have hfst : ((volume : Measure I).prod (volume : Measure I)).fst = volume :=
    Measure.fst_prod
  have e1 := eq_condKernel_of_measure_eq_compProd (ρ := (volume : Measure I).prod volume)
    κ (by rw [hfst]; exact h)
  have e2 := eq_condKernel_of_measure_eq_compProd (ρ := (volume : Measure I).prod volume)
    (Kernel.const I (volume : Measure I)) (by rw [hfst, Measure.compProd_const])
  rw [hfst] at e1 e2
  filter_upwards [e1, e2] with x h1 h2
  rw [h1, ← h2, Kernel.const_apply]

theorem ae_rowAvg_eq_volume [IsMarkovKernel K]
    (hxz : ∀ S U : Set I, MeasurableSet S → MeasurableSet U →
      (unitSquareVolume ⊗ₘ K) ((S ×ˢ Set.univ) ×ˢ U) = volume S * volume U) :
    ∀ᵐ x ∂(volume : Measure I), rowAvg K x = volume := by
  refine ae_eq_volume_of_compProd_eq (rowAvg K) (Measure.prod_eq fun S U hS hU => ?_)
  rw [Measure.compProd_apply_prod hS hU, lintegral_congr fun x => rowAvg_apply x hU,
    ← compProd_rect_xz hS hU, hxz S U hS hU]

theorem ae_colAvg_eq_volume [IsMarkovKernel K]
    (hyz : ∀ T U : Set I, MeasurableSet T → MeasurableSet U →
      (unitSquareVolume ⊗ₘ K) ((Set.univ ×ˢ T) ×ˢ U) = volume T * volume U) :
    ∀ᵐ y ∂(volume : Measure I), colAvg K y = volume := by
  refine ae_eq_volume_of_compProd_eq (colAvg K) (Measure.prod_eq fun T U hT hU => ?_)
  rw [Measure.compProd_apply_prod hT hU, lintegral_congr fun y => colAvg_apply y hU,
    ← compProd_rect_yz hT hU, hyz T U hT hU]

/-! ### The permuton conditions -/

theorem ae_row_permuton_of_xz [IsMarkovKernel K] (hf : MeasurePreserving f volume volume)
    (hxz : ∀ S U : Set I, MeasurableSet S → MeasurableSet U →
      (unitSquareVolume ⊗ₘ K) ((S ×ˢ Set.univ) ×ˢ U) = volume S * volume U) :
    ∀ᵐ x ∂(volume : Measure I), IsPermuton (rowMeasure K f x) := by
  filter_upwards [ae_rowAvg_eq_volume hxz] with x hx
  refine ⟨rowMeasure_map_fst hf x, Measure.ext fun U hU => ?_⟩
  rw [rowMeasure_map_snd_apply hf.measurable x hU, ← rowAvg_apply x hU, hx]

theorem ae_col_permuton_of_yz [IsMarkovKernel K] (hf : MeasurePreserving f volume volume)
    (hyz : ∀ T U : Set I, MeasurableSet T → MeasurableSet U →
      (unitSquareVolume ⊗ₘ K) ((Set.univ ×ˢ T) ×ˢ U) = volume T * volume U) :
    ∀ᵐ y ∂(volume : Measure I), IsPermuton (colMeasure K f y) := by
  filter_upwards [ae_colAvg_eq_volume hyz] with y hy
  refine ⟨colMeasure_map_fst hf y, Measure.ext fun U hU => ?_⟩
  rw [colMeasure_map_snd_apply hf.measurable y hU, ← colAvg_apply y hU, hy]

/-! ### Measure ⇒ kernel, and the round trips -/

/-- **Measure ⇒ kernel.** The conditional symbol kernel of a Latinon measure, with
its order map, is a GHHS Latinon. -/
def ofLatinonMeasure (W : LatinonMeasure) : GHHSLatinon where
  kernel := latinonSymbolKernel W
  isMarkov := inferInstance
  order := W.order
  order_measurePreserving := W.order_preserving
  row_permuton := ae_row_permuton_of_xz W.order_preserving fun S U hS hU => by
    rw [latinonSymbolKernel_reconstruct W]; exact W.xz_uniform S U hS hU
  col_permuton := ae_col_permuton_of_yz W.order_preserving fun T U hT hU => by
    rw [latinonSymbolKernel_reconstruct W]; exact W.yz_uniform T U hT hU

@[simp] theorem ofLatinonMeasure_kernel (W : LatinonMeasure) :
    (ofLatinonMeasure W).kernel = latinonSymbolKernel W := rfl

@[simp] theorem ofLatinonMeasure_order (W : LatinonMeasure) :
    (ofLatinonMeasure W).order = W.order := rfl

/-- Latinon measures are determined by their measure and order map. -/
theorem latinonMeasure_ext {W V : LatinonMeasure} (hm : W.measure = V.measure)
    (ho : W.order = V.order) : W = V := by
  cases W
  cases V
  cases hm
  cases ho
  rfl

/-- **Round trip 1.** Measure ⇒ kernel ⇒ measure is the identity. -/
theorem toLatinonMeasure_ofLatinonMeasure (W : LatinonMeasure) :
    (ofLatinonMeasure W).toLatinonMeasure = W :=
  latinonMeasure_ext (latinonSymbolKernel_reconstruct W) rfl

/-- **Round trip 2.** Kernel ⇒ measure ⇒ kernel returns the same order map and a
kernel equal to the original one almost everywhere on `I × I`. -/
theorem ofLatinonMeasure_toLatinonMeasure_kernel (L : GHHSLatinon) :
    ∀ᵐ p ∂unitSquareVolume, (ofLatinonMeasure L.toLatinonMeasure).kernel p = L.kernel p := by
  have hfst : L.measure.fst = unitSquareVolume := Measure.fst_compProd _ _
  have h := eq_condKernel_of_measure_eq_compProd (ρ := L.measure) L.kernel
    (by rw [hfst]; rfl)
  rw [hfst] at h
  filter_upwards [h] with p hp
  exact hp.symm

theorem ofLatinonMeasure_toLatinonMeasure_order (L : GHHSLatinon) :
    (ofLatinonMeasure L.toLatinonMeasure).order = L.order := rfl

/-- Two GHHS Latinons with the same order map and almost everywhere equal kernels
have the same measure `ν_K`. -/
theorem measure_eq_of_ae_kernel_eq {L L' : GHHSLatinon}
    (h : ∀ᵐ p ∂unitSquareVolume, L.kernel p = L'.kernel p) : L.measure = L'.measure :=
  Measure.compProd_congr h

end GHHSBridge
