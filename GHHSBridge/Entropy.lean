/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GHHSBridge.Patterns
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# The GHHS entropy in kernel terms

GHHS, Section 12.2: if `W(x, y)` has a density `g(x, y, ·)` with respect to Lebesgue
measure for almost every `(x, y)`, then `Ent(L) = ∫∫∫ g log g`. With this sign the
predicted count `(e^{Ent} n/e²)^{n²}` exceeds the number of Latin squares; the Latinon
preprint uses `Ent = −∫∫∫ g log g`, and so does this file. The printed sign is not
formalized.

* `toReal_klDiv_eq_integral_mul_log`: for a probability measure `μ ≪ λ` on `I`,
  `KL(μ ‖ λ) = ∫ g log g` with `g = dμ/dλ` (as real numbers; both sides are `∞` and the
  junk value `0` respectively when `g log g` is not integrable).
* `ghhsRate L = ∫⁻ KL(K(x, y) ‖ λ) dx dy`, with values in `[0, ∞]`. It is GHHS's
  `∫∫∫ g log g` when the kernel has densities, and `∞` when it does not.
* `ghhsEntropy L = −ghhsRate L`, in `EReal`.

The main result, `ghhsEntropy_eq`, is the entropy part (2.2) of Proposition 2.3 of the
Latinon preprint: `ghhsEntropy L = latinonEntropy L.toLatinonMeasure`, including the
case `−∞`.

Its proof uses the conditional chain rule
`KL(μ ⊗ κ ‖ μ ⊗ η) = ∫⁻ KL(κ a ‖ η a) dμ(a)` (`klDiv_compProd_right_eq_lintegral`),
which Mathlib lists as a TODO in `InformationTheory.KullbackLeibler.ChainRule`. It is
proved here for finite `μ`, Markov kernels and countably generated spaces, in
lower-integral form, so no integrability hypothesis is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory LatinonEntropy
open scoped unitInterval ENNReal

namespace GHHSBridge

/-! ### Conditional chain rule for the Kullback–Leibler divergence -/

section ChainRule

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace.CountableOrCountablyGenerated α β]

/-- **Conditional chain rule.** `KL(μ ⊗ κ ‖ μ ⊗ η) = ∫⁻ KL(κ a ‖ η a) dμ(a)`. -/
theorem klDiv_compProd_right_eq_lintegral (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  by_cases h : ∀ᵐ a ∂μ, κ a ≪ η a
  · have hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η := Measure.absolutelyContinuous_compProd_right_iff.2 h
    have hmeas : Measurable fun p : α × β =>
        ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal) :=
      ENNReal.measurable_ofReal.comp
        (measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal)
    rw [klDiv_eq_lintegral_klFun_of_ac hac,
      lintegral_congr_ae
        (g := fun p : α × β => ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal))
        ((rnDeriv_measure_compProd_right μ κ η).mono fun p hp => by simp only [hp]),
      Measure.lintegral_compProd hmeas]
    refine lintegral_congr_ae ?_
    filter_upwards [h] with a ha
    rw [klDiv_eq_lintegral_klFun_of_ac ha]
    refine lintegral_congr_ae ?_
    filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
    rw [hb]
  · have hnot : ¬ μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
      fun hac => h (Measure.absolutelyContinuous_compProd_right_iff.1 hac)
    rw [klDiv_of_not_ac hnot]
    set S : Set α := {a | κ a ≪ η a}ᶜ with hS
    have hSm : MeasurableSet S := (Kernel.measurableSet_absolutelyContinuous κ η).compl
    have hS0 : μ S ≠ 0 := by
      intro h0
      exact h (ae_iff.2 h0)
    symm
    rw [eq_top_iff]
    calc (∞ : ℝ≥0∞) = ∞ * μ S := (ENNReal.top_mul hS0).symm
      _ = ∫⁻ a, S.indicator (fun _ => ∞) a ∂μ := (lintegral_indicator_const hSm ∞).symm
      _ ≤ ∫⁻ a, klDiv (κ a) (η a) ∂μ :=
        lintegral_mono (Set.indicator_le fun a ha => (klDiv_of_not_ac ha).ge)

end ChainRule

/-- GHHS's integrand: for a probability measure `μ ≪ λ` on `I`, the divergence is
`∫ g log g` with `g = dμ/dλ`. -/
theorem toReal_klDiv_eq_integral_mul_log (μ : Measure I) [IsProbabilityMeasure μ]
    (h : μ ≪ volume) :
    (klDiv μ volume).toReal =
      ∫ z, (μ.rnDeriv volume z).toReal * Real.log (μ.rnDeriv volume z).toReal := by
  rw [toReal_klDiv_of_measure_eq h (by rw [measure_univ, measure_univ]),
    integral_rnDeriv_mul_log h]

/-! ### The GHHS entropy and the bridge -/

/-- `∫∫ KL(K(x, y) ‖ λ) dx dy ∈ [0, ∞]`: GHHS's `∫∫∫ g log g`, extended by `∞`. -/
def ghhsRate (L : GHHSLatinon) : ℝ≥0∞ :=
  ∫⁻ p, klDiv (L.kernel p) volume ∂unitSquareVolume

/-- **GHHS entropy** with the sign of the Latinon preprint: `Ent(L) = −∫∫∫ g log g`,
equal to `−∞` when the kernel has no densities or `g log g` is not integrable. -/
def ghhsEntropy (L : GHHSLatinon) : EReal := -(ghhsRate L : EReal)

theorem uniform_measure_eq_compProd :
    uniformLatinonMeasure.measure = unitSquareVolume ⊗ₘ Kernel.const (I × I) volume :=
  Measure.compProd_const.symm

/-- **Entropy part of Proposition 2.3**, unsigned form. -/
theorem ghhsRate_eq (L : GHHSLatinon) : ghhsRate L = latinonRate L.toLatinonMeasure := by
  unfold ghhsRate latinonRate
  rw [GHHSLatinon.toLatinonMeasure_measure, GHHSLatinon.measure, uniform_measure_eq_compProd,
    klDiv_compProd_right_eq_lintegral]
  simp only [Kernel.const_apply]

/-- **Entropy part of Proposition 2.3.** The GHHS entropy of a GHHS Latinon equals the
entropy of its measure representation, including the value `−∞`. -/
theorem ghhsEntropy_eq (L : GHHSLatinon) : ghhsEntropy L = latinonEntropy L.toLatinonMeasure := by
  simp only [ghhsEntropy, latinonEntropy, ghhsRate_eq]

/-- The same statement read from the measure side. -/
theorem latinonEntropy_eq_ghhs (W : LatinonMeasure) :
    latinonEntropy W = ghhsEntropy (ofLatinonMeasure W) := by
  rw [ghhsEntropy_eq, toLatinonMeasure_ofLatinonMeasure]

/-- The GHHS entropy does not see null modifications of the kernel. -/
theorem ghhsEntropy_congr_ae {L L' : GHHSLatinon}
    (hK : ∀ᵐ p ∂unitSquareVolume, L.kernel p = L'.kernel p) (ho : L.order = L'.order) :
    ghhsEntropy L = ghhsEntropy L' := by
  rw [ghhsEntropy_eq, ghhsEntropy_eq, toLatinonMeasure_eq_of_ae hK ho]

end GHHSBridge
