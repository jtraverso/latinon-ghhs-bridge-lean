/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LatinonConditionalSymbols
public import LatinonCutDistance
public import LatinonRelativeEntropy

/-!
# GHHS Latinons on the ground space `I`

This file states, on the standard ground space `I = [0, 1]`, the kernel
representation of Latinons from Garbe, Hancock, Hladký and Sharifzadeh,
*Limits of Latin squares*, Discrete Analysis 2023:8 (GHHS), Definition 3.5.

* A distribution-valued bigraphon is a kernel `K : Kernel (I × I) I`, required to be
  Markov (each `K (x, y)` is a probability measure on the symbol interval).
* The order map `f : I → I` preserves Lebesgue measure.
* Condition (i): for almost every row `x`, the measure `μ¹ₓ` on `I × I` with
  `μ¹ₓ (S × T) = ∫_{y ∈ f⁻¹(S)} K (x, y) (T) dy` is a permuton.
  It is realised here as the image of `λ ⊗ K (x, ·)` under `(y, z) ↦ (f y, z)`,
  which has these values on rectangles.
* Condition (ii): the same for almost every column `y`.

`GHHSLatinon.measure` is kernel integration `ν_K = λ² ⊗ K` (formula (2.9) of the
Latinon preprint). The identification with `LatinonEntropy.LatinonMeasure`, and the
preservation of distance, pattern densities and signed entropy (Proposition 2.3 of the
Latinon preprint), are the subject of the later files of this project.
-/

@[expose] public section

noncomputable section

namespace GHHSBridge

open MeasureTheory ProbabilityTheory LatinonEntropy
open scoped unitInterval ENNReal

/-- A permuton: a measure on `I × I` whose two marginals are Lebesgue measure. -/
def IsPermuton (μ : Measure (I × I)) : Prop :=
  μ.map Prod.fst = volume ∧ μ.map Prod.snd = volume

/-- The row measure of GHHS Definition 3.5(i) at the row `x`. -/
def rowMeasure (K : Kernel (I × I) I) (f : I → I) (x : I) : Measure (I × I) :=
  ((volume : Measure I) ⊗ₘ K.comap (fun y => (x, y)) (by fun_prop)).map
    (fun p => (f p.1, p.2))

/-- The column measure of GHHS Definition 3.5(ii) at the column `y`. -/
def colMeasure (K : Kernel (I × I) I) (f : I → I) (y : I) : Measure (I × I) :=
  ((volume : Measure I) ⊗ₘ K.comap (fun x => (x, y)) (by fun_prop)).map
    (fun p => (f p.1, p.2))

/-- **GHHS Definition 3.5**, on the ground space `I`: a Latinon is a distribution-valued
bigraphon with a measure-preserving order map whose row and column measures are
permutons almost everywhere. -/
structure GHHSLatinon where
  /-- The distribution-valued bigraphon `W`. -/
  kernel : Kernel (I × I) I
  isMarkov : IsMarkovKernel kernel
  /-- The order map `f`. -/
  order : I → I
  order_measurePreserving : MeasurePreserving order volume volume
  row_permuton : ∀ᵐ x ∂(volume : Measure I), IsPermuton (rowMeasure kernel order x)
  col_permuton : ∀ᵐ y ∂(volume : Measure I), IsPermuton (colMeasure kernel order y)

attribute [instance] GHHSLatinon.isMarkov

namespace GHHSLatinon

/-- Kernel integration: `ν_K = λ² ⊗ K`, a measure on `(I × I) × I`. -/
def measure (L : GHHSLatinon) : Measure LatinonPoint :=
  unitSquareVolume ⊗ₘ L.kernel

instance (L : GHHSLatinon) : IsProbabilityMeasure L.measure := by
  unfold measure
  infer_instance

/-- On rectangles, `ν_K (S × T × U) = ∫_{S × T} K (x, y) (U)`. -/
theorem measure_rectangle (L : GHHSLatinon) {S T U : Set I}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U) :
    L.measure ((S ×ˢ T) ×ˢ U) = ∫⁻ p in S ×ˢ T, L.kernel p U ∂unitSquareVolume := by
  unfold measure
  rw [Measure.compProd_apply_prod (hS.prod hT) hU]

end GHHSLatinon

end GHHSBridge
