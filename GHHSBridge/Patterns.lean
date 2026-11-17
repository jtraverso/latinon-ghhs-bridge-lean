/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GHHSBridge.Distance
public import LatinonPatternSampling

/-!
# GHHS pattern densities in kernel terms

GHHS Definition 3.7: for a Latinon `(W, f)` and a pattern `A ∈ R(k, ℓ)`,
`t(A, (W, f)) = k! ℓ! ∫_{x ∈ Ω^k_{<f}} ∫_{y ∈ Ω^ℓ_{<f}} (⊗_{(i,j)} W(x_i, y_j))(R_A([0,1])) dy dx`.

On `I`, with patterns encoded as `LatinOrderPattern k l` and `R_A([0,1])` as
`unitOrderPatternRealizations` (both from the Latinon build), this is
`ghhsPatternDensity`. The ordered domain is `Ω^k_{<f} × Ω^ℓ_{<f}` (`orderedConfigs`), and
the product measure of the cells is `finiteIndependentKernel` of the cell kernels.

`ghhsPatternDensity_eq` proves that it equals `latinonPatternDensity` of the measure
representation. The two definitions differ only in the kernel used: GHHS integrate the
given kernel `W`, the Latinon preprint integrates the disintegration of `ν_W`. These
agree almost everywhere on `I × I` (`OfMeasure`), and every cell `(x_i, y_j)` of a
uniform configuration is uniform on `I × I`, so the integrands agree almost everywhere.
This is the pattern part of Proposition 2.3 of the Latinon preprint.
-/

@[expose] public section

noncomputable section

namespace GHHSBridge

open MeasureTheory ProbabilityTheory LatinonEntropy
open scoped unitInterval ENNReal

/-- The law of the cell `(x_i, y_j)` of a configuration under a kernel `K`. -/
def patternCellKernel (K : Kernel (I × I) I) (k l : ℕ) (a : Fin k × Fin l) :
    Kernel (LatinonPatternConfig k l) I :=
  K.comap (fun c => (c.1 a.1, c.2 a.2))
    (((measurable_pi_apply a.1).comp measurable_fst).prodMk
      ((measurable_pi_apply a.2).comp measurable_snd))

instance (K : Kernel (I × I) I) [IsMarkovKernel K] (k l : ℕ) (a : Fin k × Fin l) :
    IsMarkovKernel (patternCellKernel K k l a) := by
  unfold patternCellKernel
  infer_instance

/-- `⊗_{(i,j)} K(x_i, y_j)`: independent sampling of all cells. -/
def patternSymbolKernel (K : Kernel (I × I) I) [IsMarkovKernel K] (k l : ℕ) :
    Kernel (LatinonPatternConfig k l) ((Fin k × Fin l) → I) :=
  finiteIndependentKernel (patternCellKernel K k l)

/-- `Ω^k_{<f} × Ω^ℓ_{<f}`: configurations increasingly ordered according to `<_f`. -/
def orderedConfigs (f : I → I) (k l : ℕ) : Set (LatinonPatternConfig k l) :=
  {c | StrictMono (f ∘ c.1) ∧ StrictMono (f ∘ c.2)}

/-- **GHHS Definition 3.7**, on the ground space `I`. -/
def ghhsPatternDensity {k l : ℕ} (L : GHHSLatinon) (P : LatinOrderPattern k l) : ℝ :=
  ((k.factorial * l.factorial : ℕ) : ℝ) *
    ∫ c in orderedConfigs L.order k l,
      (patternSymbolKernel L.kernel k l c).real (unitOrderPatternRealizations P)
        ∂latinonPatternConfigLaw k l

/-- Kernels equal almost everywhere on `I × I` give cell products equal almost
everywhere on configurations. -/
theorem ae_patternSymbolKernel_eq {K K' : Kernel (I × I) I} [IsMarkovKernel K]
    [IsMarkovKernel K'] (h : ∀ᵐ p ∂unitSquareVolume, K p = K' p) (k l : ℕ) :
    ∀ᵐ c ∂latinonPatternConfigLaw k l,
      patternSymbolKernel K k l c = patternSymbolKernel K' k l c := by
  have hcell : ∀ a : Fin k × Fin l, ∀ᵐ c ∂latinonPatternConfigLaw k l,
      K (c.1 a.1, c.2 a.2) = K' (c.1 a.1, c.2 a.2) := by
    intro a
    have hmp : MeasurePreserving (fun c : LatinonPatternConfig k l => (c.1 a.1, c.2 a.2))
        (latinonPatternConfigLaw k l) unitSquareVolume :=
      (measurePreserving_eval (fun _ : Fin k => (volume : Measure I)) a.1).prod
        (measurePreserving_eval (fun _ : Fin l => (volume : Measure I)) a.2)
    exact hmp.quasiMeasurePreserving.ae h
  filter_upwards [ae_all_iff.2 hcell] with c hc
  simp only [patternSymbolKernel, finiteIndependentKernel_apply, patternCellKernel,
    Kernel.comap_apply, hc]

/-- **Pattern part of Proposition 2.3.** GHHS pattern densities of a GHHS Latinon equal
the pattern densities of its measure representation. -/
theorem ghhsPatternDensity_eq {k l : ℕ} (L : GHHSLatinon) (P : LatinOrderPattern k l) :
    ghhsPatternDensity L P = latinonPatternDensity L.toLatinonMeasure P := by
  rw [latinonPatternDensity_eq_setIntegral]
  unfold ghhsPatternDensity
  congr 1
  have hK : ∀ᵐ p ∂unitSquareVolume,
      L.kernel p = latinonSymbolKernel L.toLatinonMeasure p :=
    (ofLatinonMeasure_toLatinonMeasure_kernel L).mono fun p hp => hp.symm
  refine setIntegral_congr_ae (measurableSet_orderedLatinonPatternConfigs L.toLatinonMeasure k l) ?_
  filter_upwards [ae_patternSymbolKernel_eq hK k l] with c hc _
  exact congrArg (fun μ : Measure ((Fin k × Fin l) → I) =>
    μ.real (unitOrderPatternRealizations P)) hc

/-- The same statement read from the measure side. -/
theorem latinonPatternDensity_eq_ghhs {k l : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) :
    latinonPatternDensity W P = ghhsPatternDensity (ofLatinonMeasure W) P := by
  rw [ghhsPatternDensity_eq, toLatinonMeasure_ofLatinonMeasure]

/-- Pattern densities do not see null modifications of the kernel. -/
theorem ghhsPatternDensity_congr_ae {k l : ℕ} {L L' : GHHSLatinon}
    (hK : ∀ᵐ p ∂unitSquareVolume, L.kernel p = L'.kernel p) (ho : L.order = L'.order)
    (P : LatinOrderPattern k l) :
    ghhsPatternDensity L P = ghhsPatternDensity L' P := by
  rw [ghhsPatternDensity_eq, ghhsPatternDensity_eq, toLatinonMeasure_eq_of_ae hK ho]

end GHHSBridge
