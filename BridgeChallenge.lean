/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. Released under Apache-2.0.
-/
module
public import Mathlib

/-!
# The kernel and measure representations of Latinons agree

This statement interface uses only Mathlib. It states, on the ground space `I = [0, 1]`,
the Latinon model of Garbe, Hancock, Hladký and Sharifzadeh (GHHS, *Limits of Latin squares*,
Discrete Analysis 2023:8) by kernels, and the measure model of the Latinon preprint
(*Entropy and large deviations for Latin squares*, preprint 1.0). Every definition is copied
from the proved development with the same name and value.

The principal claims are:

* the two descriptions define the same Latinons (`toLatinonMeasure_ofLatinonMeasure`,
  `ofLatinonMeasure_toLatinonMeasure_kernel`);
* they have the same cut distance (`ghhsCutDistance_eq`), pattern densities
  (`ghhsPatternDensity_eq`) and entropy (`ghhsEntropy_eq`), the last through the conditional
  chain rule for relative entropy (`klDiv_compProd_right_eq_lintegral`);
* GHHS Conjecture 12.4 in GHHS's own terms (`ghhsEntSup_eq`, `ghhsConjecture_12_4`,
  `ghhsConjecture_12_4_bot`, `ghhsConjecture_12_4_bot'`), with entropy taken as the negative of
  relative entropy; the sign printed in GHHS Section 12.2 is not formalized.

The marginal identities of the kernel integration and a few certificates that Lean generates
inside definitions are compared by their statements; they are named explicitly where Lean would
otherwise reuse an identical certificate generated earlier in this single file.
-/

@[expose] public section
noncomputable section
namespace LatinonEntropy
open MeasureTheory ProbabilityTheory Finset
open scoped Classical ENNReal unitInterval

/-- Rows, columns and symbols in the unit interval. -/
abbrev LatinonPoint := (I × I) × I

/-- A cube measure with uniform pair marginals and one measure-preserving order map. -/
structure LatinonMeasure where
  measure : Measure LatinonPoint
  order : I → I
  order_preserving : MeasurePreserving order volume volume
  xy_uniform : ∀ (S T : Set I), MeasurableSet S → MeasurableSet T →
    measure ((S ×ˢ T) ×ˢ Set.univ) = volume S * volume T
  xz_uniform : ∀ (S U : Set I), MeasurableSet S → MeasurableSet U →
    measure ((S ×ˢ Set.univ) ×ˢ U) = volume S * volume U
  yz_uniform : ∀ (T U : Set I), MeasurableSet T → MeasurableSet U →
    measure ((Set.univ ×ˢ T) ×ˢ U) = volume T * volume U

instance instIsProbabilityMeasureLatinonPointMeasure (W : LatinonMeasure) : IsProbabilityMeasure W.measure where
  measure_univ := by
    have h := W.xy_uniform Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simpa only [Set.univ_prod_univ,measure_univ,mul_one] using h

/-- The identity order of the uniform Latinon preserves Lebesgue measure. -/
theorem uniformLatinonMeasure_order_preserving : MeasurePreserving (id : I → I) volume volume :=
  MeasurePreserving.id volume

/-- Row-column marginal of the uniform cube measure. -/
theorem uniformLatinonMeasure_xy_uniform : ∀ (S T : Set I), MeasurableSet S → MeasurableSet T →
    @DFunLike.coe (Measure LatinonPoint) (Set LatinonPoint) (fun _ => ENNReal) _
      (((volume : Measure I).prod volume).prod volume) ((S ×ˢ T) ×ˢ Set.univ) =
      volume S * volume T := by
  intro S T _ _
  simp only [Measure.prod_prod,measure_univ,mul_one]

/-- Row-symbol marginal of the uniform cube measure. -/
theorem uniformLatinonMeasure_xz_uniform : ∀ (S U : Set I), MeasurableSet S → MeasurableSet U →
    @DFunLike.coe (Measure LatinonPoint) (Set LatinonPoint) (fun _ => ENNReal) _
      (((volume : Measure I).prod volume).prod volume) ((S ×ˢ Set.univ) ×ˢ U) =
      volume S * volume U := by
  intro S U _ _
  simp only [Measure.prod_prod,measure_univ,mul_one]

/-- Column-symbol marginal of the uniform cube measure. -/
theorem uniformLatinonMeasure_yz_uniform : ∀ (T U : Set I), MeasurableSet T → MeasurableSet U →
    @DFunLike.coe (Measure LatinonPoint) (Set LatinonPoint) (fun _ => ENNReal) _
      (((volume : Measure I).prod volume).prod volume) ((Set.univ ×ˢ T) ×ˢ U) =
      volume T * volume U := by
  intro T U _ _
  simp only [Measure.prod_prod,measure_univ,one_mul]

/-- Uniform cube measure with identity order. -/
def uniformLatinonMeasure : LatinonMeasure where
  measure := ((volume : Measure I).prod volume).prod volume
  order := id
  order_preserving := uniformLatinonMeasure_order_preserving
  xy_uniform := uniformLatinonMeasure_xy_uniform
  xz_uniform := uniformLatinonMeasure_xz_uniform
  yz_uniform := uniformLatinonMeasure_yz_uniform

/-- A measurable, measure-preserving bijection of the unit interval. -/
structure LatinonRelabel where
  equiv : I ≃ᵐ I
  preserves : MeasurePreserving equiv volume volume

instance instCoeFunLatinonRelabelForallElemRealUnitInterval : CoeFun LatinonRelabel (fun _ => I → I) := ⟨fun e => e.equiv⟩

namespace LatinonRelabel

/-- Inverse measurable relabeling. -/
def symm (e : LatinonRelabel) : LatinonRelabel :=
  ⟨e.equiv.symm,MeasurePreserving.symm e.equiv e.preserves⟩

/-- A relabeling is measurable. -/
theorem measurable (e : LatinonRelabel) : Measurable e := e.equiv.measurable

end LatinonRelabel

/-- Inverse row/column coordinate map; symbols retain their order. -/
def inverseCoordinateRelabel (e f : LatinonRelabel) (p : LatinonPoint) : LatinonPoint :=
  ((e.symm p.1.1,f.symm p.1.2),p.2)

/-- Pushforward along the inverse coordinate relabeling. -/
def relabelLatinonMeasure (mu : Measure LatinonPoint) (e f : LatinonRelabel) : Measure LatinonPoint :=
  mu.map (inverseCoordinateRelabel e f)

/-- Measurable row and column test sets. -/
structure LatinonRectangle where
  rows : Set I
  cols : Set I
  rows_measurable : MeasurableSet rows
  cols_measurable : MeasurableSet cols

/-- A measurable rectangle together with a measurable symbol interval. -/
structure LatinonBox extends LatinonRectangle where
  symbols : Set I
  symbols_measurable : MeasurableSet symbols
  symbols_interval : Set.OrdConnected symbols

/-- The corresponding product test set in the cube. -/
def LatinonBox.carrier (B : LatinonBox) : Set LatinonPoint := (B.rows ×ˢ B.cols) ×ˢ B.symbols

/-- Supremum over the specified cut tests. -/
def cutValueSup {α : Type*} (F : α → ℝ) : ℝ := sSup (Set.range F)

/-- Distribution cut norm over row/column sets and symbol intervals. -/
def measureCut (mu nu : Measure LatinonPoint) : ℝ :=
  cutValueSup (fun B : LatinonBox => |mu.real B.carrier-nu.real B.carrier|)

/-- Strict order relation induced by the order map. -/
def orderRelation (f : I → I) : Set (I × I) := {p | f p.1 < f p.2}

/-- Order mass tested on a measurable rectangle. -/
def orderBox (f : I → I) (R : LatinonRectangle) : ℝ :=
  ((volume : Measure I).prod volume).real ((R.rows ×ˢ R.cols) ∩ orderRelation f)

/-- Cut norm of the difference of two order relations. -/
def orderCut (f g : I → I) : ℝ :=
  cutValueSup (fun R : LatinonRectangle => |orderBox f R-orderBox g R|)

/-- Two order terms plus the distribution cut term. -/
def latinonAlignmentCost (W V : LatinonMeasure) (e f : LatinonRelabel) : ℝ :=
  orderCut W.order (V.order ∘ e)+orderCut W.order (V.order ∘ f)+
    measureCut W.measure (relabelLatinonMeasure V.measure e f)

/-- Infimum of alignment costs over independent row/column bijections: the distance of the
Latinon preprint between measure Latinons. -/
def latinonCutDistance (W V : LatinonMeasure) : ℝ :=
  sInf (Set.range (fun p : LatinonRelabel × LatinonRelabel => latinonAlignmentCost W V p.1 p.2))

/-- Lebesgue measure on the unit square of rows and columns. -/
abbrev unitSquareVolume : Measure (I × I) := (volume : Measure I).prod volume

/-- Extended KL divergence from uniform cube volume, including singular measures. -/
def latinonRate (W : LatinonMeasure) : ℝ≥0∞ :=
  InformationTheory.klDiv W.measure uniformLatinonMeasure.measure

/-- Entropy of a measure Latinon: minus the extended KL divergence, with value `-∞` allowed. -/
def latinonEntropy (W : LatinonMeasure) : EReal := -(latinonRate W : EReal)

/-- An array whose rows and columns are bijections. -/
def LatinArray (n : ℕ) := {L : Fin n → Fin n → Fin n //
  (∀ x, Function.Bijective (L x)) ∧ (∀ y, Function.Bijective (fun x => L x y))}

instance latinArrayFintype (n : ℕ) : Fintype (LatinArray n) := by
  unfold LatinArray
  infer_instance

section
local instance instFintypeLatinArray_latinSquareNormalization (n : ℕ) : Fintype (LatinArray n) := by
  unfold LatinArray
  infer_instance

/-- The finite set of all labeled Latin squares of a given order. -/
def allLatinSquares (n : ℕ) : Finset (LatinArray n) := univ

end

/-- A rectangular order pattern uses each strict rank once. -/
abbrev LatinOrderPattern (k l : ℕ) := (Fin k × Fin l) ≃ Fin (k*l)

/-- Vectors realizing all strict rank comparisons of the pattern. -/
def orderPatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) :
    Set ((Fin k × Fin l) → ℝ) :=
  {v | ∀ a b, P a < P b → v a < v b}

/-- Standard Borel certificate used by `latinonSymbolKernel`. In the source module Lean
generates it from the first instance argument of `condKernel`; here it is named explicitly,
with the statement computed through the same unification as `condKernel`'s binders, and
used as the instance. Compared by its statement. -/
theorem latinonSymbolKernel._proof_1 :
    type_of% ((fun {α Ω : Type} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
      (_ρ : Measure (α × Ω)) (h : StandardBorelSpace Ω) => h)
      uniformLatinonMeasure.measure inferInstance) :=
  inferInstance

section
attribute [local instance 2000] latinonSymbolKernel._proof_1

/-- Canonical conditional symbol kernel obtained by disintegration of the cube measure. -/
def latinonSymbolKernel (W : LatinonMeasure) : Kernel (I × I) I := W.measure.condKernel

end

instance latinonSymbolKernel_markov (W : LatinonMeasure) : IsMarkovKernel (latinonSymbolKernel W) := by
  unfold latinonSymbolKernel
  infer_instance

/-- Finite conditional product of Markov kernels. -/
def finiteIndependentKernel {A J : Type*} [MeasurableSpace A] [Fintype J]
    {B : J → Type*} [∀ j, MeasurableSpace (B j)]
    (K : ∀ j, Kernel A (B j)) [∀ j, IsMarkovKernel (K j)] : Kernel A (∀ j, B j) where
  toFun a := Measure.pi (fun j => K j a)
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_pi.symm isPiSystem_pi
    rintro _ ⟨S,hS,rfl⟩
    have hSm : ∀ j, MeasurableSet (S j) := fun j => hS j (Set.mem_univ j)
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_fun_prod _ (fun j _ => (K j).measurable_coe (hSm j))

/-- Sampled row and column coordinates. -/
abbrev LatinonPatternConfig (k l : ℕ) := (Fin k → I) × (Fin l → I)

/-- Independent uniform row and column samples. -/
def latinonPatternConfigLaw (k l : ℕ) : Measure (LatinonPatternConfig k l) :=
  (Measure.pi (fun _ : Fin k => (volume : Measure I))).prod
    (Measure.pi (fun _ : Fin l => (volume : Measure I)))

/-- Configurations ordered by the common order map. -/
def orderedLatinonPatternConfigs (W : LatinonMeasure) (k l : ℕ) :
    Set (LatinonPatternConfig k l) :=
  {c | StrictMono (W.order ∘ c.1) ∧ StrictMono (W.order ∘ c.2)}

/-- Conditional symbol kernel for one sampled cell. -/
def latinonPatternCellKernel (W : LatinonMeasure) (k l : ℕ) (a : Fin k × Fin l) :
    Kernel (LatinonPatternConfig k l) I :=
  (latinonSymbolKernel W).comap (fun c => (c.1 a.1,c.2 a.2))
    (((measurable_pi_apply a.1).comp measurable_fst).prodMk
      ((measurable_pi_apply a.2).comp measurable_snd))

instance latinonPatternCellKernel_markov (W : LatinonMeasure) (k l : ℕ) (a : Fin k × Fin l) :
    IsMarkovKernel (latinonPatternCellKernel W k l a) := by
  unfold latinonPatternCellKernel
  infer_instance

/-- Conditional independent symbol samples over all cells. -/
def latinonPatternSymbolKernel (W : LatinonMeasure) (k l : ℕ) :
    Kernel (LatinonPatternConfig k l) ((Fin k × Fin l) → I) :=
  finiteIndependentKernel (latinonPatternCellKernel W k l)

/-- Strict pattern realizations with values in the unit interval. -/
def unitOrderPatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) :
    Set ((Fin k × Fin l) → I) :=
  (fun v a => (v a : ℝ)) ⁻¹' orderPatternRealizations P

/-- Joint coordinate and conditional-symbol law. -/
def latinonPatternSampleLaw (W : LatinonMeasure) (k l : ℕ) :
    Measure (LatinonPatternConfig k l × ((Fin k × Fin l) → I)) :=
  latinonPatternConfigLaw k l ⊗ₘ latinonPatternSymbolKernel W k l

/-- Ordered configurations whose sampled symbols realize the specified pattern. -/
def latinonPatternEvent {k l : ℕ} (W : LatinonMeasure) (P : LatinOrderPattern k l) :
    Set (LatinonPatternConfig k l × ((Fin k × Fin l) → I)) :=
  orderedLatinonPatternConfigs W k l ×ˢ unitOrderPatternRealizations P

/-- Factorial-normalized ordered-sampling probability: the pattern density of the Latinon
preprint. -/
def latinonPatternDensity {k l : ℕ} (W : LatinonMeasure) (P : LatinOrderPattern k l) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real (latinonPatternEvent W P)

/-- Vector of pattern densities of the actual Latinon. -/
def latinonPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (W : LatinonMeasure) : J → ℝ :=
  fun j => latinonPatternDensity W (P j)

/-- Finite row and column index selections. -/
abbrev FinitePatternConfig (n k l : ℕ) := (Fin k → Fin n) × (Fin l → Fin n)

/-- Increasing index selections realizing the strict order pattern. -/
def finiteMatrixPatternConfigs {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) :
    Set (FinitePatternConfig n k l) :=
  {c | StrictMono c.1 ∧ StrictMono c.2 ∧ ∀ a b, P a < P b →
    L.val (c.1 a.1) (c.2 a.2) < L.val (c.1 b.1) (c.2 b.2)}

/-- Finite set of those increasing index selections. -/
def finiteMatrixPatternFamily {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) :
    Finset (FinitePatternConfig n k l) := Finset.univ.filter (fun c => c ∈ finiteMatrixPatternConfigs L P)

/-- Finite count divided by the product of the two binomial coefficients. -/
def standardMatrixPatternDensity {n k l : ℕ} (L : LatinArray n)
    (P : LatinOrderPattern k l) : ℝ :=
  ((finiteMatrixPatternFamily L P).card : ℝ)/
    ((n.choose k : ℝ)*(n.choose l : ℝ))

/-- Infimum of extended KL divergence over the exact compatible Latinon fiber. -/
def latinonContractedRate {Y : Type*} (T : LatinonMeasure → Y) (z : Y) : ℝ≥0∞ :=
  ⨅ W : {W : LatinonMeasure // T W=z}, latinonRate W.1

/-- Disintegration: integrating the conditional symbol kernel against `λ²` recovers the cube
measure (auxiliary comparison). -/
theorem latinonSymbolKernel_reconstruct (W : LatinonMeasure) :
    unitSquareVolume ⊗ₘ latinonSymbolKernel W=W.measure := by
  sorry

end LatinonEntropy

namespace GHHSBridge
open MeasureTheory ProbabilityTheory LatinonEntropy
open scoped unitInterval ENNReal

/-- A permuton: a measure on `I × I` whose two marginals are Lebesgue measure. -/
def IsPermuton (μ : Measure (I × I)) : Prop :=
  μ.map Prod.fst = volume ∧ μ.map Prod.snd = volume

/-- The row measure of GHHS Definition 3.5(i) at the row `x`: the image of
`λ ⊗ K(x, ·)` under `(y, z) ↦ (f y, z)`. -/
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

/-- Uniform row–column marginal of `ν_K` (auxiliary comparison). -/
theorem measure_xy (L : GHHSLatinon) {S T : Set I}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    L.measure ((S ×ˢ T) ×ˢ Set.univ) = volume S * volume T := by
  sorry

/-- Uniform row–symbol marginal of `ν_K`, from the row permuton condition (auxiliary
comparison). -/
theorem measure_xz (L : GHHSLatinon) {S U : Set I}
    (hS : MeasurableSet S) (hU : MeasurableSet U) :
    L.measure ((S ×ˢ Set.univ) ×ˢ U) = volume S * volume U := by
  sorry

/-- Uniform column–symbol marginal of `ν_K`, from the column permuton condition (auxiliary
comparison). -/
theorem measure_yz (L : GHHSLatinon) {T U : Set I}
    (hT : MeasurableSet T) (hU : MeasurableSet U) :
    L.measure ((Set.univ ×ˢ T) ×ˢ U) = volume T * volume U := by
  sorry

/-- **Kernel ⇒ measure.** A GHHS Latinon defines a Latinon measure `ν_K = λ² ⊗ K`
with the same order map. -/
def toLatinonMeasure (L : GHHSLatinon) : LatinonMeasure where
  measure := L.measure
  order := L.order
  order_preserving := L.order_measurePreserving
  xy_uniform _ _ hS hT := L.measure_xy hS hT
  xz_uniform _ _ hS hU := L.measure_xz hS hU
  yz_uniform _ _ hT hU := L.measure_yz hT hU

end GHHSLatinon

section
variable {K : Kernel (I × I) I} {f : I → I}

/-- If `λ² ⊗ K` has uniform row–symbol marginal, then `K` satisfies the row condition of GHHS
Definition 3.5 (auxiliary comparison). -/
theorem ae_row_permuton_of_xz [IsMarkovKernel K] (hf : MeasurePreserving f volume volume)
    (hxz : ∀ S U : Set I, MeasurableSet S → MeasurableSet U →
      (unitSquareVolume ⊗ₘ K) ((S ×ˢ Set.univ) ×ˢ U) = volume S * volume U) :
    ∀ᵐ x ∂(volume : Measure I), IsPermuton (rowMeasure K f x) := by
  sorry

/-- If `λ² ⊗ K` has uniform column–symbol marginal, then `K` satisfies the column condition of
GHHS Definition 3.5 (auxiliary comparison). -/
theorem ae_col_permuton_of_yz [IsMarkovKernel K] (hf : MeasurePreserving f volume volume)
    (hyz : ∀ T U : Set I, MeasurableSet T → MeasurableSet U →
      (unitSquareVolume ⊗ₘ K) ((Set.univ ×ˢ T) ×ˢ U) = volume T * volume U) :
    ∀ᵐ y ∂(volume : Measure I), IsPermuton (colMeasure K f y) := by
  sorry

end

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

/-- **Round trip 1.** Measure ⇒ kernel ⇒ measure is the identity. -/
theorem toLatinonMeasure_ofLatinonMeasure (W : LatinonMeasure) :
    (ofLatinonMeasure W).toLatinonMeasure = W := by
  sorry

/-- **Round trip 2.** Kernel ⇒ measure ⇒ kernel returns a kernel equal to the original one
almost everywhere on `I × I`. -/
theorem ofLatinonMeasure_toLatinonMeasure_kernel (L : GHHSLatinon) :
    ∀ᵐ p ∂unitSquareVolume, (ofLatinonMeasure L.toLatinonMeasure).kernel p = L.kernel p := by
  sorry

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

/-- GHHS relabelling `W^{φ,ψ}(x, y) = W(φ x, ψ y)`. -/
def relabelKernel (K : Kernel (I × I) I) (e f : LatinonRelabel) : Kernel (I × I) I :=
  K.comap (Prod.map e f)
    ((e.measurable.comp measurable_fst).prodMk (f.measurable.comp measurable_snd))

/-- GHHS Definition 4.3, the cost of one pair `(φ, ψ)` in formula (2). -/
def ghhsAlignmentCost (L₁ L₂ : GHHSLatinon) (e f : LatinonRelabel) : ℝ :=
  graphonCut (fun p => orderGraphon L₁.order p - orderGraphon (L₂.order ∘ e) p) +
    graphonCut (fun p => orderGraphon L₁.order p - orderGraphon (L₂.order ∘ f) p) +
    kernelCut L₁.kernel (relabelKernel L₂.kernel e f)

/-- **GHHS Definition 4.3**, the cut distance of Latinons, on the ground space `I`. -/
def ghhsCutDistance (L₁ L₂ : GHHSLatinon) : ℝ :=
  sInf (Set.range (fun p : LatinonRelabel × LatinonRelabel => ghhsAlignmentCost L₁ L₂ p.1 p.2))

/-- **Distance.** The GHHS cut distance of two GHHS Latinons equals the cut distance of their
measure representations. -/
theorem ghhsCutDistance_eq (L₁ L₂ : GHHSLatinon) :
    ghhsCutDistance L₁ L₂ = latinonCutDistance L₁.toLatinonMeasure L₂.toLatinonMeasure := by
  sorry

/-- Measurability of the cell coordinate map. In the source module this is Lean's generated
certificate `patternCellKernel._proof_1`; it is named explicitly because inside one file Lean
would otherwise reuse the identical certificate of `latinonPatternCellKernel`. Compared by its
statement. -/
theorem patternCellKernel._proof_1 (k l : ℕ) (a : Fin k × Fin l) :
    type_of% ((((measurable_pi_apply a.1).comp measurable_fst).prodMk
      ((measurable_pi_apply a.2).comp measurable_snd) :
        Measurable (fun c : LatinonPatternConfig k l => (c.1 a.1, c.2 a.2)))) :=
  ((measurable_pi_apply a.1).comp measurable_fst).prodMk
    ((measurable_pi_apply a.2).comp measurable_snd)

/-- The law of the cell `(x_i, y_j)` of a configuration under a kernel `K`. -/
def patternCellKernel (K : Kernel (I × I) I) (k l : ℕ) (a : Fin k × Fin l) :
    Kernel (LatinonPatternConfig k l) I :=
  K.comap (fun c => (c.1 a.1, c.2 a.2)) (patternCellKernel._proof_1 k l a)

instance instIsMarkovKernelLatinonPatternConfigElemRealUnitIntervalPatternCellKernelOfProd
    (K : Kernel (I × I) I) [IsMarkovKernel K] (k l : ℕ) (a : Fin k × Fin l) :
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

/-- **Pattern densities.** GHHS pattern densities of a GHHS Latinon equal the pattern densities
of its measure representation. -/
theorem ghhsPatternDensity_eq {k l : ℕ} (L : GHHSLatinon) (P : LatinOrderPattern k l) :
    ghhsPatternDensity L P = latinonPatternDensity L.toLatinonMeasure P := by
  sorry

end GHHSBridge

open MeasureTheory ProbabilityTheory InformationTheory LatinonEntropy
open scoped unitInterval ENNReal

namespace GHHSBridge

section ChainRule

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace.CountableOrCountablyGenerated α β]

/-- **Conditional chain rule.** `KL(μ ⊗ κ ‖ μ ⊗ η) = ∫⁻ KL(κ a ‖ η a) dμ(a)`. -/
theorem klDiv_compProd_right_eq_lintegral (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  sorry

end ChainRule

/-- `∫∫ KL(K(x, y) ‖ λ) dx dy ∈ [0, ∞]`: GHHS's `∫∫∫ g log g`, extended by `∞`. -/
def ghhsRate (L : GHHSLatinon) : ℝ≥0∞ :=
  ∫⁻ p, klDiv (L.kernel p) volume ∂unitSquareVolume

/-- **GHHS entropy** with the sign of the Latinon preprint: `Ent(L) = −∫∫∫ g log g`,
equal to `−∞` when the kernel has no densities or `g log g` is not integrable. -/
def ghhsEntropy (L : GHHSLatinon) : EReal := -(ghhsRate L : EReal)

/-- **Entropy.** The GHHS entropy of a GHHS Latinon equals the entropy of its measure
representation, including the value `−∞`. -/
theorem ghhsEntropy_eq (L : GHHSLatinon) : ghhsEntropy L = latinonEntropy L.toLatinonMeasure := by
  sorry

end GHHSBridge

namespace GHHSBridge

open MeasureTheory LatinonEntropy
open scoped Classical unitInterval ENNReal

variable {J : Type*} [Fintype J] {k l : J → ℕ}

/-- **GHHS Definition 3.3** (densities in Latin squares, binomial normalization). -/
def ghhsFiniteDensity {n k l : ℕ} (K : LatinArray n) (P : LatinOrderPattern k l) : ℝ :=
  standardMatrixPatternDensity K P

/-- Latin squares of order `n` with `t(A_j, K) = a_j ± δ` for every `j`. -/
def ghhsCount (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ) (δ : ℝ) (n : ℕ) :
    Finset (LatinArray n) :=
  (allLatinSquares n).filter fun K => ∀ j, |ghhsFiniteDensity K (P j) - a j| ≤ δ

/-- `ℓ = sup Ent(L)` over GHHS Latinons with `t(A_j, L) = a_j` for every `j`. -/
def ghhsEntSup (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ) : EReal :=
  ⨆ L : {L : GHHSLatinon // ∀ j, ghhsPatternDensity L (P j) = a j}, ghhsEntropy L.1

omit [Fintype J] in
/-- The GHHS supremum is minus the contracted rate of the Latinon preprint. -/
theorem ghhsEntSup_eq (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ) :
    ghhsEntSup P a = -((latinonContractedRate (latinonPatternProfile P) a : ℝ≥0∞) : EReal) := by
  sorry

/-- **GHHS Conjecture 12.4**, case `ℓ > −∞`, on the ground space `I`, with the entropy
sign of the Latinon preprint. -/
theorem ghhsConjecture_12_4 (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ)
    (hℓ : ghhsEntSup P a ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, 0 < (ghhsCount P a δ n).card ∧
      |(1 / (n : ℝ) ^ 2) *
          Real.log (((ghhsCount P a δ n).card : ℝ) / ((n : ℝ) / Real.exp 2) ^ (n ^ 2)) -
        (ghhsEntSup P a).toReal| ≤ ε := by
  sorry

/-- **GHHS Conjecture 12.4**, case `ℓ = −∞`: the counts are eventually below
`exp(n² (log n − 2 − t))` for every `t`. -/
theorem ghhsConjecture_12_4_bot (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ)
    (hℓ : ghhsEntSup P a = ⊥) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((ghhsCount P a δ n).card : ℝ) ≤ Real.exp ((n : ℝ) ^ 2 * (Real.log (n : ℝ) - 2 - t)) := by
  sorry

/-- The case `ℓ = −∞` in GHHS's normalization: eventually either no Latin square is
counted, or the normalized logarithm is at most `−t`. -/
theorem ghhsConjecture_12_4_bot' (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ)
    (hℓ : ghhsEntSup P a = ⊥) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, (ghhsCount P a δ n).card = 0 ∨
      (1 / (n : ℝ) ^ 2) *
          Real.log (((ghhsCount P a δ n).card : ℝ) / ((n : ℝ) / Real.exp 2) ^ (n ^ 2)) ≤ -t := by
  sorry

end GHHSBridge
