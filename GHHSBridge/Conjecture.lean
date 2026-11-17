/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GHHSBridge.Entropy
public import LatinonPatternConjecture

/-!
# Conjecture 12.4 of GHHS in their own terms

GHHS, Conjecture 12.4: let `(A_i)_{i ∈ I}` be a finite family of patterns and `a_i ∈ [0, 1]`.
Let `ℓ = sup Ent(L)` over Latinons with `t(A_i, L) = a_i` for each `i`. Then for each `ε > 0`
there are `δ > 0` and `n₀` such that for each `n > n₀` the number `N` of Latin squares `K`
of order `n` with `t(A_i, K) = a_i ± δ` for each `i` satisfies
`(1/n²) log (N / (n/e²)^{n²}) = ℓ ± ε`.

This file states the conjecture with the definitions of GHHS, on the ground space `I`:

* `ghhsFiniteDensity` is Definition 3.3 (binomial normalization), as formalized in the
  Latinon build (`standardMatrixPatternDensity`): the number of index tuples
  `x ∈ [n]^k_<`, `y ∈ [n]^ℓ_<` whose submatrix is a realization of `A`, divided by
  `C(n, k) C(n, ℓ)`.
* `ghhsCount P a δ n` is the set of Latin squares of order `n` with `|t(A_i, K) − a_i| ≤ δ`.
* `ghhsEntSup P a` is `ℓ`, the supremum in `EReal` of `ghhsEntropy` over GHHS Latinons
  with `ghhsPatternDensity L (A_i) = a_i`. The entropy has the sign of the
  Latinon preprint (minus relative entropy); the supremum of the empty family is `−∞`.

Results.

* `ghhsEntSup_eq`: `ℓ = −inf {KL(ν ‖ λ³) : t(A_i, ν) = a_i}`, the contracted rate of the
  Latinon preprint.
* `ghhsConjecture_12_4`: the conjecture when `ℓ > −∞`, with GHHS's normalization
  `(1/n²) log (N/(n/e²)^{n²})`; in particular `N > 0` for large `n`.
* `ghhsConjecture_12_4_bot`: when `ℓ = −∞`, for every `t` there are `δ > 0` and `n₀` with
  `N ≤ exp(n² (log n − 2 − t))` for `n ≥ n₀`; so either `N = 0` or the normalized
  logarithm is at most `−t`. This is the reading of "`= ℓ ± ε`" for `ℓ = −∞`.

Both follow from Theorem 2.2 of the Latinon preprint (Lean:
`finite_rate_standard_pattern_log_count`, `infinite_rate_standard_pattern_count_upper`,
`empty_standard_pattern_fiber_eventually_zero`) and the identifications of the earlier
files of this project.
-/

@[expose] public section

noncomputable section

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

theorem ghhsCount_eq (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (n : ℕ) : ghhsCount P a δ n = standardMatrixPatternBoxFamily P a δ n := by
  unfold ghhsCount standardMatrixPatternBoxFamily
  apply Finset.filter_congr
  intro K _
  rw [Metric.mem_closedBall, dist_pi_le_iff hδ]
  simp only [Real.dist_eq, standardMatrixPatternProfile, ghhsFiniteDensity]

/-- `ℓ = sup Ent(L)` over GHHS Latinons with `t(A_j, L) = a_j` for every `j`. -/
def ghhsEntSup (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ) : EReal :=
  ⨆ L : {L : GHHSLatinon // ∀ j, ghhsPatternDensity L (P j) = a j}, ghhsEntropy L.1

omit [Fintype J] in
/-- The GHHS supremum is minus the contracted rate of the Latinon preprint. -/
theorem ghhsEntSup_eq (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ) :
    ghhsEntSup P a = -((latinonContractedRate (latinonPatternProfile P) a : ℝ≥0∞) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun L => ?_
    have hW : latinonPatternProfile P L.1.toLatinonMeasure = a :=
      funext fun j => (ghhsPatternDensity_eq L.1 (P j)).symm.trans (L.2 j)
    have hle : latinonContractedRate (latinonPatternProfile P) a ≤
        latinonRate L.1.toLatinonMeasure := by
      have h := latinonContractedRate_le (latinonPatternProfile P) L.1.toLatinonMeasure
      rwa [hW] at h
    rw [ghhsEntropy_eq]
    exact EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2 hle)
  · by_cases hz : a ∈ Set.range (latinonPatternProfile P)
    · obtain ⟨W, hW, hR⟩ :=
        latinonContractedRate_attained _ (continuous_latinonPatternProfile P) a hz
      rw [hR]
      have hfeas : ∀ j, ghhsPatternDensity (ofLatinonMeasure W) (P j) = a j := fun j => by
        rw [← latinonPatternDensity_eq_ghhs]
        exact congrFun hW j
      refine le_trans ?_ (le_iSup (fun L : {L : GHHSLatinon //
        ∀ j, ghhsPatternDensity L (P j) = a j} => ghhsEntropy L.1) ⟨ofLatinonMeasure W, hfeas⟩)
      exact (latinonEntropy_eq_ghhs W).le
    · rw [latinonContractedRate_outside_image _ _ hz]
      simp

/-- GHHS's normalization: `(1/n²) log (N / (n/e²)^{n²}) = log N / n² − (log n − 2)`. -/
theorem normalized_log_eq {n N : ℕ} (hn : 0 < n) (hN : 0 < N) :
    (1 / (n : ℝ) ^ 2) * Real.log ((N : ℝ) / ((n : ℝ) / Real.exp 2) ^ (n ^ 2)) =
      Real.log (N : ℝ) / (n : ℝ) ^ 2 - (Real.log (n : ℝ) - 2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hNR : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [Real.log_div hNR.ne' (pow_pos (div_pos hnR (Real.exp_pos 2)) _).ne', Real.log_pow,
    Real.log_div hnR.ne' (Real.exp_pos 2).ne', Real.log_exp]
  push_cast
  have h2 : (n : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp

/-- **GHHS Conjecture 12.4**, case `ℓ > −∞`, on the ground space `I`, with the entropy
sign of the Latinon preprint. -/
theorem ghhsConjecture_12_4 (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ)
    (hℓ : ghhsEntSup P a ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, 0 < (ghhsCount P a δ n).card ∧
      |(1 / (n : ℝ) ^ 2) *
          Real.log (((ghhsCount P a δ n).card : ℝ) / ((n : ℝ) / Real.exp 2) ^ (n ^ 2)) -
        (ghhsEntSup P a).toReal| ≤ ε := by
  have hR : latinonContractedRate (latinonPatternProfile P) a ≠ ⊤ := by
    intro h
    apply hℓ
    rw [ghhsEntSup_eq, h]
    simp
  obtain ⟨ρ, hρ, -, N, hN, hcount⟩ :=
    finite_rate_standard_pattern_log_count P a hR 1 ε one_pos hε
  refine ⟨ρ, hρ, N, fun n hn => ?_⟩
  obtain ⟨hpos, habs⟩ := hcount n hn
  rw [ghhsCount_eq P a hρ.le]
  refine ⟨hpos, ?_⟩
  rw [normalized_log_eq (hN.trans_le hn) hpos, ghhsEntSup_eq, EReal.toReal_neg_eq,
    EReal.toReal_coe_ennreal, sub_neg_eq_add]
  exact habs

/-- **GHHS Conjecture 12.4**, case `ℓ = −∞`: the counts are eventually below
`exp(n² (log n − 2 − t))` for every `t`. -/
theorem ghhsConjecture_12_4_bot (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ)
    (hℓ : ghhsEntSup P a = ⊥) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((ghhsCount P a δ n).card : ℝ) ≤ Real.exp ((n : ℝ) ^ 2 * (Real.log (n : ℝ) - 2 - t)) := by
  rw [ghhsEntSup_eq, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff] at hℓ
  by_cases hz : ∃ W : LatinonMeasure, latinonPatternProfile P W = a
  · obtain ⟨ρ, hρ, -, N, -, hc⟩ :=
      infinite_rate_standard_pattern_count_upper P a hℓ 1 (t + 1) 1 one_pos one_pos
    refine ⟨ρ, hρ, N, fun n hn => ?_⟩
    rw [ghhsCount_eq P a hρ.le]
    refine (hc n hn).trans_eq ?_
    congr 1
    ring
  · obtain ⟨ρ, hρ, -, N, -, hc⟩ := empty_standard_pattern_fiber_eventually_zero P a hz 1 one_pos
    refine ⟨ρ, hρ, N, fun n hn => ?_⟩
    rw [ghhsCount_eq P a hρ.le, hc n hn, Nat.cast_zero]
    exact (Real.exp_pos _).le

/-- The case `ℓ = −∞` in GHHS's normalization: eventually either no Latin square is
counted, or the normalized logarithm is at most `−t`. -/
theorem ghhsConjecture_12_4_bot' (P : ∀ j, LatinOrderPattern (k j) (l j)) (a : J → ℝ)
    (hℓ : ghhsEntSup P a = ⊥) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, (ghhsCount P a δ n).card = 0 ∨
      (1 / (n : ℝ) ^ 2) *
          Real.log (((ghhsCount P a δ n).card : ℝ) / ((n : ℝ) / Real.exp 2) ^ (n ^ 2)) ≤ -t := by
  obtain ⟨δ, hδ, N, hc⟩ := ghhsConjecture_12_4_bot P a hℓ t
  refine ⟨δ, hδ, N + 1, fun n hn => ?_⟩
  rcases Nat.eq_zero_or_pos (ghhsCount P a δ n).card with h0 | hpos
  · exact Or.inl h0
  · right
    have hn : 0 < n := by omega
    rw [normalized_log_eq hn hpos]
    have hlog := Real.log_le_log (Nat.cast_pos.2 hpos) (hc n (by omega))
    rw [Real.log_exp] at hlog
    have hnsq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [sub_le_iff_le_add, div_le_iff₀ hnsq]
    nlinarith [hlog]

end GHHSBridge
