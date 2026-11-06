import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Kernel-checked numerical entropy gap for output dimension 182

The logarithms in this file are `Real.log`.  Rational enclosures follow
from the finite logarithm-series remainder theorem in mathlib; no numerical
oracle, floating-point decision procedure, or additional axiom is used.
The connection between `entropyLower` and all states in the limiting body
is a separate mathematical statement, not an assumption of this file.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace ProjectionChannels.K182

noncomputable def cutoff : ℝ := 162513 / 1000000
noncomputable def density : ℝ := 27 / 100000
noncomputable def bellMixing : ℝ :=
  182 ^ 2 * (1 - density) / ((182 ^ 2 - 1) ^ 2 * density + 1 - density)
noncomputable def bellAlpha : ℝ := (1 + (182 ^ 2 - 1) * bellMixing) / 182 ^ 2
noncomputable def bellBeta : ℝ := (1 - bellMixing) / 182 ^ 2
noncomputable def entropyLower : ℝ :=
  -cutoff * Real.log cutoff - (1 - cutoff) * Real.log ((1 - cutoff) / 181)
noncomputable def bellEntropy : ℝ :=
  -bellAlpha * Real.log bellAlpha - (182 ^ 2 - 1) * bellBeta * Real.log bellBeta

/-- An explicit finite-series enclosure, with all side conditions rational. -/
theorem log_enclosure (x lo hi : ℝ) (n : ℕ) (hx : |1 - x| < 1)
    (hlo : lo ≤ -(∑ i ∈ Finset.range n, (1 - x) ^ (i + 1) / (i + 1)) -
      |1 - x| ^ (n + 1) / (1 - |1 - x|))
    (hhi : -(∑ i ∈ Finset.range n, (1 - x) ^ (i + 1) / (i + 1)) +
      |1 - x| ^ (n + 1) / (1 - |1 - x|) ≤ hi) :
    lo ≤ Real.log x ∧ Real.log x ≤ hi := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [show 1 - (1 - x) = x by ring] at h
  obtain ⟨h₁, h₂⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_half_bounds :
    -(693147181 : ℝ) / 1000000000 ≤ Real.log (1 / 2) ∧
    Real.log (1 / 2) ≤ -(693147179 : ℝ) / 1000000000 := by
  apply log_enclosure _ _ _ 32 <;> norm_num [Finset.sum_range_succ, abs_div]

private theorem log_cutoff_scaled_bounds :
    -(430702920 : ℝ) / 1000000000 ≤ Real.log (162513 / 250000) ∧
    Real.log (162513 / 250000) ≤ -(430702918 : ℝ) / 1000000000 := by
  apply log_enclosure _ _ _ 32 <;> norm_num [Finset.sum_range_succ, abs_div]

private theorem log_rest_bounds :
    -(177349538 : ℝ) / 1000000000 ≤ Real.log (837487 / 1000000) ∧
    Real.log (837487 / 1000000) ≤ -(177349536 : ℝ) / 1000000000 := by
  apply log_enclosure _ _ _ 32 <;> norm_num [Finset.sum_range_succ, abs_div]

private theorem log_dimension_scaled_bounds :
    -(346680414 : ℝ) / 1000000000 ≤ Real.log (181 / 256) ∧
    Real.log (181 / 256) ≤ -(346680412 : ℝ) / 1000000000 := by
  apply log_enclosure _ _ _ 32 <;> norm_num [Finset.sum_range_succ, abs_div]

private theorem log_alpha_scaled_bounds :
    -(111456426 : ℝ) / 1000000000 ≤ Real.log (27429156101413 / 30663191598767) ∧
    Real.log (27429156101413 / 30663191598767) ≤ -(111456424 : ℝ) / 1000000000 := by
  apply log_enclosure _ _ _ 32 <;> norm_num [Finset.sum_range_succ, abs_div]

private theorem log_beta_scaled_bounds :
    -(129352160 : ℝ) / 1000000000 ≤ Real.log (26942657335296 / 30663191598767) ∧
    Real.log (26942657335296 / 30663191598767) ≤ -(129352158 : ℝ) / 1000000000 := by
  apply log_enclosure _ _ _ 32 <;> norm_num [Finset.sum_range_succ, abs_div]

private theorem log_mul_half_pow (y : ℝ) (hy : y ≠ 0) (n : ℕ) :
    Real.log (y * (1 / 2 : ℝ) ^ n) = Real.log y + n * Real.log (1 / 2) := by
  rw [Real.log_mul hy (pow_ne_zero _ (by norm_num)), Real.log_pow]

theorem bellAlpha_eq : bellAlpha = (27429156101413 : ℝ) / 245305532790136 := by
  norm_num [bellAlpha, bellMixing, density]

theorem bellBeta_eq : bellBeta = (6577797201 : ℝ) / 245305532790136 := by
  norm_num [bellBeta, bellMixing, density]

/-- The rationally specified Bell spectrum is a strictly positive probability vector. -/
theorem bell_coefficients_valid : 0 < bellAlpha ∧ 0 < bellBeta ∧
    bellAlpha + (182 ^ 2 - 1) * bellBeta = 1 := by
  rw [bellAlpha_eq, bellBeta_eq]
  norm_num

/-- The chosen density lies in the admissible open interval. -/
theorem density_admissible : (182 : ℝ)⁻¹ ^ 2 < density ∧ density < 1 := by
  norm_num [density]

/-- A rigorous strict lower bound on the explicit entropy-expression gap.

This theorem alone does not assert that `entropyLower` bounds every output
state: that analytic step must be supplied separately.
-/
theorem certified_entropy_gap : (477 : ℝ) / 1000000 < 2 * entropyLower - bellEntropy := by
  obtain ⟨hhalf₁, hhalf₂⟩ := log_half_bounds
  obtain ⟨hcut₁, hcut₂⟩ := log_cutoff_scaled_bounds
  obtain ⟨hrest₁, hrest₂⟩ := log_rest_bounds
  obtain ⟨hdim₁, hdim₂⟩ := log_dimension_scaled_bounds
  obtain ⟨halpha₁, halpha₂⟩ := log_alpha_scaled_bounds
  obtain ⟨hbeta₁, hbeta₂⟩ := log_beta_scaled_bounds
  have hc : Real.log cutoff = Real.log (162513 / 250000 : ℝ) +
      2 * Real.log (1 / 2) := by
    convert log_mul_half_pow (162513 / 250000) (by norm_num) 2 using 1
    norm_num [cutoff]
  have hd : Real.log (181 / 256 : ℝ) = Real.log 181 +
      8 * Real.log (1 / 2) := by
    convert log_mul_half_pow 181 (by norm_num) 8 using 1
    norm_num
  have ha : Real.log bellAlpha = Real.log (27429156101413 / 30663191598767 : ℝ) +
      3 * Real.log (1 / 2) := by
    rw [bellAlpha_eq]
    convert log_mul_half_pow (27429156101413 / 30663191598767) (by norm_num) 3
      using 1
    norm_num
  have hb : Real.log bellBeta = Real.log (26942657335296 / 30663191598767 : ℝ) +
      15 * Real.log (1 / 2) := by
    rw [bellBeta_eq]
    convert log_mul_half_pow (26942657335296 / 30663191598767) (by norm_num) 15
      using 1
    norm_num
  have hr : Real.log ((1 - cutoff) / 181) =
      Real.log (837487 / 1000000 : ℝ) - Real.log 181 := by
    rw [Real.log_div (by norm_num [cutoff]) (by norm_num)]
    norm_num [cutoff]
  unfold entropyLower bellEntropy
  rw [hc, ha, hb, hr, bellAlpha_eq, bellBeta_eq]
  norm_num [cutoff] at *
  linarith

#print axioms certified_entropy_gap

end ProjectionChannels.K182

