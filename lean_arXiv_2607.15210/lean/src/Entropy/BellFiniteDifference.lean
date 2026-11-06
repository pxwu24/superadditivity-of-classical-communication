import Entropy.Analysis

/-! Scalar logarithmic remainder underlying the uniform finite-difference
estimate. The weighted form applies to normalized matrix eigenvalue counting
measures; it does not presuppose a random-matrix limit. -/

open Finset
noncomputable section
namespace BellLimitVerification

lemma log_symmetric_remainder {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |Real.log (1 + z) + Real.log (1 - z) + z ^ 2| ≤ 2 * z ^ 4 := by
  have hzlo := neg_abs_le z
  have hzhi := le_abs_self z
  have hp : 0 < 1 + z := by linarith
  have hm : 0 < 1 - z := by linarith
  have hzsq : z ^ 2 ≤ 1 / 4 := by
    nlinarith only [hz, abs_nonneg z, sq_abs z]
  have hsmall : |-(z ^ 2)| ≤ 1 / 2 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg z)]
    linarith
  have h := AppendixB.log_bound1 hsmall
  rw [← Real.log_mul hp.ne' hm.ne']
  have he : (1 + z) * (1 - z) = 1 + -(z ^ 2) := by ring
  rw [he]
  convert h using 1 <;> ring

lemma log_central_remainder {x c : ℝ} (hx : x ≠ 0) (hc : |x * c| ≤ 1 / 2) :
    |(Real.log (1 + x * c) + Real.log (1 - x * c)) / x ^ 2 + c ^ 2|
      ≤ 2 * x ^ 2 * c ^ 4 := by
  have h := log_symmetric_remainder hc
  have hs : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have he : (Real.log (1 + x * c) + Real.log (1 - x * c)) / x ^ 2 + c ^ 2 =
      (Real.log (1 + x * c) + Real.log (1 - x * c) + (x * c) ^ 2) / x ^ 2 := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hs, div_le_iff₀ hs]
  convert h using 1 <;> ring

/-- Uniform normalized spectral remainder. For matrices, take the eigenvalues
as `c` and weights all equal to reciprocal dimension. The bound `2 x² M⁴`
is slightly stronger than the paper's stated `4 x² M⁴`. -/
theorem weighted_log_central_remainder {ι : Type*} (s : Finset ι)
    (weights c : ι → ℝ) (M x : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weights i) (hmass : ∑ i ∈ s, weights i = 1)
    (hc : ∀ i ∈ s, |c i| ≤ M) (hx : x ≠ 0)
    (hsmall : |x| * M ≤ 1 / 2) :
    |(∑ i ∈ s, weights i *
        ((Real.log (1 + x * c i) + Real.log (1 - x * c i)) / x ^ 2)) +
      ∑ i ∈ s, weights i * (c i) ^ 2|
      ≤ 2 * x ^ 2 * M ^ 4 := by
  have hi : ∀ i ∈ s,
      |weights i * (((Real.log (1 + x * c i) + Real.log (1 - x * c i)) /
          x ^ 2) + (c i) ^ 2)| ≤ weights i * (2 * x ^ 2 * M ^ 4) := by
    intro i his
    have hprod : |x * c i| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hc i his) (abs_nonneg x)).trans hsmall
    have hrem := log_central_remainder hx hprod
    have hpow : (c i) ^ 4 ≤ M ^ 4 := by
      calc (c i) ^ 4 = |c i| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
        _ ≤ M ^ 4 := pow_le_pow_left (abs_nonneg _) (hc i his) _
    rw [abs_mul, abs_of_nonneg (hw i his)]
    apply mul_le_mul_of_nonneg_left _ (hw i his)
    exact hrem.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  calc
    _ = |∑ i ∈ s, weights i *
        (((Real.log (1 + x * c i) + Real.log (1 - x * c i)) / x ^ 2) + (c i) ^ 2)| := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ s, |weights i *
        (((Real.log (1 + x * c i) + Real.log (1 - x * c i)) / x ^ 2) + (c i) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, weights i * (2 * x ^ 2 * M ^ 4) := Finset.sum_le_sum hi
    _ = 2 * x ^ 2 * M ^ 4 := by rw [← Finset.sum_mul, hmass, one_mul]

#print axioms log_symmetric_remainder
#print axioms log_central_remainder
#print axioms weighted_log_central_remainder
end BellLimitVerification
