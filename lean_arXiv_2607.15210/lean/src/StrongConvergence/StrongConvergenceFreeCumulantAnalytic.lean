import StrongConvergence.StrongConvergenceFreeCumulant
import RandomCompression.RevisionBernoulliLaw

/-!
# Analytic evaluation of the Bernoulli cumulant series

The recursively constructed coefficients satisfy the Bernoulli quadratic after
evaluation inside their proved disk of absolute convergence. A uniform bound
selects the correct square-root branch near zero.
-/

open scoped BigOperators

noncomputable section
namespace ProjectionChannels.FreeCumulant

theorem bernoulliCumulant_eval_quadratic {t z : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : |z| < 1 / 8) :
    (∑' n : ℕ, bernoulliCumulant t n * z ^ n) ^ 2 +
      (1 - z) * (∑' n : ℕ, bernoulliCumulant t n * z ^ n) - t * z = 0 := by
  let f : ℕ → ℝ := fun n => bernoulliTail t n * z ^ n
  let conv : ℕ → ℝ := fun n => ∑ i : Fin (n + 1), f i.val * f (n - i.val)
  have hz8 : |8 * abs z| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hf : Summable (fun n => ‖f n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (summable_geometric_of_abs_lt_one hz8)
    intro n
    change |bernoulliTail t n * z ^ n| ≤ (8 * |z|) ^ n
    rw [abs_mul, abs_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right (abs_bernoulliCumulant_succ_le ht0 ht1 n)
      (by positivity)
  have hconv : Summable conv := by
    have h := summable_norm_sum_mul_range_of_summable_norm hf hf
    have h' : Summable (fun n => ‖conv n‖) := by
      simpa only [conv, ← Fin.sum_univ_eq_sum_range] using h
    exact h'.of_norm
  have hprod : (∑' n, f n) * (∑' n, f n) = ∑' n, conv n := by
    simpa only [conv, ← Fin.sum_univ_eq_sum_range] using
      tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hf
  have hrec : ∀ n, f (n + 1) = z * (f n - conv n) := by
    intro n
    have hsum : conv n = (∑ i : Fin (n + 1),
        bernoulliTail t i.val * bernoulliTail t (n - i.val)) * z ^ n := by
      dsimp only [conv, f]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      have hi : i.val + (n - i.val) = n := by omega
      calc
        _ = (bernoulliTail t i.val * bernoulliTail t (n - i.val)) *
            z ^ (i.val + (n - i.val)) := by rw [pow_add]; ring
        _ = _ := by rw [hi]
    change bernoulliTail t (n + 1) * z ^ (n + 1) =
      z * (bernoulliTail t n * z ^ n - conv n)
    rw [bernoulliTail, hsum, pow_succ]
    ring
  have hsplit := hf.of_norm.tsum_eq_zero_add
  have hf0 : f 0 = t := by simp [f, bernoulliTail]
  rw [hf0] at hsplit
  have hH : (∑' n, f n) - t = z * ((∑' n, f n) - (∑' n, f n) ^ 2) := by
    calc
      _ = ∑' n, f (n + 1) := by linarith [hsplit]
      _ = ∑' n, z * (f n - conv n) := tsum_congr hrec
      _ = z * ((∑' n, f n) - ∑' n, conv n) := by
        rw [tsum_mul_left, hf.of_norm.tsum_sub hconv]
      _ = _ := by rw [← hprod, pow_two]
  have hk : Summable (fun n => bernoulliCumulant t n * z ^ n) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using summable_abs_bernoulliCumulant ht0 ht1 hz
  have hF : (∑' n, bernoulliCumulant t n * z ^ n) = z * (∑' n, f n) := by
    rw [hk.tsum_eq_zero_add]
    simp only [bernoulliCumulant_zero, zero_mul, zero_add]
    calc
      _ = ∑' n, z * f n := by
        apply tsum_congr
        intro n
        simp only [bernoulliCumulant, f, pow_succ]
        ring
      _ = _ := tsum_mul_left
  rw [hF]
  linear_combination z * hH

/-- Identification with the branch used in the project's Bernoulli R-transform.
This includes the removable point `z=0` and both signs of `z`. -/
theorem bernoulliDual_eq_cumulant_sum {t z : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : |z| ≤ 1 / 16) :
    bernoulliDual t z = ∑' n : ℕ, bernoulliCumulant t n * z ^ n := by
  have hz' : |z| < 1 / 8 := by linarith
  apply bernoulliDual_eq_of_quadratic ht0 ht1
    (bernoulliCumulant_eval_quadratic ht0 ht1 hz')
  have hknorm : Summable (fun n => ‖bernoulliCumulant t n * z ^ n‖) := by
    simpa only [Real.norm_eq_abs] using summable_abs_bernoulliCumulant ht0 ht1 hz'
  have hnorm : |∑' n, bernoulliCumulant t n * z ^ n| ≤
      ∑' n, |bernoulliCumulant t n * z ^ n| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hknorm
  have hden : 0 < 1 - 8 * |z| := by linarith
  have hsmall : |∑' n, bernoulliCumulant t n * z ^ n| ≤ 1 / 8 := by
    apply (hnorm.trans (tsum_abs_bernoulliCumulant_le ht0 ht1 hz')).trans
    apply (div_le_iff₀ hden).mpr
    linarith
  linarith [(abs_le.mp hsmall).1, le_abs_self z]

#print axioms bernoulliCumulant_eval_quadratic
#print axioms bernoulliDual_eq_cumulant_sum

end ProjectionChannels.FreeCumulant
