import StrongConvergence.StrongConvergenceMomentLaw
import RandomCompression.RevisionBernoulliLaw
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed

/-! The actual Cauchy transform of a compact probability law as a moment series. -/
open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels

lemma abs_moment_le_of_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {K : ℝ} (hs : ∀ᵐ y ∂ν, |y| ≤ K) (n : ℕ) :
    |∫ y, y^n ∂ν| ≤ K^n := by
  have hb : ∀ᵐ y ∂ν, ‖y^n‖ ≤ K^n := hs.mono fun y hy => by
    simpa only [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg y) hy n
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const hb

/-- Moment expansion at inverse spectral parameter `z`, valid on both sides
of infinity. The statement includes `z = 0` without any division by zero. -/
theorem hasSum_moment_resolvent (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {K z : ℝ} (hK : 0 ≤ K) (hs : ∀ᵐ y ∂ν, |y| ≤ K)
    (hz : K * |z| < 1) :
    HasSum (fun n : ℕ => (∫ y, y^n ∂ν) * z^n)
      (∫ y, (1-y*z)⁻¹ ∂ν) := by
  have hq : |K * abs z| < 1 := by rw [abs_of_nonneg (by positivity)]; exact hz
  have hi := hasSum_integral_of_dominated_convergence
    (μ := ν) (F := fun n (y : ℝ) => (y*z)^n) (f := fun y => (1-y*z)⁻¹)
    (fun n _ => (K * |z|)^n)
    (fun n => Continuous.aestronglyMeasurable (by fun_prop))
    (fun n => hs.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_pow, abs_mul]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hy (abs_nonneg z)) n)
    (Eventually.of_forall fun _ => summable_geometric_of_abs_lt_one hq)
    (integrable_const _)
    (hs.mono fun y hy => hasSum_geometric_of_abs_lt_one
      (by rw [abs_mul]; exact (mul_le_mul_of_nonneg_right hy (abs_nonneg z)).trans_lt hz))
  convert hi using 1
  ext n
  simp_rw [mul_pow]
  exact (integral_mul_const _ _).symm

lemma summable_norm_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {K z : ℝ} (hK : 0 ≤ K) (hs : ∀ᵐ y ∂ν, |y| ≤ K)
    (hz : K * |z| < 1) :
    Summable (fun n : ℕ => ‖(∫ y, y^n ∂ν) * z^n‖) := by
  have hq : |K * abs z| < 1 := by rw [abs_of_nonneg (by positivity)]; exact hz
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (summable_geometric_of_abs_lt_one hq)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right (abs_moment_le_of_support ν hs n) (by positivity)

/-- The real Cauchy transform is its absolutely convergent moment series
at every real point strictly outside the symmetric support bound. -/
theorem realCauchyTransform_eq_moment_tsum (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {K x : ℝ} (hK : 0 ≤ K) (hs : ∀ᵐ y ∂ν, |y| ≤ K) (hx : K < |x|) :
    realCauchyTransform ν x = x⁻¹ *
      ∑' n : ℕ, (∫ y, y^n ∂ν) * (x⁻¹)^n := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; linarith
  have hz : K * |x⁻¹| < 1 := by
    rw [abs_inv, ← div_eq_mul_inv]
    exact (div_lt_one (lt_of_le_of_lt hK hx)).mpr hx
  rw [(hasSum_moment_resolvent ν hK hs hz).tsum_eq, ← integral_const_mul]
  unfold realCauchyTransform
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    have hid : 1 - y * x⁻¹ = (x-y)*x⁻¹ := by field_simp
    dsimp only
    rw [hid, mul_inv_rev, inv_inv]
    simp [← mul_assoc, hx0]

#print axioms hasSum_moment_resolvent
#print axioms realCauchyTransform_eq_moment_tsum
end ProjectionChannels
