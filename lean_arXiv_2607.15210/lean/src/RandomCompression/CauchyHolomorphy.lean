import RandomCompression.CauchyBernoulli
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv

open MeasureTheory Filter Set
open scoped Topology
namespace ProjectionChannels
noncomputable section

/-- Differentiation of the genuine measure Cauchy transform under a uniform
positive separation from the measure's essential support. -/
theorem hasDerivAt_cauchyTransform_of_separation
    (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ᵐ s : ℝ ∂μ, 2 * δ ≤ ‖z - (s : ℂ)‖) :
    HasDerivAt (cauchyTransform μ)
      (∫ s : ℝ, -((z - (s : ℂ)) ^ 2)⁻¹ ∂μ) z := by
  have hmeas : ∀ x : ℂ, AEStronglyMeasurable
      (fun s : ℝ => (x - (s : ℂ))⁻¹) μ := by
    intro x
    exact (show Measurable (fun s : ℝ => (x - (s : ℂ))⁻¹) by fun_prop).aestronglyMeasurable
  have hint : Integrable (fun s : ℝ => (z - (s : ℂ))⁻¹) μ := by
    apply (integrable_const ((2 * δ)⁻¹)).mono' (hmeas z)
    filter_upwards [hsep] with s hs
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 2 * δ) hs
  have hnear : ∀ᵐ s : ℝ ∂μ, ∀ x ∈ Metric.ball z δ, δ ≤ ‖x - (s : ℂ)‖ := by
    filter_upwards [hsep] with s hs
    intro x hx
    have hnorm : ‖z - x‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
    have htri := norm_sub_le_norm_sub_add_norm_sub z x (s : ℂ)
    linarith
  have hdmeas : AEStronglyMeasurable (fun s : ℝ => -((z - (s : ℂ)) ^ 2)⁻¹) μ := by
    exact (show Measurable (fun s : ℝ => -((z - (s : ℂ)) ^ 2)⁻¹) by fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ s : ℝ ∂μ, ∀ x ∈ Metric.ball z δ,
      ‖-((x - (s : ℂ)) ^ 2)⁻¹‖ ≤ (δ ^ 2)⁻¹ := by
    filter_upwards [hnear] with s hs
    intro x hx
    simp only [norm_neg, norm_inv, norm_pow]
    simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hδ)
      (pow_le_pow_left₀ hδ.le (hs x hx) 2)
  have hdiff : ∀ᵐ s : ℝ ∂μ, ∀ x ∈ Metric.ball z δ,
      HasDerivAt (fun y : ℂ => (y - (s : ℂ))⁻¹) (-((x - (s : ℂ)) ^ 2)⁻¹) x := by
    filter_upwards [hnear] with s hs
    intro x hx
    have hneq : x - (s : ℂ) ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hs x hx))
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_inv hneq).comp x ((hasDerivAt_id' x).sub_const (s : ℂ))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) hδ (Eventually.of_forall hmeas) hint hdmeas hbound
    (integrable_const ((δ ^ 2)⁻¹)) hdiff).2

/-- Holomorphy off the real axis, proved for the actual integral. -/
theorem differentiableAt_cauchyTransform_off_real
    (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℂ) (hz : z.im ≠ 0) :
    DifferentiableAt ℂ (cauchyTransform μ) z := by
  have hδ : 0 < |z.im| / 2 := by positivity
  apply (hasDerivAt_cauchyTransform_of_separation μ z (|z.im| / 2) hδ _).differentiableAt
  apply Eventually.of_forall
  intro s
  have h := Complex.abs_im_le_norm (z - (s : ℂ))
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using h

/-- Holomorphy to the right of an essential support bound. -/
theorem differentiableAt_cauchyTransform_right
    (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r) (z : ℂ) (hz : r < z.re) :
    DifferentiableAt ℂ (cauchyTransform μ) z := by
  have hδ : 0 < (z.re - r) / 2 := by linarith
  apply (hasDerivAt_cauchyTransform_of_separation μ z ((z.re - r) / 2) hδ _).differentiableAt
  filter_upwards [hbound] with s hs
  have h := Complex.abs_re_le_norm (z - (s : ℂ))
  have hreal : (z - (s : ℂ)).re = z.re - s := by simp
  rw [hreal, abs_of_nonneg (by linarith : 0 ≤ z.re - s)] at h
  linarith

theorem differentiableOn_cauchyTransform_upper
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    DifferentiableOn ℂ (cauchyTransform μ) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (differentiableAt_cauchyTransform_off_real μ z (ne_of_gt hz)).differentiableWithinAt

theorem differentiableOn_cauchyTransform_right
    (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r) :
    DifferentiableOn ℂ (cauchyTransform μ) {z : ℂ | r < z.re} := by
  intro z hz
  exact (differentiableAt_cauchyTransform_right μ r hbound z hz).differentiableWithinAt

end
end ProjectionChannels

