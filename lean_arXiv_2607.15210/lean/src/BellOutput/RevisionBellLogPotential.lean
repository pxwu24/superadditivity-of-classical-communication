import RandomCompression.CauchyHolomorphy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Actual measure-theoretic logarithmic potential on the left of a compact
positive spectrum. This module proves analytic facts about the integral; it
does not postulate the inverse-Cauchy identity for a free-convolution law. -/

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace RevisionBell

def logPotential (μ : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ s : ℝ, Real.log (s-z) ∂μ

theorem integrable_logPotential_kernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (m M z : ℝ) (hbound : ∀ᵐ s ∂μ, m ≤ s ∧ s ≤ M) (hz : z < m) :
    Integrable (fun s : ℝ => Real.log (s-z)) μ := by
  have hm : AEStronglyMeasurable (fun s : ℝ => Real.log (s-z)) μ :=
    (show Measurable (fun s : ℝ => Real.log (s-z)) by fun_prop).aestronglyMeasurable
  apply (integrable_const (|Real.log (m-z)| + |Real.log (M-z)|)).mono' hm
  filter_upwards [hbound] with s hs
  have hms : Real.log (m-z) ≤ Real.log (s-z) :=
    Real.log_le_log (by linarith) (by linarith)
  have hsM : Real.log (s-z) ≤ Real.log (M-z) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (Real.log (m-z))
    have := abs_nonneg (Real.log (M-z))
    linarith
  · have := le_abs_self (Real.log (M-z))
    have := abs_nonneg (Real.log (m-z))
    linarith

/-- Differentiating the genuine logarithmic potential gives the genuine real
Cauchy transform. The compact support hypotheses supply domination. -/
theorem hasDerivAt_logPotential (μ : Measure ℝ) [IsFiniteMeasure μ]
    (m M z : ℝ) (hbound : ∀ᵐ s ∂μ, m ≤ s ∧ s ≤ M) (hz : z < m) :
    HasDerivAt (logPotential μ) (ProjectionChannels.realCauchyTransform μ z) z := by
  let δ := (m-z)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun s : ℝ => Real.log (s-x)) μ := by
    intro x
    exact (show Measurable (fun s : ℝ => Real.log (s-x)) by fun_prop).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (fun s : ℝ => (z-s)⁻¹) μ :=
    (show Measurable (fun s : ℝ => (z-s)⁻¹) by fun_prop).aestronglyMeasurable
  have hnear : ∀ᵐ s ∂μ, ∀ x ∈ Metric.ball z δ, δ ≤ s-x := by
    filter_upwards [hbound] with s hs
    intro x hx
    have hx' : |x-z| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
    have hx'' := le_abs_self (x-z)
    dsimp [δ] at *
    linarith
  have hnorm : ∀ᵐ s ∂μ, ∀ x ∈ Metric.ball z δ, ‖(x-s)⁻¹‖ ≤ δ⁻¹ := by
    filter_upwards [hnear] with s hs
    intro x hx
    have hpos : 0 < s-x := hδ.trans_le (hs x hx)
    rw [Real.norm_eq_abs, abs_inv, abs_of_neg (by linarith : x-s < 0)]
    simpa only [neg_sub] using inv_anti₀ hδ (hs x hx)
  have hdiff : ∀ᵐ s ∂μ, ∀ x ∈ Metric.ball z δ,
      HasDerivAt (fun y : ℝ => Real.log (s-y)) ((x-s)⁻¹) x := by
    filter_upwards [hnear] with s hs
    intro x hx
    have hpos : 0 < s-x := hδ.trans_le (hs x hx)
    have h := (Real.hasDerivAt_log hpos.ne').comp x
      ((hasDerivAt_const x s).sub (hasDerivAt_id x))
    have hneg : -(s-x)⁻¹ = (x-s)⁻¹ := by rw [← inv_neg, neg_sub]
    simpa only [Function.comp_def, zero_sub, mul_neg, mul_one, hneg] using h
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) hδ (Eventually.of_forall hmeas)
    (integrable_logPotential_kernel μ m M z hbound hz) hdmeas hnorm
    (integrable_const δ⁻¹) hdiff).2

lemma log_kernel_normalization_bound {s M z : ℝ}
    (hs : 0 ≤ s) (hsM : s ≤ M) (hz : z < 0) :
    0 ≤ Real.log (s-z) - Real.log (-z) ∧
      Real.log (s-z) - Real.log (-z) ≤ M / (-z) := by
  have hsp : 0 < s-z := by linarith
  have hzp : 0 < -z := by linarith
  have hid : (s-z)/(-z) = 1+s/(-z) := by field_simp [hz.ne]; ring
  rw [← Real.log_div hsp.ne' hzp.ne', hid]
  have hdiv : 0 ≤ s/(-z) := div_nonneg hs hzp.le
  constructor
  · exact Real.log_nonneg (by linarith)
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1+s/(-z) by linarith)
    have hm := div_le_div_of_nonneg_right hsM hzp.le
    linarith

/-- A uniform error bound fixes the additive constant of the logarithmic
primitive: the leading term at negative infinity is `log (-z)`. -/
theorem logPotential_normalization_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M z : ℝ) (hbound : ∀ᵐ s ∂μ, 0 ≤ s ∧ s ≤ M) (hz : z < 0) :
    0 ≤ logPotential μ z - Real.log (-z) ∧
      logPotential μ z - Real.log (-z) ≤ M / (-z) := by
  have hi := integrable_logPotential_kernel μ 0 M z hbound hz
  have heq : logPotential μ z - Real.log (-z) =
      ∫ s : ℝ, Real.log (s-z) - Real.log (-z) ∂μ := by
    rw [integral_sub hi (integrable_const _)]
    simp [logPotential]
  rw [heq]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hbound] with s hs
    exact (log_kernel_normalization_bound hs.1 hs.2 hz).1
  · have hm := integral_mono_ae (hi.sub (integrable_const (Real.log (-z))))
      (integrable_const (M/(-z))) (show ∀ᵐ s ∂μ,
        Real.log (s-z)-Real.log (-z) ≤ M/(-z) by
          filter_upwards [hbound] with s hs
          exact (log_kernel_normalization_bound hs.1 hs.2 hz).2)
    simpa using hm

theorem logPotential_normalized_tendsto_atBot (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (hbound : ∀ᵐ s ∂μ, 0 ≤ s ∧ s ≤ M) :
    Tendsto (fun z => logPotential μ z - Real.log (-z)) atBot (nhds 0) := by
  have hupper : Tendsto (fun z : ℝ => M/(-z)) atBot (nhds 0) := by
    simpa only [div_eq_mul_inv, inv_neg, mul_zero, neg_zero] using
      (tendsto_inv_atBot_zero.neg.const_mul M :
        Tendsto (fun z : ℝ => M * -z⁻¹) atBot (nhds (M * -0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with z hz
    exact (logPotential_normalization_bound μ M z hbound hz).1
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with z hz
    exact (logPotential_normalization_bound μ M z hbound hz).2

/-- The Cauchy derivative and normalization at negative infinity uniquely
characterize the genuine logarithmic potential. This is the constant-fixing
argument required when integrating the inverse-Cauchy expression in (96). -/
theorem logPotential_unique_primitive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m M : ℝ) (hm : 0 ≤ m) (hbound : ∀ᵐ s ∂μ, m ≤ s ∧ s ≤ M)
    (f : ℝ → ℝ)
    (hf : ∀ z < m, HasDerivAt f (ProjectionChannels.realCauchyTransform μ z) z)
    (hnorm : Tendsto (fun z => f z - Real.log (-z)) atBot (nhds 0)) :
    ∀ z < m, f z = logPotential μ z := by
  have hg : ∀ z < m, HasDerivAt (logPotential μ)
      (ProjectionChannels.realCauchyTransform μ z) z :=
    fun z hz => hasDerivAt_logPotential μ m M z hbound hz
  obtain ⟨c,hc⟩ := isOpen_Iio.exists_eq_add_of_deriv_eq
    (convex_Iio m).isPreconnected
    (fun z hz => (hf z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hg z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hf z hz).deriv.trans (hg z hz).deriv.symm)
  have hb0 : ∀ᵐ s ∂μ, 0 ≤ s ∧ s ≤ M := by
    filter_upwards [hbound] with s hs
    exact ⟨hm.trans hs.1,hs.2⟩
  have hlim : Tendsto (fun z => f z-logPotential μ z) atBot (nhds 0) := by
    have h := hnorm.sub (logPotential_normalized_tendsto_atBot μ M hb0)
    simpa only [sub_sub_sub_cancel_right, sub_self] using h
  have hevent : (fun z => f z-logPotential μ z) =ᶠ[atBot] (fun _ => c) := by
    filter_upwards [eventually_lt_atBot m] with z hz
    rw [hc hz]
    ring
  have hc0 : c=0 := tendsto_nhds_unique tendsto_const_nhds (hlim.congr' hevent)
  intro z hz
  simpa only [hc0, add_zero] using hc hz

end RevisionBell
