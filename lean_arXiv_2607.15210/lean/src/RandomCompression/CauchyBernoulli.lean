import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Actual Bernoulli measures and Cauchy transforms

The Cauchy transform below is the Bochner integral against a genuine measure.
No free-probability law, asymptotic convergence, or inversion theorem is assumed.
-/

open MeasureTheory
open scoped ENNReal

namespace ProjectionChannels

noncomputable section

/-- The two-point Bernoulli measure, a probability measure for `0 ≤ t ≤ 1`. -/
def bernoulliMeasure (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - t) • Measure.dirac 0 + ENNReal.ofReal t • Measure.dirac 1

theorem bernoulliMeasure_isProbability {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure t) := by
  constructor
  simp only [bernoulliMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht1) ht0]
  norm_num

/-- The measure is concentrated on the actual two atoms. -/
theorem ae_bernoulliMeasure_zero_or_one (t : ℝ) :
    ∀ᵐ x ∂bernoulliMeasure t, x = 0 ∨ x = 1 := by
  rw [bernoulliMeasure, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    simp [ae_dirac_eq]
  · apply Measure.ae_smul_measure
    simp [ae_dirac_eq]

theorem bernoulliMeasure_mass_zero (t : ℝ) :
    bernoulliMeasure t {0} = ENNReal.ofReal (1 - t) := by
  simp [bernoulliMeasure]

theorem bernoulliMeasure_mass_one (t : ℝ) :
    bernoulliMeasure t {1} = ENNReal.ofReal t := by
  simp [bernoulliMeasure]

/-- Every complex-valued function is integrable against this finite atomic measure. -/
theorem integrable_bernoulliMeasure (t : ℝ) (f : ℝ → ℂ) :
    Integrable f (bernoulliMeasure t) := by
  exact (integrable_dirac.smul_measure ENNReal.ofReal_ne_top).add_measure
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)

/-- Integration against the actual two-point law. -/
theorem integral_bernoulliMeasure {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (f : ℝ → ℂ) :
    (∫ x, f x ∂bernoulliMeasure t) = (1 - t) • f 0 + t • f 1 := by
  unfold bernoulliMeasure
  rw [integral_add_measure
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)]
  simp [ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal (sub_nonneg.mpr ht1)]

/-- Every strictly positive integer moment of the Bernoulli law equals its parameter. -/
theorem bernoulliMeasure_moment {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (m : ℕ) (hm : m ≠ 0) :
    (∫ x : ℝ, (x : ℂ) ^ m ∂bernoulliMeasure t) = (t : ℂ) := by
  rw [integral_bernoulliMeasure ht0 ht1]
  simp [hm, Complex.real_smul]

/-- Cauchy transform with the manuscript's sign convention. -/
def cauchyTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ

/-- The real Cauchy transform on a component outside the measure's support. -/
def realCauchyTransform (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, (x - y)⁻¹ ∂μ

/-- On real arguments, the complex integral agrees with the real integral. -/
theorem cauchyTransform_ofReal (μ : Measure ℝ) (x : ℝ) :
    cauchyTransform μ (x : ℂ) = (realCauchyTransform μ x : ℂ) := by
  simp only [cauchyTransform, realCauchyTransform, ← Complex.ofReal_sub,
    ← Complex.ofReal_inv, integral_complex_ofReal]

/-- The complex resolvent kernel is integrable off the real axis. -/
theorem integrable_cauchyKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (z : ℂ) (hz : z.im ≠ 0) :
    Integrable (fun y : ℝ => (z - (y : ℂ))⁻¹) μ := by
  have hm : AEStronglyMeasurable (fun y : ℝ => (z - (y : ℂ))⁻¹) μ :=
    (show Measurable (fun y : ℝ => (z - (y : ℂ))⁻¹) by fun_prop).aestronglyMeasurable
  apply (integrable_const (|z.im|⁻¹)).mono' hm
  filter_upwards [] with y
  have him : |z.im| ≤ ‖z - (y : ℂ)‖ := by
    simpa using Complex.abs_im_le_norm (z - (y : ℂ))
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (abs_pos.mpr hz) him

/-- The negative imaginary part of the actual Cauchy transform is the
Poisson-kernel integral. -/
theorem cauchyTransform_neg_im (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x η : ℝ) (hη : η ≠ 0) :
    -(cauchyTransform μ ((x : ℂ) + (η : ℂ) * Complex.I)).im =
      ∫ y : ℝ, η / ((x - y) ^ 2 + η ^ 2) ∂μ := by
  have hi := integrable_cauchyKernel μ ((x : ℂ) + (η : ℂ) * Complex.I)
    (by simpa using hη)
  have him : (∫ y : ℝ, (((x : ℂ) + (η : ℂ) * Complex.I - (y : ℂ))⁻¹).im ∂μ) =
      (∫ y : ℝ, ((x : ℂ) + (η : ℂ) * Complex.I - (y : ℂ))⁻¹ ∂μ).im :=
    integral_im hi
  rw [cauchyTransform, ← him, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [Complex.inv_im, Complex.normSq_apply, pow_two, neg_div]

/-- A finite measure supported to the left has an integrable resolvent kernel
at every real point strictly to the right of that bound. -/
theorem integrable_realCauchyKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (r x : ℝ) (hbound : ∀ᵐ y ∂μ, y ≤ r) (hx : r < x) :
    Integrable (fun y : ℝ => (x - y)⁻¹) μ := by
  have hm : AEStronglyMeasurable (fun y : ℝ => (x - y)⁻¹) μ :=
    (show Measurable (fun y : ℝ => (x - y)⁻¹) by fun_prop).aestronglyMeasurable
  apply (integrable_const ((x - r)⁻¹)).mono' hm
  filter_upwards [hbound] with y hy
  have hxy : 0 < x - y := by linarith
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxy)]
  simpa only [one_div] using
    one_div_le_one_div_of_le (show 0 < x - r by linarith) (show x - r ≤ x - y by linarith)

/-- The real Cauchy transform of a probability measure is positive to the
right of an almost-sure upper bound on its support. -/
theorem realCauchyTransform_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r x : ℝ) (hbound : ∀ᵐ y ∂μ, y ≤ r) (hx : r < x) :
    0 < realCauchyTransform μ x := by
  have hp : ∀ᵐ y ∂μ, 0 < (x - y)⁻¹ := by
    filter_upwards [hbound] with y hy
    apply inv_pos.mpr
    linarith
  have hn : 0 ≤ᵐ[μ] (fun y : ℝ => (x - y)⁻¹) := by
    filter_upwards [hp] with y hy
    exact hy.le
  have hi := integrable_realCauchyKernel μ r x hbound hx
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro heq
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp heq.symm
  obtain ⟨y, hyp, hyz⟩ := (hp.and hz).exists
  exact (ne_of_gt hyp) hyz

/-- A quantitative bound for the right-hand Cauchy transform. -/
theorem realCauchyTransform_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r x : ℝ) (hbound : ∀ᵐ y ∂μ, y ≤ r) (hx : r < x) :
    realCauchyTransform μ x ≤ (x - r)⁻¹ := by
  have hi := integrable_realCauchyKernel μ r x hbound hx
  have hle : (fun y : ℝ => (x - y)⁻¹) ≤ᵐ[μ] (fun _ => (x - r)⁻¹) := by
    filter_upwards [hbound] with y hy
    simpa only [one_div] using
      one_div_le_one_div_of_le (show 0 < x - r by linarith) (show x - r ≤ x - y by linarith)
  have h := integral_mono_ae hi (integrable_const ((x - r)⁻¹)) hle
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

/-- The right-hand Cauchy transform tends to zero at positive infinity. -/
theorem realCauchyTransform_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r : ℝ) (hbound : ∀ᵐ y ∂μ, y ≤ r) :
    Filter.Tendsto (realCauchyTransform μ) Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun x : ℝ => x - r) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b + r)] with x hx
    linarith
  apply squeeze_zero' (g := fun x => (x - r)⁻¹) ?_ ?_
    (tendsto_inv_atTop_zero.comp hshift)
  · filter_upwards [Filter.eventually_gt_atTop r] with x hx
    exact (realCauchyTransform_pos μ r x hbound hx).le
  · filter_upwards [Filter.eventually_gt_atTop r] with x hx
    exact realCauchyTransform_le μ r x hbound hx

/-- Strict decrease of the actual real Cauchy transform on the right-hand
component. This is not an assumption about an inverse branch. -/
theorem realCauchyTransform_strictAntiOn (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r : ℝ) (hbound : ∀ᵐ y ∂μ, y ≤ r) :
    StrictAntiOn (realCauchyTransform μ) (Set.Ioi r) := by
  intro x hx z hz hxz
  simp only [Set.mem_Ioi] at hx hz
  have hiX := integrable_realCauchyKernel μ r x hbound hx
  have hiZ := integrable_realCauchyKernel μ r z hbound hz
  have hlt : ∀ᵐ y ∂μ, (z - y)⁻¹ < (x - y)⁻¹ := by
    filter_upwards [hbound] with y hy
    simpa only [one_div] using
      one_div_lt_one_div_of_lt (show 0 < x - y by linarith) (show x - y < z - y by linarith)
  have hle : (fun y : ℝ => (z - y)⁻¹) ≤ᵐ[μ] (fun y : ℝ => (x - y)⁻¹) := by
    filter_upwards [hlt] with y hy
    exact hy.le
  apply lt_of_le_of_ne (integral_mono_ae hiZ hiX hle)
  intro heq
  have hEq := (integral_eq_iff_of_ae_le hiZ hiX hle).mp heq
  obtain ⟨y, hyl, hye⟩ := (hlt.and hEq).exists
  exact (ne_of_lt hyl) hye

/-- Dilation of an actual measure gives the standard Cauchy-transform identity. -/
theorem cauchyTransform_dilation (μ : Measure ℝ) (c : ℝ) (hc : c ≠ 0) (z : ℂ) :
    cauchyTransform (Measure.map (fun x : ℝ => c * x) μ) z =
      (c : ℂ)⁻¹ * cauchyTransform μ (z / (c : ℂ)) := by
  unfold cauchyTransform
  have hm : StronglyMeasurable (fun x : ℝ => (z - (x : ℂ))⁻¹) :=
    (show Measurable (fun x : ℝ => (z - (x : ℂ))⁻¹) by fun_prop).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable (by fun_prop) hm]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  have h : z - (c : ℂ) * (x : ℂ) = (c : ℂ) * (z / (c : ℂ) - (x : ℂ)) := by
    field_simp
  rw [h, mul_inv_rev]
  ring

theorem cauchyTransform_bernoulli {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (z : ℂ) :
    cauchyTransform (bernoulliMeasure t) z =
      ((1 - t : ℝ) : ℂ) / z + (t : ℂ) / (z - 1) := by
  rw [cauchyTransform, integral_bernoulliMeasure ht0 ht1]
  simp [Complex.real_smul, div_eq_mul_inv]

/-- The rational formula for the Bernoulli Cauchy transform away from its atoms. -/
theorem cauchyTransform_bernoulli_rational {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    cauchyTransform (bernoulliMeasure t) z =
      (z - (1 - (t : ℂ))) / (z * (z - 1)) := by
  rw [cauchyTransform_bernoulli ht0 ht1]
  push_cast
  field_simp [hz0, sub_ne_zero.mpr hz1]
  ring

/-- The polynomial relation inverted in the manuscript, for the actual measure. -/
theorem cauchyTransform_bernoulli_quadratic {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    let w := cauchyTransform (bernoulliMeasure t) z
    w * z ^ 2 - (1 + w) * z + (1 - (t : ℂ)) = 0 := by
  dsimp
  rw [cauchyTransform_bernoulli_rational ht0 ht1 z hz0 hz1]
  field_simp [hz0, sub_ne_zero.mpr hz1]
  ring

end
end ProjectionChannels

