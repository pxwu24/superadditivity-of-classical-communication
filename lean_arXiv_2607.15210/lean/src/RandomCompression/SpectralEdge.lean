import RandomCompression.CauchyBernoulli
import RandomCompression.CauchyHolomorphic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace ProjectionChannels
noncomputable section

def poissonKernel (η x s : ℝ) : ℝ := η / ((x - s) ^ 2 + η ^ 2)

theorem poissonKernel_nonneg {η : ℝ} (hη : 0 < η) (x s : ℝ) :
    0 ≤ poissonKernel η x s := by
  unfold poissonKernel
  positivity

theorem poissonKernel_le_inv {η : ℝ} (hη : 0 < η) (x s : ℝ) :
    poissonKernel η x s ≤ η⁻¹ := by
  have hd : 0 < (x - s) ^ 2 + η ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη)
  unfold poissonKernel
  apply (div_le_iff₀ hd).2
  have h : η ^ 2 ≤ (x - s) ^ 2 + η ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left h (inv_pos.mpr hη).le
  have hid : η⁻¹ * η ^ 2 = η := by field_simp; ring
  rw [hid] at hmul
  exact hmul

theorem continuous_poissonKernel {η : ℝ} (hη : 0 < η) :
    Continuous (fun p : ℝ × ℝ => poissonKernel η p.1 p.2) := by
  unfold poissonKernel
  apply continuous_const.div (by fun_prop)
  intro p
  exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη))

theorem integrable_poissonKernel_prod
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {η : ℝ} (hη : 0 < η) :
    Integrable (fun p : ℝ × ℝ => poissonKernel η p.1 p.2) (μ.prod ν) := by
  apply (integrable_const η⁻¹).mono' (continuous_poissonKernel hη).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (poissonKernel_nonneg hη _ _)]
  exact poissonKernel_le_inv hη _ _

theorem integrable_poissonKernel_left
    (μ : Measure ℝ) [IsFiniteMeasure μ] {η : ℝ} (hη : 0 < η) (s : ℝ) :
    Integrable (fun x : ℝ => poissonKernel η x s) μ := by
  have hc : Continuous (fun x : ℝ => poissonKernel η x s) :=
    (continuous_poissonKernel hη).comp (continuous_id.prodMk continuous_const)
  apply (integrable_const η⁻¹).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (poissonKernel_nonneg hη _ _)]
  exact poissonKernel_le_inv hη _ _

/-- A local lower bound requiring no Stieltjes inversion theorem. -/
theorem poissonKernel_local_lower {η x s : ℝ} (hη : 0 < η)
    (hx : x ∈ Icc (s - η) (s + η)) :
    1 / (2 * η) ≤ poissonKernel η x s := by
  have hd : 0 < (x - s) ^ 2 + η ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη)
  have hdist : (x - s) ^ 2 ≤ η ^ 2 := by
    nlinarith [sq_nonneg (x - s), hx.1, hx.2]
  unfold poissonKernel
  apply (div_le_div_iff₀ (by positivity) hd).2
  nlinarith

/-- Integrating the Poisson kernel over its central window gives at least one. -/
theorem poissonKernel_window_integral {η s : ℝ} (hη : 0 < η) :
    1 ≤ ∫ x in Icc (s - η) (s + η), poissonKernel η x s := by
  have h := setIntegral_ge_of_const_le (μ := (volume : Measure ℝ))
    (c := 1 / (2 * η)) measurableSet_Icc measure_Icc_lt_top.ne
    (fun x hx => poissonKernel_local_lower hη hx)
    (integrable_poissonKernel_left (volume.restrict (Icc (s - η) (s + η))) hη s)
  rw [Real.volume_real_Icc_of_le (by linarith : s - η ≤ s + η)] at h
  have hid : (1 / (2 * η)) * (s + η - (s - η)) = 1 := by
    field_simp [ne_of_gt hη]
    ring
  rwa [hid] at h

/-- An interior interval's mass is bounded by the integrated Poisson transform.
This elementary estimate supplies the no-mass implication without importing
any Stieltjes inversion theorem. -/
theorem poisson_interval_mass_lower
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b δ η : ℝ) (hη : 0 < η) (hηδ : η ≤ δ) :
    μ.real (Icc (a + δ) (b - δ)) ≤
      ∫ x in Icc a b, ∫ s : ℝ, poissonKernel η x s ∂μ := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  have hi := integrable_poissonKernel_prod ν μ hη
  have hswap : (∫ x, ∫ s, poissonKernel η x s ∂μ ∂ν) =
      ∫ s, ∫ x, poissonKernel η x s ∂ν ∂μ := integral_integral_swap hi
  change μ.real (Icc (a + δ) (b - δ)) ≤ ∫ x, ∫ s, poissonKernel η x s ∂μ ∂ν
  rw [hswap]
  have houter : Integrable (fun s : ℝ => ∫ x : ℝ, poissonKernel η x s ∂ν) μ :=
    hi.integral_prod_right
  have hnonneg : ∀ s : ℝ, 0 ≤ ∫ x : ℝ, poissonKernel η x s ∂ν := by
    intro s
    exact integral_nonneg (fun x => poissonKernel_nonneg hη x s)
  have hlocal : ∀ s ∈ Icc (a + δ) (b - δ),
      1 ≤ ∫ x : ℝ, poissonKernel η x s ∂ν := by
    intro s hs
    apply (poissonKernel_window_integral (s := s) hη).trans
    apply setIntegral_mono_set
      (integrable_poissonKernel_left (volume.restrict (Icc a b)) hη s)
      (Eventually.of_forall (fun x => poissonKernel_nonneg hη x s))
    apply Eventually.of_forall
    intro x hx
    constructor <;> linarith [hx.1, hx.2, hs.1, hs.2]
  have hrestricted := setIntegral_ge_of_const_le (μ := μ) (c := 1)
    measurableSet_Icc (measure_ne_top _ _) hlocal houter.integrableOn
  simp only [one_mul] at hrestricted
  exact hrestricted.trans (setIntegral_le_integral houter (Eventually.of_forall hnonneg))

/-- Quantitative mass estimate from a uniform imaginary-transform bound. -/
theorem cauchy_interval_mass_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b δ η C : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (hbound : ∀ x ∈ Icc a b,
      -(cauchyTransform μ ((x : ℂ) + (η : ℂ) * Complex.I)).im ≤ C * η) :
    μ.real (Icc (a + δ) (b - δ)) ≤ (C * η) * volume.real (Icc a b) := by
  apply (poisson_interval_mass_lower μ a b δ η hη hηδ).trans
  have hi := (integrable_poissonKernel_prod (volume.restrict (Icc a b)) μ hη).integral_prod_left
  have hle : (∫ x in Icc a b, ∫ s, poissonKernel η x s ∂μ) ≤
      ∫ _x in Icc a b, C * η := by
    apply setIntegral_mono_on hi (integrable_const (C * η)) measurableSet_Icc
    intro x hx
    simpa only [cauchyTransform_neg_im μ x η (ne_of_gt hη), poissonKernel] using hbound x hx
  simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hle

/-- A Cauchy transform with a uniform linear imaginary bound has no
measure mass in any strictly interior closed interval. -/
theorem cauchy_no_mass_of_linear_imaginary_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b δ ε C : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hbound : ∀ η : ℝ, 0 < η → η < ε → ∀ x ∈ Icc a b,
      -(cauchyTransform μ ((x : ℂ) + (η : ℂ) * Complex.I)).im ≤ C * η) :
    μ (Icc (a + δ) (b - δ)) = 0 := by
  have hlim : Tendsto (fun η : ℝ => (C * η) * volume.real (Icc a b))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Continuous (fun η : ℝ => (C * η) * volume.real (Icc a b)) := by fun_prop
    simpa only [mul_zero, zero_mul] using (h.tendsto 0).mono_left (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0)
  have hzero : μ.real (Icc (a + δ) (b - δ)) ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds hδ),
      nhdsWithin_le_nhds (gt_mem_nhds hε)] with η hη hηδ hηε
    exact cauchy_interval_mass_bound μ a b δ η C hη hηδ.le (hbound η hη hηε)
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  exact le_antisymm hzero measureReal_nonneg

/-- A genuinely real-valued holomorphic continuation across a real point
forces a whole neighborhood of that point to have zero measure. -/
theorem cauchy_no_mass_holomorphic_continuation
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℂ → ℂ) (r R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball (r : ℂ) R))
    (hreal : ∀ x : ℝ, |x - r| < R → (f (x : ℂ)).im = 0)
    (hagrees : ∀ z ∈ Metric.ball (r : ℂ) R,
      0 < z.im → f z = cauchyTransform μ z) :
    ∃ ε : ℝ, 0 < ε ∧ μ (Icc (r - ε) (r + ε)) = 0 := by
  let s : Set ℂ := Metric.closedBall (r : ℂ) (R / 2)
  have hsU : s ⊆ Metric.ball (r : ℂ) R := by
    intro z hz
    change dist z (r : ℂ) ≤ R / 2 at hz
    change dist z (r : ℂ) < R
    linarith
  obtain ⟨C, hC, hbound⟩ := holomorphic_imaginary_bound_on_compact f
    (Metric.ball (r : ℂ) R) s Metric.isOpen_ball (isCompact_closedBall _ _)
    (convex_closedBall _ _) hsU hf
  have hstrip : ∀ η : ℝ, 0 < η → η < R / 8 →
      ∀ x ∈ Icc (r - R / 8) (r + R / 8),
      -(cauchyTransform μ ((x : ℂ) + (η : ℂ) * Complex.I)).im ≤ C * η := by
    intro η hη hηR x hx
    have hxabs : |x - r| ≤ R / 8 := by
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2]
    have hxnorm : ‖(x : ℂ) - (r : ℂ)‖ ≤ R / 8 := by
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hxabs
    have hxs : (x : ℂ) ∈ s := by
      change dist (x : ℂ) (r : ℂ) ≤ R / 2
      rw [dist_eq_norm]
      linarith
    have hzs : (x : ℂ) + (η : ℂ) * Complex.I ∈ s := by
      change dist ((x : ℂ) + (η : ℂ) * Complex.I) (r : ℂ) ≤ R / 2
      rw [dist_eq_norm]
      have heq : (x : ℂ) + (η : ℂ) * Complex.I - (r : ℂ) =
          ((x : ℂ) - (r : ℂ)) + (η : ℂ) * Complex.I := by ring
      rw [heq]
      apply (norm_add_le _ _).trans
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        mul_one, abs_of_pos hη]
      linarith
    have hfreal : (f (x : ℂ)).im = 0 := hreal x (by linarith)
    have him : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
    have heq := hagrees _ (hsU hzs) him
    have hb := hbound x η hxs hzs hfreal
    rw [heq, abs_of_pos hη] at hb
    exact (neg_le_abs _).trans hb
  have hz := cauchy_no_mass_of_linear_imaginary_bound μ
    (r - R / 8) (r + R / 8) (R / 16) (R / 8) C
    (by positivity) (by positivity) hstrip
  refine ⟨R / 16, by positivity, ?_⟩
  have hl : r - R / 8 + R / 16 = r - R / 16 := by ring
  have hr : r + R / 8 - R / 16 = r + R / 16 := by ring
  simpa only [hl, hr] using hz

/-- The topological support of a real measure, stated through its defining
open-neighborhood condition. -/
def realMeasureSupport (μ : Measure ℝ) : Set ℝ :=
  {r | ∀ U : Set ℝ, IsOpen U → r ∈ U → μ U ≠ 0}

/-- The Cauchy transform cannot have a real holomorphic continuation
through any point of the actual topological support. -/
theorem no_real_holomorphic_continuation_at_support
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℂ → ℂ) (r R : ℝ) (hR : 0 < R)
    (hr : r ∈ realMeasureSupport μ)
    (hf : DifferentiableOn ℂ f (Metric.ball (r : ℂ) R))
    (hreal : ∀ x : ℝ, |x - r| < R → (f (x : ℂ)).im = 0)
    (hagrees : ∀ z ∈ Metric.ball (r : ℂ) R,
      0 < z.im → f z = cauchyTransform μ z) : False := by
  obtain ⟨ε, hε, hzero⟩ := cauchy_no_mass_holomorphic_continuation μ f r R hR hf hreal hagrees
  have hopenzero : μ (Ioo (r - ε) (r + ε)) = 0 :=
    measure_mono_null Ioo_subset_Icc_self hzero
  exact hr (Ioo (r - ε) (r + ε)) isOpen_Ioo ⟨by linarith, by linarith⟩ hopenzero

end
end ProjectionChannels

