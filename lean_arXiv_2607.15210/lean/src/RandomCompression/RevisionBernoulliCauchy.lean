import RandomCompression.CompressionEndpointGlue
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The actual Cauchy transform on the right of a probability measure

These lemmas concern the Bochner integral of an actual probability measure.
They supply the derivative, range, and finite endpoint limit used in Step 4 of
Lemma A.1. No free-convolution identity or spectral-edge formula is assumed.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section
namespace ProjectionChannels

/-- Differentiation of the real Cauchy transform to the right of the support. -/
theorem hasDerivAt_realCauchyTransform_right
    (μ : Measure ℝ) [IsFiniteMeasure μ] (r x : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r) (hx : r < x) :
    HasDerivAt (realCauchyTransform μ)
      (∫ s : ℝ, -((x - s) ^ 2)⁻¹ ∂μ) x := by
  have hd := hasDerivAt_cauchyTransform_of_separation μ (x : ℂ)
    ((x-r)/2) (by linarith) (by
      filter_upwards [hbound] with s hs
      simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith : 0 < x-s)]
      linarith)
  have h := hd.real_of_complex
  simpa only [cauchyTransform_ofReal, Complex.ofReal_re,
    ← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    ← Complex.ofReal_neg, integral_complex_ofReal] using h

/-- The derivative is strictly negative for a probability measure. -/
theorem realCauchyTransform_deriv_neg
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r x : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r) (hx : r < x) :
    deriv (realCauchyTransform μ) x < 0 := by
  rw [(hasDerivAt_realCauchyTransform_right μ r x hbound hx).deriv,
    integral_neg, neg_neg_iff_pos]
  have hi : Integrable (fun s : ℝ => ((x-s)^2)⁻¹) μ := by
    apply (integrable_const (((x-r)^2)⁻¹)).mono'
      (show AEStronglyMeasurable (fun s : ℝ => ((x-s)^2)⁻¹) μ from
        (show Measurable (fun s : ℝ => ((x-s)^2)⁻¹) by fun_prop).aestronglyMeasurable)
    filter_upwards [hbound] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    simpa only [one_div] using one_div_le_one_div_of_le
      (sq_pos_of_pos (sub_pos.mpr hx))
      (pow_le_pow_left₀ (sub_pos.mpr hx).le (by linarith : x-r ≤ x-s) 2)
  have hp : ∀ᵐ s : ℝ ∂μ, 0 < ((x-s)^2)⁻¹ := by
    filter_upwards [hbound] with s hs
    exact inv_pos.mpr (sq_pos_of_pos (by linarith))
  have hn : 0 ≤ᵐ[μ] (fun s : ℝ => ((x-s)^2)⁻¹) := hp.mono (fun _ h => h.le)
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro heq
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp heq.symm
  obtain ⟨s, hs, hsz⟩ := (hp.and hz).exists
  exact (ne_of_gt hs) hsz

/-- Continuity needed for the inverse branch, established for the actual integral. -/
theorem continuousOn_realCauchyTransform_right
    (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r) :
    ContinuousOn (realCauchyTransform μ) (Ioi r) := by
  intro x hx
  exact (hasDerivAt_realCauchyTransform_right μ r x hbound hx).continuousAt.continuousWithinAt

/-- Every positive value below a value of the Cauchy transform is attained.
This uses decay at infinity and the intermediate value theorem. -/
theorem realCauchyTransform_exists_eq_of_lt
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r x w : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r) (hx : r < x)
    (hw : 0 < w) (hwx : w < realCauchyTransform μ x) :
    ∃ z, r < z ∧ realCauchyTransform μ z = w := by
  have he : ∀ᶠ z in atTop, realCauchyTransform μ z < w :=
    (realCauchyTransform_tendsto_zero μ r hbound).eventually (Iio_mem_nhds hw)
  obtain ⟨z, hz, hzx⟩ := (he.and (eventually_gt_atTop x)).exists
  have hc : ContinuousOn (realCauchyTransform μ) (Icc x z) :=
    (continuousOn_realCauchyTransform_right μ r hbound).mono
      (fun y hy => hx.trans_le hy.1)
  obtain ⟨y, hy, hval⟩ := intermediate_value_Icc' hzx.le hc ⟨hz.le, hwx.le⟩
  exact ⟨y, hx.trans_le hy.1, hval⟩

/-- When the right branch is bounded, its range is the open interval between
zero and its supremum. In particular its upper endpoint is not attained. -/
theorem realCauchyTransform_range_bounded
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r)
    (hbdd : BddAbove (realCauchyTransform μ '' Ioi r)) :
    realCauchyTransform μ '' Ioi r =
      Ioo 0 (sSup (realCauchyTransform μ '' Ioi r)) := by
  let S := realCauchyTransform μ '' Ioi r
  have hsne : S.Nonempty := ⟨_, ⟨r+1, by simp, rfl⟩⟩
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨realCauchyTransform_pos μ r x hbound hx, ?_⟩
    have hx' : r < x := hx
    have hm : r < (r+x)/2 := by linarith
    have hmx : (r+x)/2 < x := by linarith
    exact ((realCauchyTransform_strictAntiOn μ r hbound) hm hx hmx).trans_le
      (le_csSup hbdd ⟨(r+x)/2, hm, rfl⟩)
  · intro hw
    obtain ⟨v, hv, hwv⟩ := exists_lt_of_lt_csSup hsne hw.2
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨z, hz, heq⟩ := realCauchyTransform_exists_eq_of_lt μ r x w hbound hx hw.1 hwv
    exact ⟨z, hz, heq⟩

/-- If the right branch is unbounded, its range is the whole positive half-line. -/
theorem realCauchyTransform_range_unbounded
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r)
    (hbdd : ¬ BddAbove (realCauchyTransform μ '' Ioi r)) :
    realCauchyTransform μ '' Ioi r = Ioi 0 := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact realCauchyTransform_pos μ r x hbound hx
  · intro hw
    obtain ⟨v, hv, hwv⟩ := not_bddAbove_iff.mp hbdd w
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨z, hz, heq⟩ := realCauchyTransform_exists_eq_of_lt μ r x w hbound hx hw hwv
    exact ⟨z, hz, heq⟩

/-- The finite upper endpoint of the right Cauchy branch is its actual limit
at the support edge from above. -/
theorem realCauchyTransform_tendsto_right_edge_bounded
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r)
    (hbdd : BddAbove (realCauchyTransform μ '' Ioi r)) :
    Tendsto (realCauchyTransform μ) (𝓝[>] r)
      (𝓝 (sSup (realCauchyTransform μ '' Ioi r))) := by
  have hsne : (realCauchyTransform μ '' Ioi r).Nonempty :=
    ⟨_, ⟨r+1, by simp, rfl⟩⟩
  apply tendsto_order.2
  constructor
  · intro b hb
    obtain ⟨v, ⟨x, hx, rfl⟩, hbv⟩ := exists_lt_of_lt_csSup hsne hb
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with y hy hyx
    exact hbv.trans ((realCauchyTransform_strictAntiOn μ r hbound) hy hx hyx)
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (le_csSup hbdd ⟨x, hx, rfl⟩).trans_lt hb

/-- The alternative endpoint is infinite, also as an actual filter limit. -/
theorem realCauchyTransform_tendsto_right_edge_unbounded
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r)
    (hbdd : ¬ BddAbove (realCauchyTransform μ '' Ioi r)) :
    Tendsto (realCauchyTransform μ) (𝓝[>] r) atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨v, ⟨x, hx, rfl⟩, hbv⟩ := not_bddAbove_iff.mp hbdd b
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with y hy hyx
  exact (hbv.trans ((realCauchyTransform_strictAntiOn μ r hbound) hy hx hyx)).le

end ProjectionChannels
