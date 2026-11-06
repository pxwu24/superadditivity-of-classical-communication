import RandomCompression.CauchyLocalInverse
import RandomCompression.CauchyHolomorphy
import Mathlib.Analysis.Convex.Topology

/-!
# The finite-endpoint obstruction for an actual Cauchy transform

This file supplies analytic glue in Step 4 of the random-compression proof.
Agreement of a holomorphic function with the actual Cauchy transform on the
real interval to the right of the support is propagated into the upper
half-disc. This is then incompatible with membership in the measure support.

No free-convolution law or R-transform addition theorem is introduced here.
The final theorem has an explicit local inverse-branch hypothesis. Applying
it to the free-convolution law still requires proving that hypothesis.
-/

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

noncomputable section
namespace ProjectionChannels

/-- Real agreement to the right of a support bound propagates to the upper
half-disc by the analytic identity theorem. -/
theorem cauchy_agreement_upper_of_real_right
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℂ → ℂ) (r R : ℝ) (hR : 0 < R)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.ball (r : ℂ) R))
    (hreal : ∀ x : ℝ, r < x → x < r + R →
      f (x : ℂ) = cauchyTransform μ (x : ℂ)) :
    ∀ z ∈ Metric.ball (r : ℂ) R, 0 < z.im →
      f z = cauchyTransform μ z := by
  let U : Set ℂ := Metric.ball (r : ℂ) R ∩ {z : ℂ | 0 < z.im}
  let V : Set ℂ := Metric.ball (r : ℂ) R ∩ {z : ℂ | r < z.re}
  have hUopen : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hVopen : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const Complex.continuous_re)
  have hUconv : Convex ℝ U := (convex_ball _ _).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)
  have hVconv : Convex ℝ V := (convex_ball _ _).inter
    ((convex_Ioi r).linear_preimage Complex.reLm)
  let zc : ℂ := (r : ℂ) + (R / 4 : ℝ) + (R / 4 : ℝ) * Complex.I
  have hzcball : zc ∈ Metric.ball (r : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hzceq : zc - (r : ℂ) = (R / 4 : ℝ) + (R / 4 : ℝ) * Complex.I := by
      dsimp [zc]
      ring
    rw [hzceq]
    apply (norm_add_le _ _).trans_lt
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_pos (by positivity : 0 < R / 4)]
    linarith
  have hzcU : zc ∈ U := ⟨hzcball, by dsimp [zc]; simp; linarith⟩
  have hzcV : zc ∈ V := ⟨hzcball, by dsimp [zc]; simp; linarith⟩
  have hconnected : IsPreconnected (U ∪ V) :=
    IsPreconnected.union zc hzcU hzcV hUconv.isPreconnected hVconv.isPreconnected
  have hfg : AnalyticOnNhd ℂ f (U ∪ V) := by
    apply (hf.analyticOnNhd Metric.isOpen_ball).mono
    intro z hz
    exact hz.elim And.left And.left
  have hgg : AnalyticOnNhd ℂ (cauchyTransform μ) (U ∪ V) := by
    apply DifferentiableOn.analyticOnNhd _ (hUopen.union hVopen)
    intro z hz
    rcases hz with hz | hz
    · exact (differentiableAt_cauchyTransform_off_real μ z (ne_of_gt hz.2)).differentiableWithinAt
    · exact (differentiableAt_cauchyTransform_right μ r hbound z hz.2).differentiableWithinAt
  let x₀ : ℝ := r + R / 2
  have hx₀ : (x₀ : ℂ) ∈ U ∪ V := by
    right
    refine ⟨?_, ?_⟩
    · change dist (x₀ : ℂ) (r : ℂ) < R
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      dsimp [x₀]
      rw [add_sub_cancel_left, abs_of_pos (by positivity : 0 < R / 2)]
      linarith
    · change r < x₀
      dsimp [x₀]
      linarith
  have hclosure : (x₀ : ℂ) ∈ closure
      ({z | f z = cauchyTransform μ z} \ {(x₀ : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min ε (R / 2) / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ < ε := by
      have h := min_le_left ε (R / 2)
      dsimp [δ]
      linarith
    have hδR : δ < R / 2 := by
      have h := min_le_right ε (R / 2)
      dsimp [δ]
      linarith
    refine ⟨((x₀ + δ : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · exact hreal (x₀ + δ) (by dsimp [x₀]; linarith) (by dsimp [x₀]; linarith)
    · simp only [Set.mem_singleton_iff, Complex.ofReal_inj]
      linarith
    · rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simpa only [sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg, abs_of_pos hδ] using hδε
  have heq := hfg.eqOn_of_preconnected_of_mem_closure hgg hconnected hx₀ hclosure
  intro z hz him
  exact heq (Or.inl ⟨hz, him⟩)

/-- A real holomorphic function cannot agree with the actual Cauchy
transform on a right interval next to a point of the measure support. -/
theorem no_real_holomorphic_right_continuation_at_support
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℂ → ℂ) (r R : ℝ) (hR : 0 < R)
    (hr : r ∈ realMeasureSupport μ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.ball (r : ℂ) R))
    (hreal : ∀ x : ℝ, |x - r| < R → (f (x : ℂ)).im = 0)
    (hagrees : ∀ x : ℝ, r < x → x < r + R →
      f (x : ℂ) = cauchyTransform μ (x : ℂ)) : False := by
  exact no_real_holomorphic_continuation_at_support μ f r R hR hr hf hreal
    (cauchy_agreement_upper_of_real_right μ f r R hR hbound hf hagrees)

/-- At a finite endpoint of an inverse Cauchy branch, its derivative
vanishes. The inverse relation is required only eventually as real arguments
approach the right edge from above. Neither an assumed spectral-edge formula
nor an assumed holomorphic continuation is used. -/
theorem inverse_cauchy_finite_endpoint_deriv_eq_zero
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (K : ℂ → ℂ) (r w : ℝ)
    (hr : r ∈ realMeasureSupport μ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r)
    (hK : AnalyticAt ℂ K (w : ℂ))
    (hvalue : K (w : ℂ) = (r : ℂ))
    (hreflect : ∀ᶠ z in 𝓝 (w : ℂ), K (conj z) = conj (K z))
    (hG : Tendsto (realCauchyTransform μ) (𝓝[>] r) (𝓝 w))
    (hbranch : ∀ᶠ x in 𝓝[>] r,
      K (realCauchyTransform μ x : ℂ) = (x : ℂ)) :
    deriv K (w : ℂ) = 0 := by
  by_contra hd
  obtain ⟨f, R, hR, _hfvalue, hf, hreal, _hright, hleft⟩ :=
    exists_real_holomorphic_local_inverse K w r hK hd hvalue hreflect
  have hGC : Tendsto (fun x : ℝ => (realCauchyTransform μ x : ℂ))
      (𝓝[>] r) (𝓝 (w : ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto.comp hG
  have hagrees : ∀ᶠ x : ℝ in 𝓝[>] r,
      f (x : ℂ) = cauchyTransform μ (x : ℂ) := by
    filter_upwards [hbranch, hGC.eventually hleft] with x hx hxleft
    rw [cauchyTransform_ofReal, ← hx]
    exact hxleft
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhdsWithin_iff.mp hagrees
  let R' : ℝ := min R ε / 2
  have hR' : 0 < R' := by dsimp [R']; positivity
  have hR'R : R' < R := by
    have h := min_le_left R ε
    dsimp [R']
    linarith
  have hR'ε : R' < ε := by
    have h := min_le_right R ε
    dsimp [R']
    linarith
  apply no_real_holomorphic_right_continuation_at_support μ f r R' hR' hr hbound
  · exact hf.mono (Metric.ball_subset_ball hR'R.le)
  · intro x hx
    exact hreal x (hx.trans hR'R)
  · intro x hx hxR
    apply hεball
    refine ⟨?_, hx⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hx)]
    linarith

end ProjectionChannels
