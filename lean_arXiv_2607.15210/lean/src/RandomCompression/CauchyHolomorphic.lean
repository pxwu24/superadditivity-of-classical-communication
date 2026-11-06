import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# The local imaginary-part estimate for real holomorphic continuations

The bound is derived from analyticity and compactness, not assumed as a
research-theorem input. The result is phrased on a compact convex subset
of the continuation domain so it applies to a small disk or rectangle.
-/

namespace ProjectionChannels

/-- An analytic function which is real on the relevant real points has an
imaginary part bounded linearly in height, uniformly on a compact convex set. -/
theorem analytic_imaginary_bound_on_compact
    (f : ℂ → ℂ) (s : Set ℂ) (hs : IsCompact s) (hc : Convex ℝ s)
    (hf : AnalyticOnNhd ℂ f s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x η : ℝ,
      (x : ℂ) ∈ s → (x : ℂ) + (η : ℂ) * Complex.I ∈ s →
      (f (x : ℂ)).im = 0 →
      |(f ((x : ℂ) + (η : ℂ) * Complex.I)).im| ≤ C * |η| := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf.deriv.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x η hx hη hreal
  have hd : ∀ z ∈ s, DifferentiableAt ℂ f z :=
    fun z hz => (hf z hz).differentiableAt
  have hb : ∀ z ∈ s, ‖deriv f z‖ ≤ max C 0 :=
    fun z hz => (hC z hz).trans (le_max_left _ _)
  have hm := hc.norm_image_sub_le_of_norm_deriv_le hd hb hx hη
  have him := Complex.abs_im_le_norm
    (f ((x : ℂ) + (η : ℂ) * Complex.I) - f (x : ℂ))
  simp only [Complex.sub_im, hreal, sub_zero] at him
  refine him.trans ?_
  simpa only [add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one] using hm

/-- The preceding bound follows from ordinary holomorphicity on an open
neighborhood of a compact convex set. -/
theorem holomorphic_imaginary_bound_on_compact
    (f : ℂ → ℂ) (U s : Set ℂ) (hU : IsOpen U)
    (hs : IsCompact s) (hc : Convex ℝ s) (hsU : s ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x η : ℝ,
      (x : ℂ) ∈ s → (x : ℂ) + (η : ℂ) * Complex.I ∈ s →
      (f (x : ℂ)).im = 0 →
      |(f ((x : ℂ) + (η : ℂ) * Complex.I)).im| ≤ C * |η| := by
  apply analytic_imaginary_bound_on_compact f s hs hc
  exact (hf.analyticOnNhd hU).mono hsU

end ProjectionChannels

