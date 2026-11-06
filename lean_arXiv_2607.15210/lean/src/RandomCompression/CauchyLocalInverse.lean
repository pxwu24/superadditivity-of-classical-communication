import RandomCompression.SpectralEdge
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

noncomputable section

namespace ProjectionChannels

/-- The complex inverse-function theorem plus local conjugation symmetry gives
a holomorphic inverse which is real on a real neighborhood. Real-valuedness
and the inverse identities are proved, rather than supplied as hypotheses. -/
theorem exists_real_holomorphic_local_inverse
    (K : ℂ → ℂ) (w r : ℝ) (hK : AnalyticAt ℂ K (w : ℂ))
    (hd : deriv K (w : ℂ) ≠ 0) (hvalue : K (w : ℂ) = (r : ℂ))
    (hreflect : ∀ᶠ z in 𝓝 (w : ℂ), K (conj z) = conj (K z)) :
    ∃ f : ℂ → ℂ, ∃ R : ℝ, 0 < R ∧
      f (r : ℂ) = (w : ℂ) ∧
      DifferentiableOn ℂ f (Metric.ball (r : ℂ) R) ∧
      (∀ x : ℝ, |x - r| < R → (f (x : ℂ)).im = 0) ∧
      (∀ z ∈ Metric.ball (r : ℂ) R, K (f z) = z) ∧
      (∀ᶠ z in 𝓝 (w : ℂ), f (K z) = z) := by
  obtain ⟨p, hp⟩ := hK
  have hs : HasStrictDerivAt K (deriv K (w : ℂ)) (w : ℂ) := by
    rw [hp.deriv]
    exact hp.hasStrictDerivAt
  let he := hs.hasStrictFDerivAt_equiv hd
  let e := he.toPartialHomeomorph K
  let f : ℂ → ℂ := e.symm
  have hw : (w : ℂ) ∈ e.source := he.mem_toPartialHomeomorph_source
  have hr : (r : ℂ) ∈ e.target := by
    rw [← hvalue]
    exact he.image_mem_toPartialHomeomorph_target
  have hfvalue : f (r : ℂ) = (w : ℂ) := by
    rw [← hvalue]
    exact e.left_inv hw
  have hft : Tendsto f (𝓝 (r : ℂ)) (𝓝 (w : ℂ)) := by
    rw [← hvalue]
    exact e.tendsto_symm hw
  have hcft : Tendsto (fun z => conj (f z)) (𝓝 (r : ℂ)) (𝓝 (w : ℂ)) := by
    simpa only [Complex.conj_ofReal] using
      (Complex.continuous_conj.tendsto (w : ℂ)).comp hft
  have hAn : AnalyticAt ℂ K (w : ℂ) := ⟨p, hp⟩
  have hall : ∀ᶠ z in 𝓝 (r : ℂ),
      z ∈ e.target ∧ AnalyticAt ℂ K (f z) ∧ deriv K (f z) ≠ 0 ∧
      conj (f z) ∈ e.source ∧ K (conj (f z)) = conj (K (f z)) := by
    filter_upwards [e.open_target.mem_nhds hr,
      hft.eventually hAn.eventually_analyticAt,
      hft.eventually (hAn.deriv.continuousAt.eventually_ne hd),
      hcft.eventually (e.open_source.mem_nhds hw),
      hft.eventually hreflect] with z hz hza hzd hzc hzr
    exact ⟨hz, hza, hzd, hzc, hzr⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨f, R, hR, hfvalue, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h := hball z hz
    exact (e.hasDerivAt_symm h.1 h.2.2.1 h.2.1.differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxb : (x : ℂ) ∈ Metric.ball (r : ℂ) R := by
      simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hx
    have h := hball (x : ℂ) hxb
    have hright : K (f (x : ℂ)) = (x : ℂ) := e.right_inv h.1
    have heq : f (x : ℂ) = conj (f (x : ℂ)) := by
      apply e.injOn (e.map_target h.1) h.2.2.2.1
      change K (f (x : ℂ)) = K (conj (f (x : ℂ)))
      rw [h.2.2.2.2, hright, Complex.conj_ofReal]
    have hi := congrArg Complex.im heq
    simp only [Complex.conj_im] at hi
    linarith
  · intro z hz
    exact e.right_inv (hball z hz).1
  · exact he.eventually_left_inverse

end ProjectionChannels

