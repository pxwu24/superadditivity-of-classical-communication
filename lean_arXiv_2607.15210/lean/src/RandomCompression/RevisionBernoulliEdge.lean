import RandomCompression.RevisionBernoulliCauchy
import RandomCompression.BernoulliCriticalPoint

/-!
# A complete right-edge argument from an actual inverse-Cauchy germ

The measure in this file is genuine, and its right edge belongs to its
support. The inverse relation is only assumed near positive infinity; its
continuation to the whole right component and the finite/infinite endpoint
arguments are proved.

The explicit hypothesis `hgerm` remains to be instantiated for the free
convolution in the paper. It is not part of block-modified strong convergence,
and the theorem below therefore does not by itself establish Lemma A.1.
-/

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate BigOperators

noncomputable section
namespace ProjectionChannels

/-- Analytic continuation propagates a genuine inverse-Cauchy germ from
infinity over the entire right component of the complement of the support. -/
theorem inverse_cauchy_germ_extends_right
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r) (K : ℂ → ℂ)
    (hK : ∀ w : ℝ, 0 < w → AnalyticAt ℂ K (w : ℂ))
    (hgerm : ∀ᶠ x : ℝ in atTop,
      K (realCauchyTransform μ x : ℂ) = (x : ℂ)) :
    ∀ x : ℝ, r < x → K (realCauchyTransform μ x : ℂ) = (x : ℂ) := by
  let f : ℝ → ℂ := fun x => K (cauchyTransform μ (x : ℂ))
  have hf : AnalyticOnNhd ℝ f (Ioi r) := by
    intro x hx
    have hG : AnalyticAt ℂ (cauchyTransform μ) (x : ℂ) :=
      (differentiableOn_cauchyTransform_right μ r hbound).analyticAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx)
    have hKG : AnalyticAt ℂ (fun z => K (cauchyTransform μ z)) (x : ℂ) := by
      apply AnalyticAt.comp _ hG
      rw [cauchyTransform_ofReal]
      exact hK _ (realCauchyTransform_pos μ r x hbound hx)
    exact hKG.restrictScalars.comp (Complex.ofRealCLM.analyticAt x)
  have hg : AnalyticOnNhd ℝ (fun x : ℝ => (x : ℂ)) (Ioi r) :=
    fun x _ => Complex.ofRealCLM.analyticAt x
  obtain ⟨R, hR⟩ := eventually_atTop.mp hgerm
  let x₀ := max r R + 1
  have hx₀r : r < x₀ := by dsimp [x₀]; linarith [le_max_left r R]
  have hx₀R : R < x₀ := by dsimp [x₀]; linarith [le_max_right r R]
  have heq : f =ᶠ[𝓝 x₀] (fun x : ℝ => (x : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx₀R] with x hx
    simpa only [f, cauchyTransform_ofReal] using hR x hx.le
  have hall := hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_Ioi r).isPreconnected hx₀r heq
  intro x hx
  simpa only [f, cauchyTransform_ofReal] using hall hx

/-- Complete finite/infinite endpoint proof for the Bernoulli variational
formula, conditional only on the stated inverse germ and holomorphic extension.
In particular an edge formula is not a hypothesis. -/
theorem bernoulli_right_edge_of_inverse_cauchy_germ
    {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ)
    (hr : r ∈ realMeasureSupport μ)
    (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r)
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (K : ℂ → ℂ)
    (hK : ∀ w : ℝ, 0 < w → AnalyticAt ℂ K (w : ℂ))
    (hreal : ∀ w : ℝ, 0 < w → K (w : ℂ) = (bernoulliK t k a w : ℂ))
    (hreflect : ∀ w : ℝ, 0 < w → ∀ᶠ z in 𝓝 (w : ℂ), K (conj z) = conj (K z))
    (hgerm : ∀ᶠ x : ℝ in atTop,
      K (realCauchyTransform μ x : ℂ) = (x : ℂ)) :
    IsGLB (bernoulliKValues t k a) r ∧
      r = sSup (bernoulliObjectiveValues t k a) := by
  have hbranch := inverse_cauchy_germ_extends_right μ r hbound K hK hgerm
  have hbranchR : ∀ x : ℝ, r < x →
      bernoulliK t k a (realCauchyTransform μ x) = x := by
    intro x hx
    have h := hbranch x hx
    rw [hreal _ (realCauchyTransform_pos μ r x hbound hx)] at h
    exact Complex.ofReal_injective h
  have hglb : IsGLB (bernoulliKValues t k a) r := by
    by_cases hbdd : BddAbove (realCauchyTransform μ '' Ioi r)
    · let w := sSup (realCauchyTransform μ '' Ioi r)
      have hw : 0 < w :=
        (realCauchyTransform_pos μ r (r+1) hbound (by linarith)).trans_le
          (le_csSup hbdd ⟨r+1, by simp, rfl⟩)
      have hG := realCauchyTransform_tendsto_right_edge_bounded μ r hbound hbdd
      have hGC : Tendsto (fun x => (realCauchyTransform μ x : ℂ))
          (𝓝[>] r) (𝓝 (w : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hG
      have hKG := (hK w hw).continuousAt.tendsto.comp hGC
      have hKr : K (w : ℂ) = (r : ℂ) := by
        apply tendsto_nhds_unique hKG
        have hi : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] r) (𝓝 (r : ℂ)) :=
          Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        apply hi.congr'
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hbranch x hx).symm
      have hd := inverse_cauchy_finite_endpoint_deriv_eq_zero μ K r w hr hbound
        (hK w hw) hKr (hreflect w hw) hG
        (by filter_upwards [self_mem_nhdsWithin] with x hx; exact hbranch x hx)
      have hDr := (hK w hw).differentiableAt.hasDerivAt.real_of_complex
      have heq : (fun x : ℝ => (K (x : ℂ)).re) =ᶠ[𝓝 w] bernoulliK t k a := by
        filter_upwards [Ioi_mem_nhds hw] with x hx
        rw [hreal x hx, Complex.ofReal_re]
      have hdk : deriv (bernoulliK t k a) w = 0 := by
        have hh := hDr.congr_of_eventuallyEq heq.symm
        simpa only [hd, Complex.zero_re] using hh.deriv
      have hmin := bernoulliK_critical_minimum t k a ht0 ht1 hk w hw hdk
      have hKrR : bernoulliK t k a w = r := by
        rw [hreal w hw] at hKr
        exact Complex.ofReal_injective hKr
      constructor
      · rintro v ⟨z, hz, rfl⟩
        rw [← hKrR]
        exact hmin z hz
      · intro b hb
        rw [← hKrR]
        exact hb ⟨w, hw, rfl⟩
    · have hrange := realCauchyTransform_range_unbounded μ r hbound hbdd
      constructor
      · rintro v ⟨w, hw, rfl⟩
        have hin : w ∈ realCauchyTransform μ '' Ioi r := by rw [hrange]; exact hw
        obtain ⟨x, hx, rfl⟩ := hin
        rw [hbranchR x hx]
        exact hx.le
      · intro b hb
        apply le_of_forall_pos_le_add
        intro ε hε
        have hx : r < r+ε := by linarith
        have h := hb ⟨realCauchyTransform μ (r+ε),
          realCauchyTransform_pos μ r (r+ε) hbound hx, rfl⟩
        rwa [hbranchR (r+ε) hx] at h
  refine ⟨hglb, ?_⟩
  have hne : (bernoulliKValues t k a).Nonempty := ⟨_, ⟨1, by norm_num, rfl⟩⟩
  rw [bernoulli_support_eq_inf t k a ht0 ht1 hk]
  exact (hglb.csInf_eq hne).symm

end ProjectionChannels
