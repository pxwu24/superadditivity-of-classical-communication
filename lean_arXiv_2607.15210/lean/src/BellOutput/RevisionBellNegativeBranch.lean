import RandomCompression.RevisionBernoulliHolomorphic
import BellOutput.RevisionBellLogPotential

/-! Analytic continuation of the negative inverse-Cauchy branch used by the
logarithmic variation argument. -/

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace RevisionBell
open ProjectionChannels

theorem differentiableAt_cauchyTransform_left
    (μ : Measure ℝ) [IsFiniteMeasure μ] (m : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, m ≤ s) (z : ℂ) (hz : z.re < m) :
    DifferentiableAt ℂ (cauchyTransform μ) z := by
  apply (hasDerivAt_cauchyTransform_of_separation μ z ((m-z.re)/2)
    (by linarith) _).differentiableAt
  filter_upwards [hbound] with s hs
  have h := Complex.abs_re_le_norm (z-(s : ℂ))
  have he : (z-(s : ℂ)).re = z.re-s := by simp
  rw [he, abs_of_neg (by linarith : z.re-s < 0)] at h
  linarith

theorem differentiableOn_cauchyTransform_left
    (μ : Measure ℝ) [IsFiniteMeasure μ] (m : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, m ≤ s) :
    DifferentiableOn ℂ (cauchyTransform μ) {z : ℂ | z.re < m} := by
  intro z hz
  exact (differentiableAt_cauchyTransform_left μ m hbound z hz).differentiableWithinAt

theorem hasDerivAt_realCauchyTransform_left
    (μ : Measure ℝ) [IsFiniteMeasure μ] (m x : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, m ≤ s) (hx : x < m) :
    HasDerivAt (realCauchyTransform μ)
      (∫ s : ℝ, -((x-s)^2)⁻¹ ∂μ) x := by
  have hd := hasDerivAt_cauchyTransform_of_separation μ (x : ℂ)
    ((m-x)/2) (by linarith) (by
      filter_upwards [hbound] with s hs
      simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_neg (by linarith : x-s < 0)]
      linarith)
  have h := hd.real_of_complex
  simpa only [cauchyTransform_ofReal, Complex.ofReal_re,
    ← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    ← Complex.ofReal_neg, integral_complex_ofReal] using h

/-- The inverse germ at negative infinity continues over the whole left
component. In particular it reaches `z=0` when the lower bound is positive. -/
theorem inverse_cauchy_germ_extends_left
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, m ≤ s)
    (K : ℂ → ℂ)
    (hK : ∀ w : ℝ, w < 0 → AnalyticAt ℂ K (w : ℂ))
    (hgerm : ∀ᶠ x : ℝ in atBot,
      K (realCauchyTransform μ x : ℂ) = (x : ℂ)) :
    ∀ x : ℝ, x < m → K (realCauchyTransform μ x : ℂ) = (x : ℂ) := by
  let f : ℝ → ℂ := fun x => K (cauchyTransform μ (x : ℂ))
  have hf : AnalyticOnNhd ℝ f (Iio m) := by
    intro x hx
    have hG : AnalyticAt ℂ (cauchyTransform μ) (x : ℂ) :=
      (differentiableOn_cauchyTransform_left μ m hbound).analyticAt
        ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hx)
    have hKG : AnalyticAt ℂ (fun z => K (cauchyTransform μ z)) (x : ℂ) := by
      apply AnalyticAt.comp _ hG
      rw [cauchyTransform_ofReal]
      exact hK _ (realCauchyTransform_neg_left μ m x hbound hx)
    exact hKG.restrictScalars.comp (Complex.ofRealCLM.analyticAt x)
  have hg : AnalyticOnNhd ℝ (fun x : ℝ => (x : ℂ)) (Iio m) :=
    fun x _ => Complex.ofRealCLM.analyticAt x
  obtain ⟨R,hR⟩ := eventually_atBot.mp hgerm
  let x₀ := min m R - 1
  have hx₀m : x₀ < m := by dsimp [x₀]; linarith [min_le_left m R]
  have hx₀R : x₀ < R := by dsimp [x₀]; linarith [min_le_right m R]
  have heq : f =ᶠ[𝓝 x₀] (fun x : ℝ => (x : ℂ)) := by
    filter_upwards [Iio_mem_nhds hx₀R] with x hx
    simpa only [f, cauchyTransform_ofReal] using hR x hx.le
  have hall := hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_Iio m).isPreconnected hx₀m heq
  intro x hx
  simpa only [f, cauchyTransform_ofReal] using hall hx

/-- Specialization to the explicit Bernoulli inverse transform. -/
theorem bernoulli_inverse_germ_extends_left
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (hbound : ∀ᵐ s : ℝ ∂μ, m ≤ s)
    (hgerm : ∀ᶠ x : ℝ in atBot,
      bernoulliK t (k : ℝ) a (realCauchyTransform μ x) = x) :
    ∀ x : ℝ, x < m → bernoulliK t (k : ℝ) a (realCauchyTransform μ x) = x := by
  have hgermC : ∀ᶠ x : ℝ in atBot,
      bernoulliComplexK t (k : ℝ) a (realCauchyTransform μ x : ℂ) = (x : ℂ) := by
    filter_upwards [hgerm] with x hx
    rw [bernoulliComplexK_ofReal t (k : ℝ) a ht0 ht1, hx]
  have h := inverse_cauchy_germ_extends_left μ m hbound
    (bernoulliComplexK t (k : ℝ) a)
    (fun w hw => analyticAt_bernoulliComplexK_ne t (k : ℝ) a ht0 ht1 w hw.ne)
    hgermC
  intro x hx
  have heq := h x hx
  rw [bernoulliComplexK_ofReal t (k : ℝ) a ht0 ht1] at heq
  exact_mod_cast heq

/-- The actual free-sum law's inverse identity on its negative branch. Only
the conventional law characterization and a positive spectral lower bound
are used; the inverse identity is proved by continuation. -/
theorem bernoulli_law_inverse_left
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) (μ : Measure ℝ) (hμ : IsBernoulliFreeSumLaw k t a μ)
    (m : ℝ) (hbound : ∀ᵐ s : ℝ ∂μ, m ≤ s) :
    ∀ x : ℝ, x < m → bernoulliK t (k : ℝ) a (realCauchyTransform μ x) = x := by
  letI := hμ.probability
  exact bernoulli_inverse_germ_extends_left hk ht0 ht1 a μ m hbound
    (hμ.bernoulliK_germ_left hk)

/-- The `w_X = G_{μ_X}(0)` in (96) is a negative root of its displayed scalar
equation, for the genuine limiting probability measure. -/
theorem bernoulli_law_zero_root
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) (μ : Measure ℝ) (hμ : IsBernoulliFreeSumLaw k t a μ)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ᵐ s : ℝ ∂μ, m ≤ s) :
    realCauchyTransform μ 0 < 0 ∧
      1+(k : ℝ)*∑ i, bernoulliDual t (a i * realCauchyTransform μ 0 / k) = 0 := by
  letI := hμ.probability
  have hw := realCauchyTransform_neg_left μ m 0 hbound hm
  refine ⟨hw, ?_⟩
  have h := bernoulli_law_inverse_left hk ht0 ht1 a μ hμ m hbound 0 hm
  unfold bernoulliK at h
  exact (div_eq_zero_iff.mp h).resolve_right hw.ne

end RevisionBell
