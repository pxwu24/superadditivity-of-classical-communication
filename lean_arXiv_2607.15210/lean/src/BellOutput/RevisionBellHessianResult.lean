import BellOutput.RevisionBellImplicit
import BellOutput.RevisionBellPositiveLaw

open MeasureTheory Filter Finset
open scoped Topology BigOperators
noncomputable section
namespace RevisionBell
open ProjectionChannels

/-- Centering the direction reduces the general root equation to the
traceless implicit-function theorem. -/
theorem exists_smooth_bernoulli_root_general {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : Fin k → ℝ)
    (w0 : ℝ) (hroot : rootEquation k t h 0 w0 = 0) :
    ∃ w : ℝ → ℝ, w 0=w0 ∧ ContDiffAt ℝ 2 w 0 ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ), rootEquation k t h ε (w ε)=0 := by
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  let m : ℝ := (∑ i, h i)/(k : ℝ)
  let h0 : Fin k → ℝ := fun i => h i-m
  have hs : ∑ i, h0 i = 0 := by
    dsimp [h0, m]
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hroot0 : rootEquation k t h0 0 w0 = 0 := by
    simpa only [rootEquation, zero_mul, add_zero, one_mul] using hroot
  obtain ⟨v, hv0, hv, hvroot⟩ := exists_smooth_bernoulli_root hk ht0 ht1 h0 hs w0 hroot0
  let x : ℝ → ℝ := fun ε => 1+ε*m
  let ξ : ℝ → ℝ := fun ε => ε/x ε
  let w : ℝ → ℝ := fun ε => v (ξ ε)/x ε
  have hx0 : x 0 = 1 := by simp [x]
  have hξ0 : ξ 0 = 0 := by simp [ξ]
  have hx : ContDiffAt ℝ 2 x 0 := by dsimp [x]; fun_prop
  have hξ : ContDiffAt ℝ 2 ξ 0 :=
    contDiffAt_id.div hx (by rw [hx0]; norm_num)
  have hvξ : ContDiffAt ℝ 2 (fun ε => v (ξ ε)) 0 := by
    apply ContDiffAt.comp 0 _ hξ
    rwa [hξ0]
  refine ⟨w, ?_, hvξ.div hx (by rw [hx0]; norm_num), ?_⟩
  · simp only [w, hξ0, hx0, hv0, div_one]
  · have hlim : Tendsto ξ (𝓝 0) (𝓝 0) := by simpa only [hξ0] using hξ.continuousAt.tendsto
    filter_upwards [hlim.eventually hvroot, hx.continuousAt.eventually_ne
      (by rw [hx0]; norm_num : x 0 ≠ 0)] with ε hε hxε
    have heach (i : Fin k) : (1+ε*h i)*w ε/(k : ℝ) =
        (1+ξ ε*h0 i)*v (ξ ε)/(k : ℝ) := by
      dsimp only [w, ξ, h0]
      have hxε' : 1+ε*m ≠ 0 := hxε
      dsimp [x] at *
      field_simp
      <;> ring
      <;> simp
    unfold rootEquation at hε ⊢
    simpa only [heach] using hε

/-- Strict monotonicity makes the root of the positive-coefficient equation
unique on the whole real line. -/
theorem rootEquation_strictMono {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : Fin k → ℝ) (ε : ℝ)
    (ha : ∀ i, 0 < 1+ε*h i) : StrictMono (rootEquation k t h ε) := by
  have hg : StrictMono (bernoulliDual t) := by
    apply strictMono_of_deriv_pos
    intro y
    rw [(hasDerivAt_bernoulliDual ht0 ht1 y).deriv]
    exact (bernoulliMaximizer_mem_Ioo ht0 ht1 y).1
  intro x y hxy
  unfold rootEquation
  apply add_lt_add_left
  apply mul_lt_mul_of_pos_left _ (Nat.cast_pos.mpr hk)
  apply sum_lt_sum_of_nonempty
  · exact ⟨⟨0,hk⟩, mem_univ _⟩
  · intro i _
    apply hg
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hxy (ha i)) (Nat.cast_pos.mpr hk)

/-- Positivity of the coefficient direction holds on a single neighborhood
because there are only finitely many coefficients. -/
theorem eventually_positive_coefficients {k : ℕ} (h : Fin k → ℝ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i, 0 < 1+ε*h i := by
  apply Filter.eventually_all.mpr
  intro i
  have hc : ContinuousAt (fun ε : ℝ => 1+ε*h i) 0 := by fun_prop
  have hh : 0 < 1+(0:ℝ)*h i := by norm_num
  exact hc.eventually (Ioi_mem_nhds hh)

/-- **Lemma A.2 for actual probability laws.** The family is specified by
its Bernoulli free-sum R-transform and positive compact support. The proof
constructs the smooth root and identifies it with the Cauchy root by uniqueness;
no differentiability of the measure family, root, or log-potential is assumed. -/
theorem bernoulli_logPotential_hessian_of_positive_laws
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t) (h : Fin k → ℝ) (μ : ℝ → Measure ℝ)
    (hμ : ∀ᶠ ε in 𝓝 (0 : ℝ),
      IsBernoulliFreeSumLaw k t (fun i => 1+ε*h i) (μ ε))
    (hpositive : ∀ᶠ ε in 𝓝 (0 : ℝ), ∃ m M : ℝ,
      0 < m ∧ ∀ᵐ s ∂μ ε, m ≤ s ∧ s ≤ M) :
    HasDerivAt (deriv (fun ε => logPotential (μ ε) 0))
      (BellLimitVerification.hessianC0 k t * (∑ i, h i)^2 +
        BellLimitVerification.hessianC1 k t * ∑ i, (h i)^2) 0 := by
  have hμ0 := hμ.self_of_nhds
  obtain ⟨m0, M0, hm0, hb0⟩ := hpositive.self_of_nhds
  have hzero := bernoulli_law_zero_root hk ht0 ht1 (fun i => 1+(0:ℝ)*h i)
    (μ 0) hμ0 m0 hm0 (hb0.mono fun _ hs => hs.1)
  have hroot0 : rootEquation k t h 0 (realCauchyTransform (μ 0) 0) = 0 := hzero.2
  obtain ⟨w, hw0, hw, hwroot⟩ := exists_smooth_bernoulli_root_general hk ht0 ht1 h
    (realCauchyTransform (μ 0) 0) hroot0
  have hne : w 0 ≠ 0 := by rw [hw0]; exact hzero.1.ne
  have hd := rootLogExpression_hessian hk ht0 ht1 hkt h w hw hne hwroot
  have heq : (fun ε => logPotential (μ ε) 0) =ᶠ[𝓝 0] rootLogExpression t h w := by
    filter_upwards [hμ, hpositive, hwroot, eventually_positive_coefficients h] with ε hμε hbε hwrε haε
    obtain ⟨m, M, hm, hb⟩ := hbε
    have hact := bernoulli_law_zero_root hk ht0 ht1 (fun i => 1+ε*h i)
      (μ ε) hμε m hm (hb.mono fun _ hs => hs.1)
    have heqr : w ε = realCauchyTransform (μ ε) 0 := by
      apply (rootEquation_strictMono hk ht0 ht1 h ε haε).injective
      exact hwrε.trans hact.2.symm
    rw [bernoulli_law_logPotential_identity hk ht0 ht1 (fun i => 1+ε*h i) (μ ε) hμε m M hm hb]
    simp only [rootLogExpression, heqr]
  exact hd.congr_of_eventuallyEq heq.deriv

/-- A smooth local scalar model for the actual logarithmic moment. -/
theorem bernoulli_logPotential_root_model
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t) (h : Fin k → ℝ) (μ : ℝ → Measure ℝ)
    (hμ : ∀ᶠ ε in 𝓝 (0 : ℝ),
      IsBernoulliFreeSumLaw k t (fun i => 1+ε*h i) (μ ε)) :
    ∃ w : ℝ → ℝ, ContDiffAt ℝ 2 w 0 ∧ w 0 ≠ 0 ∧
      (∀ᶠ ε in 𝓝 (0 : ℝ), rootEquation k t h ε (w ε)=0) ∧
      (fun ε => logPotential (μ ε) 0) =ᶠ[𝓝 0] rootLogExpression t h w := by
  have hpositive : ∀ᶠ ε in 𝓝 (0 : ℝ), ∃ m M : ℝ,
      0 < m ∧ ∀ᵐ s ∂μ ε, m ≤ s ∧ s ≤ M := by
    filter_upwards [hμ, eventually_positive_coefficients h] with ε hμε haε
    exact IsBernoulliFreeSumLaw.positive_bounds hk ht0 ht1 hkt
      (fun i => 1+ε*h i) haε (μ ε) hμε
  have hμ0 := hμ.self_of_nhds
  obtain ⟨m0, M0, hm0, hb0⟩ := hpositive.self_of_nhds
  have hzero := bernoulli_law_zero_root hk ht0 ht1 (fun i => 1+(0:ℝ)*h i)
    (μ 0) hμ0 m0 hm0 (hb0.mono fun _ hs => hs.1)
  have hroot0 : rootEquation k t h 0 (realCauchyTransform (μ 0) 0) = 0 := hzero.2
  obtain ⟨w, hw0, hw, hwroot⟩ := exists_smooth_bernoulli_root_general hk ht0 ht1 h
    (realCauchyTransform (μ 0) 0) hroot0
  have hne : w 0 ≠ 0 := by rw [hw0]; exact hzero.1.ne
  have heq : (fun ε => logPotential (μ ε) 0) =ᶠ[𝓝 0] rootLogExpression t h w := by
    filter_upwards [hμ, hpositive, hwroot, eventually_positive_coefficients h] with ε hμε hbε hwrε haε
    obtain ⟨m, M, hm, hb⟩ := hbε
    have hact := bernoulli_law_zero_root hk ht0 ht1 (fun i => 1+ε*h i)
      (μ ε) hμε m hm (hb.mono fun _ hs => hs.1)
    have heqr : w ε = realCauchyTransform (μ ε) 0 := by
      apply (rootEquation_strictMono hk ht0 ht1 h ε haε).injective
      exact hwrε.trans hact.2.symm
    rw [bernoulli_law_logPotential_identity hk ht0 ht1 (fun i => 1+ε*h i) (μ ε) hμε m M hm hb]
    simp only [rootLogExpression, heqr]
  exact ⟨w, hw, hne, hwroot, heq⟩

/-- The logarithmic moment is differentiable throughout a neighborhood of zero,
with no regularity of the measure-valued family assumed. -/
theorem bernoulli_logPotential_eventually_differentiable
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t) (h : Fin k → ℝ) (μ : ℝ → Measure ℝ)
    (hμ : ∀ᶠ ε in 𝓝 (0 : ℝ),
      IsBernoulliFreeSumLaw k t (fun i => 1+ε*h i) (μ ε)) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun x => logPotential (μ x) 0) ε := by
  obtain ⟨w, hw, hne, hroot, heq⟩ := bernoulli_logPotential_root_model hk ht0 ht1 hkt h μ hμ
  filter_upwards [hw.eventually (by norm_num), hw.continuousAt.eventually_ne hne,
    hroot, heq.eventuallyEq_nhds] with ε hwε hneε hrootε heqε
  apply heqε.differentiableAt_iff.mpr
  exact (hasDerivAt_rootLogExpression hk ht0 ht1 h w ε (deriv w ε)
    (hwε.differentiableAt (by norm_num)).hasDerivAt hneε hrootε).differentiableAt

/-- **Lemma A.2 with all support and differentiability conditions discharged.**
For an actual family of compact probability laws having the Bernoulli free-sum
R-transform, the logarithmic moment has the asserted Hessian. Its positive
spectral gap follows from Lemma A.1 by reflecting the actual measure. -/
theorem bernoulli_logPotential_hessian
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t) (h : Fin k → ℝ) (μ : ℝ → Measure ℝ)
    (hμ : ∀ᶠ ε in 𝓝 (0 : ℝ),
      IsBernoulliFreeSumLaw k t (fun i => 1+ε*h i) (μ ε)) :
    HasDerivAt (deriv (fun ε => logPotential (μ ε) 0))
      (BellLimitVerification.hessianC0 k t * (∑ i, h i)^2 +
        BellLimitVerification.hessianC1 k t * ∑ i, (h i)^2) 0 := by
  apply bernoulli_logPotential_hessian_of_positive_laws hk ht0 ht1 hkt h μ hμ
  filter_upwards [hμ, eventually_positive_coefficients h] with ε hμε haε
  exact IsBernoulliFreeSumLaw.positive_bounds hk ht0 ht1 hkt
    (fun i => 1+ε*h i) haε (μ ε) hμε

end RevisionBell

