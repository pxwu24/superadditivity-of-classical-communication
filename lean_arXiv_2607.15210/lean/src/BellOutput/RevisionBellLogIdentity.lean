import BellOutput.RevisionBellPrimitive

/-! Identification of the actual logarithmic potential from the Bernoulli
inverse-Cauchy branch. All integrals are genuine measure integrals. -/

open MeasureTheory Filter Finset
open scoped Topology BigOperators
noncomputable section
namespace RevisionBell
open ProjectionChannels

lemma normalized_cauchy_kernel_bound {s M z : ℝ}
    (hs : 0 ≤ s) (hsM : s ≤ M) (hz : z < 0) :
    0 ≤ 1-z*(z-s)⁻¹ ∧ 1-z*(z-s)⁻¹ ≤ M/(-z) := by
  have hpos : 0 < s-z := by linarith
  have hid : 1-z*(z-s)⁻¹ = s/(s-z) := by
    field_simp [hpos.ne', (show z-s ≠ 0 by linarith)]
    ring
  rw [hid]
  constructor
  · exact div_nonneg hs hpos.le
  · apply (div_le_div_iff₀ hpos (show 0 < -z by linarith)).2
    have hM : 0 ≤ M := hs.trans hsM
    have hprod := mul_nonneg hM hs
    have hmono := mul_le_mul_of_nonneg_right hsM (show 0 ≤ -z by linarith)
    nlinarith only [hprod,hmono]

theorem normalized_cauchy_bound_left (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M z : ℝ) (hbound : ∀ᵐ s ∂μ, 0 ≤ s ∧ s ≤ M) (hz : z < 0) :
    0 ≤ 1-z*realCauchyTransform μ z ∧
      1-z*realCauchyTransform μ z ≤ M/(-z) := by
  have hi := integrable_realCauchyKernel_left μ 0 z (hbound.mono fun s hs => hs.1) hz
  have heq : 1-z*realCauchyTransform μ z = ∫ s : ℝ, 1-z*(z-s)⁻¹ ∂μ := by
    rw [integral_sub (integrable_const _) (hi.const_mul z), integral_const_mul]
    simp [realCauchyTransform]
  rw [heq]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hbound] with s hs
    exact (normalized_cauchy_kernel_bound hs.1 hs.2 hz).1
  · have hm := integral_mono_ae ((integrable_const 1).sub (hi.const_mul z))
      (integrable_const (M/(-z))) (show ∀ᵐ s ∂μ,
        1-z*(z-s)⁻¹ ≤ M/(-z) by
          filter_upwards [hbound] with s hs
          exact (normalized_cauchy_kernel_bound hs.1 hs.2 hz).2)
    simpa using hm

theorem normalized_cauchy_tendsto_one_left (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (hbound : ∀ᵐ s ∂μ, 0 ≤ s ∧ s ≤ M) :
    Tendsto (fun z => z*realCauchyTransform μ z) atBot (nhds 1) := by
  have hupper : Tendsto (fun z : ℝ => M/(-z)) atBot (nhds 0) := by
    simpa only [div_eq_mul_inv, inv_neg, mul_zero, neg_zero] using
      (tendsto_inv_atBot_zero.neg.const_mul M :
        Tendsto (fun z : ℝ => M * -z⁻¹) atBot (nhds (M * -0)))
  have hlim : Tendsto (fun z => 1-z*realCauchyTransform μ z) atBot (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with z hz
      exact (normalized_cauchy_bound_left μ M z hbound hz).1
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with z hz
      exact (normalized_cauchy_bound_left μ M z hbound hz).2
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hlim

theorem cauchy_tendsto_zero_left (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (hbound : ∀ᵐ s ∂μ, 0 ≤ s ∧ s ≤ M) :
    Tendsto (realCauchyTransform μ) atBot (nhds 0) := by
  have h := (normalized_cauchy_tendsto_one_left μ M hbound).mul tendsto_inv_atBot_zero
  have heq : (fun z => z*realCauchyTransform μ z*z⁻¹) =ᶠ[atBot] realCauchyTransform μ := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with z hz
    field_simp [hz.ne]
  simpa using h.congr' heq

def inverseCauchyLogPrimitive {k : ℕ} (t : ℝ) (a : Fin k → ℝ)
    (G : ℝ → ℝ) (z : ℝ) : ℝ :=
  -Real.log (-G z)+z*G z-1-(k : ℝ)*∑ i, bernoulliPrimitive t (a i*G z/k)

theorem inverseCauchyLogPrimitive_normalized
    {k : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : Fin k → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (hbound : ∀ᵐ s ∂μ, 0 ≤ s ∧ s ≤ M) :
    Tendsto (fun z => inverseCauchyLogPrimitive t a (realCauchyTransform μ) z -
      Real.log (-z)) atBot (nhds 0) := by
  have hG := cauchy_tendsto_zero_left μ M hbound
  have hzG := normalized_cauchy_tendsto_one_left μ M hbound
  have hl : Tendsto (fun z => Real.log (z*realCauchyTransform μ z)) atBot (nhds 0) := by
    simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hzG
  have hsum : Tendsto (fun z => ∑ i, bernoulliPrimitive t (a i*realCauchyTransform μ z/k))
      atBot (nhds 0) := by
    have harg (i : Fin k) : Tendsto (fun z => a i*realCauchyTransform μ z/k)
        atBot (nhds 0) := by simpa using (hG.const_mul (a i)).div_const (k : ℝ)
    have h := tendsto_finset_sum Finset.univ (fun i _ =>
      (hasDerivAt_bernoulliPrimitive ht0 ht1 0).continuousAt.tendsto.comp
        (harg i))
    simpa using h
  have h := ((hl.neg.add hzG).sub (tendsto_const_nhds (x := (1 : ℝ)))).sub
    (hsum.const_mul (k : ℝ))
  have heq : (fun z => -Real.log (z*realCauchyTransform μ z)+z*realCauchyTransform μ z-1-
      (k : ℝ)*∑ i, bernoulliPrimitive t (a i*realCauchyTransform μ z/k)) =ᶠ[atBot]
      (fun z => inverseCauchyLogPrimitive t a (realCauchyTransform μ) z-Real.log (-z)) := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with z hz
    have hneg := realCauchyTransform_neg_left μ 0 z (hbound.mono fun s hs => hs.1) hz
    have hlog := Real.log_mul (neg_ne_zero.mpr hz.ne) (neg_ne_zero.mpr hneg.ne)
    rw [neg_mul_neg] at hlog
    rw [hlog]
    unfold inverseCauchyLogPrimitive
    ring
  simpa using h.congr' heq

/-- Equation (96): the logarithmic potential of the actual free-sum measure.
The only measure-law hypothesis is its usual additive R-transform germ;
the lower spectral bound is explicit and is not replaced by the conclusion. -/
theorem bernoulli_law_logPotential_identity
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) (μ : Measure ℝ) (hμ : IsBernoulliFreeSumLaw k t a μ)
    (m M : ℝ) (hm : 0 < m) (hbound : ∀ᵐ s ∂μ, m ≤ s ∧ s ≤ M) :
    logPotential μ 0 =
      -Real.log (-realCauchyTransform μ 0)-1-
        (k : ℝ)*∑ i, bernoulliPrimitive t (a i*realCauchyTransform μ 0/k) := by
  letI := hμ.probability
  have hlo : ∀ᵐ s ∂μ, m ≤ s := hbound.mono fun s hs => hs.1
  have hf : ∀ z < m, HasDerivAt
      (inverseCauchyLogPrimitive t a (realCauchyTransform μ)) (realCauchyTransform μ z) z := by
    intro z hz
    have hneg := realCauchyTransform_neg_left μ m z hlo hz
    have hInv := bernoulli_law_inverse_left hk ht0 ht1 a μ hμ m hlo z hz
    rw [← bernoulliFreeSum_inverse_formula hk t a hneg.ne] at hInv
    exact hasDerivAt_inverse_cauchy_primitive hk ht0 ht1 a _ z _
      (hasDerivAt_realCauchyTransform_left μ m z hlo hz) hneg.ne hInv
  have hb0 : ∀ᵐ s ∂μ, 0 ≤ s ∧ s ≤ M :=
    hbound.mono fun s hs => ⟨hm.le.trans hs.1,hs.2⟩
  have heq := logPotential_unique_primitive μ m M hm.le hbound
    (inverseCauchyLogPrimitive t a (realCauchyTransform μ)) hf
    (inverseCauchyLogPrimitive_normalized ht0 ht1 a μ M hb0) 0 hm
  simpa [inverseCauchyLogPrimitive] using heq.symm

end RevisionBell
