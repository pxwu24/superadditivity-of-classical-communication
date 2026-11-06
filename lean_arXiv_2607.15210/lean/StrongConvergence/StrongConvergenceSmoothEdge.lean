import StrongConvergence.StrongConvergenceSmoothMaster
import StrongConvergence.StrongConvergenceGenusDerivatives
import StrongConvergence.StrongConvergenceRankDensityBound
import RandomCompression.RevisionBernoulliLaw

open MeasureTheory Filter Set Polynomial
open scoped Topology BigOperators ContDiff
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar

/-- Positivity of the smooth genus functional and a zero integral cancel its
linear density term. The resulting bound is uniform in all nearby densities. -/
theorem smoothGenusValue_le_quadratic {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) (a : Fin k → ℝ)
    {K : ℝ} (hK : 0 < K) (hKa : (∑i, |a i|) ≤ K)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsν : ∀ᵐ x ∂ν, x ∈ Icc (-K) K)
    (hmom : ∀m : ℕ, (∫x, x^m ∂ν) = (normalizedMomentCoefficient k m a 0).eval t)
    (c : ℤ → ℝ) (χ : ℝ → ℝ)
    (hc : ∀p : ℕ, Summable (fun j => |c j| * (|(j:ℝ)|+1)^p))
    (hexp : ∀ x ∈ Icc (-K) K, HasSum
      (fun j => c j*(scaledChebyshev K j).eval x) (χ x))
    (hχ : ∀x, 0 ≤ χ x) (hzero : (∫x, χ x ∂ν) = 0)
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    smoothGenusValue k a K c s ≤
      (16 * ∑'j : ℤ, |c j| * (|(j:ℝ)|+1)^6) * (s-t)^2 := by
  have hc0 : Summable (fun j => |c j|) := by simpa only [pow_zero, mul_one] using hc 0
  have hcast (j : ℤ) : ((j.natAbs+1 : ℕ):ℝ) = |(j:ℝ)|+1 := by
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_natAbs, Int.cast_abs]
  have hq3 : Summable (fun j : ℤ => |c j| * ((j.natAbs+1 : ℕ):ℝ)^3) := by
    simpa only [hcast] using hc 3
  have hq6 : Summable (fun j : ℤ => |c j| * ((j.natAbs+1 : ℕ):ℝ)^6) := by
    simpa only [hcast] using hc 6
  have hft : smoothGenusValue k a K c t = 0 :=
    (smoothGenusValue_eq_integral a hK ν hsν hmom c χ hc0 hexp).trans hzero
  have hquad := genus_polynomial_series_le_quadratic hk a
    (fun j : ℤ => j.natAbs+1) (scaledChebyshev K)
    (scaledChebyshev_natDegree_le_succ K) hKa
    (fun j x hx => scaledChebyshev_abs_le hK hx j)
    c hq3 hq6
    (fun s hs => smoothGenusValue_hasSum hk a hK hKa c hc0 hs)
    (fun s hs => smoothGenusValue_nonneg hk a hK hKa c χ hc0 hexp hχ hs)
    ht0 ht1 hft hs
  simpa only [hcast] using hquad

/-- A test above an almost-everywhere upper support bound has zero integral. -/
lemma integral_edgeTest_eq_zero (ν : Measure ℝ) {r ε : ℝ} (hε : 0 < ε)
    (hr : ∀ᵐ x ∂ν, x ≤ r) :
    (∫x, StrongConvergence.edgeTest r ε x ∂ν) = 0 := by
  apply integral_eq_zero_of_ae
  exact hr.mono fun x hx => StrongConvergence.edgeTest_of_le hε hx

/-- An inverse-square expected trace estimate gives a vanishing probability
of an actual eigenvalue above the support edge. -/
theorem upper_edge_probability_tendsto_zero_of_trace_bound
    {k : ℕ} {t r ε C : ℝ} (hk : 0 < k) (a : Fin k → ℝ) (hε : 0 < ε)
    (htrace : ∀n : ℕ,
      (∫sample, spectralTest k t a n (StrongConvergence.edgeTest r ε) sample ∂probability k) ≤
        C / (((n+1)*k : ℕ):ℝ)^2) :
    Tendsto (fun n : ℕ => (probability k).real
      {sample | r+ε ≤ largestEigenvalue (compressionHermitian k t a sample n)})
      atTop (𝓝 0) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (g := fun n : ℕ => (C/(k:ℝ)^2) * (1/((n:ℝ)+1)))
  · intro n
    have hn0 : (n:ℝ)+1 ≠ 0 := by positivity
    calc
      _ ≤ ((n+1:ℕ):ℝ) * ∫sample, spectralTest k t a n
          (StrongConvergence.edgeTest r ε) sample ∂probability k :=
        upper_edge_probability_le_smooth_trace k t a n hε
      _ ≤ ((n+1:ℕ):ℝ) * (C / (((n+1)*k : ℕ):ℝ)^2) :=
        mul_le_mul_of_nonneg_left (htrace n) (by positivity)
      _ = _ := by push_cast; field_simp; ring
  · simpa only [mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (C/(k:ℝ)^2)

/-- B6: moments and compact support of the actual limiting law imply that the
probability of an eigenvalue above any upper support bound vanishes. The proof
uses the proved polynomial master estimate, smooth summation, positivity and
the quantitative floor-rank error. -/
theorem upper_edge_probability_tendsto_zero_of_moments
    {k : ℕ} {t r ε : ℝ} (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {K : ℝ} (hK : 0 < K) (hKa : (∑i, |a i|) ≤ K)
    (hsν : ∀ᵐ x ∂ν, x ∈ Icc (-K) K)
    (hmom : ∀m : ℕ, (∫x, x^m ∂ν) = (normalizedMomentCoefficient k m a 0).eval t)
    (hr : ∀ᵐ x ∂ν, x ≤ r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (probability k).real
      {sample | r+ε ≤ largestEigenvalue (compressionHermitian k t a sample n)})
      atTop (𝓝 0) := by
  let χ := StrongConvergence.edgeTest r ε
  obtain ⟨c, hc, hexp'⟩ := StrongConvergence.exists_smooth_chebyshev_expansion
    (StrongConvergence.edgeTest_contDiff r ε) hK
  have hexp : ∀x ∈ Icc (-K) K, HasSum
      (fun j => c j*(scaledChebyshev K j).eval x) (χ x) := by
    simpa only [scaledChebyshev_eval] using hexp'
  let M : ℝ := 16 * ∑'j : ℤ, |c j| * (|(j:ℝ)|+1)^6
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hzero : (∫x, χ x ∂ν) = 0 := integral_edgeTest_eq_zero ν hε hr
  apply upper_edge_probability_tendsto_zero_of_trace_bound hk a hε
    (C := M + smoothMasterConstant k c)
  intro n
  have hN : (0:ℝ) < (((n+1)*k:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hk
  have hdensity := rankSequence_density_mem_Icc hk ht0.le ht1.le n
  have hquad := smoothGenusValue_le_quadratic hk ht0 ht1 a hK hKa ν hsν hmom c χ hc hexp
    (StrongConvergence.edgeTest_nonneg r ε) hzero hdensity
  have hmaster := expected_spectralTest_smooth_master_bound hk ⟨ht0.le,ht1.le⟩ a hK hKa
    c χ hc hexp n
  exact StrongConvergence.trace_le_inverse_sq_of_quadratic_density_bound
    hM hN (rankSequence_density_abs_sub_le hk ht0.le n) hquad
    (by linarith [(le_abs_self _).trans hmaster])

/-- The same tail statement for the extended-real probability measure, the
form consumed by the concentration and almost-sure edge argument. -/
theorem upper_edge_measure_tendsto_zero_of_moments
    {k : ℕ} {t r ε : ℝ} (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {K : ℝ} (hK : 0 < K) (hKa : (∑i, |a i|) ≤ K)
    (hsν : ∀ᵐ x ∂ν, x ∈ Icc (-K) K)
    (hmom : ∀m : ℕ, (∫x, x^m ∂ν) = (normalizedMomentCoefficient k m a 0).eval t)
    (hr : ∀ᵐ x ∂ν, x ≤ r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => probability k
      {sample | r+ε ≤ largestEigenvalue (compressionHermitian k t a sample n)})
      atTop (𝓝 0) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (upper_edge_probability_tendsto_zero_of_moments hk ht0 ht1 a ν hK hKa hsν hmom hr hε)
  simp only [ENNReal.ofReal_zero, Function.comp_def] at h
  convert h using 1
  funext n
  exact (ofReal_measureReal (measure_ne_top (probability k) _)).symm

/-- In particular the rightmost point of the support of the law is an upper
spectral edge in probability. No regularity of support in the density is used. -/
theorem upper_support_edge_measure_tendsto_zero
    {k : ℕ} {t ε : ℝ} (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {K : ℝ} (hK : 0 < K) (hKa : (∑i, |a i|) ≤ K)
    (hsν : ∀ᵐ x ∂ν, x ∈ Icc (-K) K)
    (hmom : ∀m : ℕ, (∫x, x^m ∂ν) = (normalizedMomentCoefficient k m a 0).eval t)
    (hε : 0 < ε) :
    Tendsto (fun n : ℕ => probability k
      {sample | sSup (realMeasureSupport ν)+ε ≤
        largestEigenvalue (compressionHermitian k t a sample n)})
      atTop (𝓝 0) := by
  obtain ⟨r, -, hr, heq⟩ := compact_probability_right_edge ν
    ⟨K, hsν.mono fun x hx => abs_le.mpr hx⟩
  subst r
  exact upper_edge_measure_tendsto_zero_of_moments hk ht0 ht1 a ν hK hKa hsν hmom hr hε

#print axioms smoothGenusValue_le_quadratic
#print axioms upper_edge_probability_tendsto_zero_of_moments
#print axioms upper_support_edge_measure_tendsto_zero
end ProjectionChannels.Canonical
