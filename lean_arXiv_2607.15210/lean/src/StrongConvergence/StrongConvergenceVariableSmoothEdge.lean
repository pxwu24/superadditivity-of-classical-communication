import StrongConvergence.StrongConvergenceSmoothEdge
import StrongConvergence.StrongConvergenceCanonicalLimitLaw
import StrongConvergence.StrongConvergenceGenusLawIdentification
import StrongConvergence.StrongConvergenceVariableMomentLimit
import StrongConvergence.StrongConvergenceSupportDensity

open MeasureTheory Filter Set Polynomial
open scoped Topology BigOperators ContDiff
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar

/-- The actual genus-zero smooth functional vanishes when the support edge
at that density lies below the support of the test. -/
lemma smoothGenusValue_edgeTest_eq_zero {k : ℕ} {s K r ε : ℝ}
    (hk : 0 < k) (hs0 : 0 < s) (hs1 : s < 1) (a : Fin k → ℝ)
    (hK : 0 < K) (hKa : (∑i, |a i|) ≤ K)
    (c : ℤ → ℝ) (hc : Summable (fun j => |c j|))
    (hexp : ∀x ∈ Icc (-K) K, HasSum
      (fun j => c j * (scaledChebyshev K j).eval x) (StrongConvergence.edgeTest r ε x))
    (hr : bernoulliSupport s (k:ℝ) a ≤ r) (hε : 0 < ε) :
    smoothGenusValue k a K c s = 0 := by
  obtain ⟨ν,hprob,hν,hmom,-⟩ := exists_canonical_spectral_limit hk hs0.le hs1 a
  letI := hprob
  have hνK : ∀ᵐ x ∂ν, x ∈ Icc (-K) K := hν.mono fun x hx =>
    ⟨by linarith [hx.1], hx.2.trans hKa⟩
  have hlaw := isBernoulliFreeSumLaw_of_genus_moments ν hk hs0.le hs1.le
    (Finset.sum_nonneg (fun i _ => abs_nonneg (a i)))
    (hν.mono fun _ hx => abs_le.mpr hx) hmom
  have hedge : sSup (realMeasureSupport ν) = bernoulliSupport s (k:ℝ) a :=
    bernoulli_free_sum_right_edge hk hs0 hs1 a ν hlaw
  have hupper : ∀ᵐ x ∂ν, x ≤ r := hlaw.right_edge.2.mono fun x hx => by
    rw [hedge] at hx
    exact hx.trans hr
  rw [smoothGenusValue_eq_integral a hK ν hνK hmom c _ hc hexp]
  exact integral_edgeTest_eq_zero ν hε hupper

/-- The Markov estimate also applies to varying densities and an eventual
inverse-square trace bound. -/
lemma variable_upper_probability_tendsto_zero_of_trace_bound
    {k : ℕ} {r ε C : ℝ} (hk : 0 < k) (a : Fin k → ℝ) (u : ℕ → ℝ) (hε : 0 < ε)
    (htrace : ∀ᶠ n : ℕ in atTop,
      (∫sample, spectralTest k (u n) a n (StrongConvergence.edgeTest r ε) sample ∂probability k) ≤
        C / (((n+1)*k : ℕ):ℝ)^2) :
    Tendsto (fun n : ℕ => (probability k).real
      {sample | r+ε ≤ largestEigenvalue (compressionHermitian k (u n) a sample n)})
      atTop (𝓝 0) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg)
    (g := fun n : ℕ => (C/(k:ℝ)^2) * (1/((n:ℝ)+1)))
  · filter_upwards [htrace] with n hn
    have hn0 : (n:ℝ)+1 ≠ 0 := by positivity
    calc
      _ ≤ ((n+1:ℕ):ℝ) * ∫sample, spectralTest k (u n) a n
          (StrongConvergence.edgeTest r ε) sample ∂probability k :=
        upper_edge_probability_le_smooth_trace k (u n) a n hε
      _ ≤ ((n+1:ℕ):ℝ) * (C / (((n+1)*k : ℕ):ℝ)^2) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by push_cast; field_simp; ring
  · simpa only [mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (C/(k:ℝ)^2)

/-- For any converging sequence of densities, the upper outlier probability
vanishes above the limiting Bernoulli support edge. The uniform smooth master
estimate is used at the rounded density; upper semicontinuity makes its
leading term exactly zero eventually, so no convergence rate is required. -/
theorem variable_upper_edge_measure_tendsto_zero
    {k : ℕ} {t ε : ℝ} (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) (u : ℕ → ℝ)
    (hu0 : ∀n, 0 ≤ u n) (hu1 : ∀n, u n ≤ 1) (hut : Tendsto u atTop (𝓝 t))
    (hε : 0 < ε) :
    Tendsto (fun n : ℕ => probability k
      {sample | bernoulliSupport t (k:ℝ) a + ε ≤
        largestEigenvalue (compressionHermitian k (u n) a sample n)})
      atTop (𝓝 0) := by
  let K : ℝ := (∑i, |a i|) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKa : (∑i, |a i|) ≤ K := by dsimp [K]; linarith
  let r : ℝ := bernoulliSupport t (k:ℝ) a + ε/2
  let χ := StrongConvergence.edgeTest r (ε/2)
  have hhalf : 0 < ε/2 := by positivity
  obtain ⟨c,hc,hexp'⟩ := StrongConvergence.exists_smooth_chebyshev_expansion
    (StrongConvergence.edgeTest_contDiff r (ε/2)) hK
  have hc0 : Summable (fun j => |c j|) := by simpa only [pow_zero, mul_one] using hc 0
  have hexp : ∀x ∈ Icc (-K) K, HasSum
      (fun j => c j * (scaledChebyshev K j).eval x) (χ x) := by
    simpa only [scaledChebyshev_eval] using hexp'
  let ρ : ℕ → ℝ := fun n => (rankSequence k (u n) n:ℝ)/(((n+1)*k:ℕ):ℝ)
  have hρ : Tendsto ρ atTop (𝓝 t) := rank_density_variable_tendsto hk hu0 hut
  have hρint : ∀ᶠ n in atTop, ρ n ∈ Ioo (0:ℝ) 1 := hρ.eventually (Ioo_mem_nhds ht0 ht1)
  have hρedge : ∀ᶠ n in atTop, bernoulliSupport (ρ n) (k:ℝ) a < r :=
    hρ.eventually (eventually_bernoulliSupport_lt ht0 ht1 (Nat.cast_pos.mpr hk) a
      (by dsimp [r]; linarith))
  have htrace : ∀ᶠ n : ℕ in atTop,
      (∫sample, spectralTest k (u n) a n χ sample ∂probability k) ≤
        smoothMasterConstant k c / (((n+1)*k:ℕ):ℝ)^2 := by
    filter_upwards [hρint,hρedge] with n hn he
    have hz := smoothGenusValue_edgeTest_eq_zero hk hn.1 hn.2 a hK hKa c hc0 hexp he.le hhalf
    have hm := expected_spectralTest_smooth_master_bound hk ⟨hu0 n,hu1 n⟩ a hK hKa c χ hc hexp n
    change |(∫sample, spectralTest k (u n) a n χ sample ∂probability k) -
      smoothGenusValue k a K c (ρ n)| ≤ _ at hm
    rw [hz, sub_zero] at hm
    exact (le_abs_self _).trans hm
  have hreal := variable_upper_probability_tendsto_zero_of_trace_bound hk a u hhalf htrace
  have heq : r + ε/2 = bernoulliSupport t (k:ℝ) a + ε := by dsimp [r]; ring
  rw [heq] at hreal
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  simp only [ENNReal.ofReal_zero, Function.comp_def] at h
  convert h using 1
  funext n
  exact (ofReal_measureReal (measure_ne_top (probability k) _)).symm

#print axioms variable_upper_edge_measure_tendsto_zero
end ProjectionChannels.Canonical
