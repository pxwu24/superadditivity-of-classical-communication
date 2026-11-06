import StrongConvergence.StrongConvergenceGenusMomentLimit
import StrongConvergence.StrongConvergenceSmoothSpectralTests

/-! Positivity and the compact spectral interval bound for the genus-zero functional,
obtained from convergence of actual expected empirical spectral tests. -/

open Polynomial Filter Set MeasureTheory
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

lemma testRankCoefficient_stable_degree {k q : ℕ} (a : Fin k → ℝ) (p : ℝ[X])
    (hp : p.natDegree ≤ q) (j : ℕ) :
    testRankCoefficient k q a p j = testRankCoefficient k p.natDegree a p j := by
  classical
  unfold testRankCoefficient
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hp 1))
  intro m hm hmn
  have hc : p.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by
    simp only [Finset.mem_range] at hmn
    omega)
  rw [hc, zero_smul]

end ProjectionChannels.TensorHaar
namespace ProjectionChannels.Canonical
open TensorHaar

/-- The expected empirical spectral moment has the genus-zero coefficient as its
limit, with the zeroth moment included. -/
theorem expected_spectralTest_power_tendsto_genus
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a : Fin k → ℝ) (m : ℕ) :
    Tendsto (fun n => ∫ sample, spectralTest k t a n (fun x => x^m) sample ∂probability k)
      atTop (𝓝 ((normalizedMomentCoefficient k m a 0).eval t)) := by
  cases m with
  | zero =>
    have heq (n : ℕ) : (∫ sample, spectralTest k t a n (fun x => x^0) sample
        ∂probability k) = 1 := by simp [spectralTest]
    simpa only [heq, normalizedMomentCoefficient, if_true, Polynomial.eval_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ m =>
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (expectedNormalizedMoment_tendsto_genus hk ht0 ht1 m a)
    simpa only [integral_spectralTest_power_succ, normalizedMomentCoefficient,
      Nat.succ_ne_zero, if_false, Complex.ofReal_re] using h

/-- A7 for every polynomial test and every degree cutoff large enough to contain it. -/
theorem expected_spectralTest_polynomial_tendsto_genus
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a : Fin k → ℝ) (p : ℝ[X]) (q : ℕ) (hp : p.natDegree ≤ q) :
    Tendsto (fun n => ∫ sample, spectralTest k t a n p.eval sample ∂probability k)
      atTop (𝓝 ((testRankCoefficient k q a p 0).eval t)) := by
  rw [testRankCoefficient_stable_degree a p hp]
  simp only [testRankCoefficient, Polynomial.eval_finset_sum, Polynomial.eval_smul, smul_eq_mul]
  have h := tendsto_finset_sum (Finset.range (p.natDegree+1)) (fun m _ =>
    (expected_spectralTest_power_tendsto_genus hk ht0 ht1 a m).const_mul (p.coeff m))
  apply h.congr'
  apply Eventually.of_forall
  intro n
  simp_rw [spectralTest_polynomial]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
  · intro m _
    exact (continuous_const.mul (continuous_spectralTest_power k t a n m)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The leading genus functional has the norm bound of a probability measure on
the deterministic spectral interval. -/
theorem testRankCoefficient_zero_abs_le
    {k q : ℕ} (hk : 0 < k) (a : Fin k → ℝ) (p : ℝ[X]) (hp : p.natDegree ≤ q)
    {K H : ℝ} (hK : (∑ i, |a i|) ≤ K)
    (hb : ∀ x ∈ Icc (-K) K, |p.eval x| ≤ H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(testRankCoefficient k q a p 0).eval t| ≤ H := by
  apply le_of_tendsto' (expected_spectralTest_polynomial_tendsto_genus hk ht.1 ht.2 a p q hp).abs
  intro n
  have hb' : ∀ᵐ sample ∂probability k, ‖spectralTest k t a n p.eval sample‖ ≤ H :=
    Eventually.of_forall fun sample => by
      simpa only [Real.norm_eq_abs] using spectralTest_abs_le k t a n hK hb sample
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const hb'

/-- The same limit is positive on polynomials nonnegative on the spectral interval. -/
theorem testRankCoefficient_zero_nonneg
    {k q : ℕ} (hk : 0 < k) (a : Fin k → ℝ) (p : ℝ[X]) (hp : p.natDegree ≤ q)
    {K : ℝ} (hK : (∑ i, |a i|) ≤ K)
    (hb : ∀ x ∈ Icc (-K) K, 0 ≤ p.eval x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (testRankCoefficient k q a p 0).eval t := by
  apply ge_of_tendsto' (expected_spectralTest_polynomial_tendsto_genus hk ht.1 ht.2 a p q hp)
  intro n
  apply integral_nonneg
  intro sample
  apply integral_nonneg_of_ae
  exact (spectralMeasure_ae_mem k t a n sample hK).mono fun x hx => hb x hx

#print axioms expected_spectralTest_polynomial_tendsto_genus
#print axioms testRankCoefficient_zero_abs_le
#print axioms testRankCoefficient_zero_nonneg
end ProjectionChannels.Canonical
