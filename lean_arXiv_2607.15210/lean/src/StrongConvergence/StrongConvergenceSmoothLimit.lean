import StrongConvergence.StrongConvergenceChebyshevDegree
import StrongConvergence.StrongConvergenceGenusLimitTests
import StrongConvergence.StrongConvergenceGenusMaster
import Mathlib.Analysis.Normed.Group.Tannery

open MeasureTheory Filter Set Polynomial
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar StrongConvergenceMoments

/-- The genus-zero functional applied to a smooth Chebyshev expansion. -/
def smoothGenusValue (k : ℕ) (a : Fin k → ℝ) (K : ℝ) (c : ℤ → ℝ) (s : ℝ) : ℝ :=
  ∑' j : ℤ, c j * (testRankCoefficient k (j.natAbs+1) a (scaledChebyshev K j) 0).eval s

lemma scaledChebyshev_genus_abs_le {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ)
    {K : ℝ} (hK : 0 < K) (hKa : (∑i, |a i|) ≤ K) (j : ℤ)
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    |(testRankCoefficient k (j.natAbs+1) a (scaledChebyshev K j) 0).eval s| ≤ 1 :=
  testRankCoefficient_zero_abs_le hk a _ (scaledChebyshev_natDegree_le_succ K j)
    hKa (fun _ hx => scaledChebyshev_abs_le hK hx j) hs

lemma smoothGenusValue_hasSum {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ)
    {K : ℝ} (hK : 0 < K) (hKa : (∑i, |a i|) ≤ K)
    (c : ℤ → ℝ) (hc : Summable (fun j => |c j|))
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    HasSum (fun j : ℤ => c j * (testRankCoefficient k (j.natAbs+1) a
      (scaledChebyshev K j) 0).eval s) (smoothGenusValue k a K c s) := by
  apply Summable.hasSum
  apply Summable.of_norm_bounded _ hc
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (scaledChebyshev_genus_abs_le hk a hK hKa j hs) (abs_nonneg (c j))

/-- Expected smooth empirical tests converge to the explicit genus-zero
series, at every density including irrational densities and endpoints. -/
theorem expected_spectralTest_smooth_tendsto_genus {k : ℕ} {s : ℝ}
    (hk : 0 < k) (hs : s ∈ Icc (0:ℝ) 1) (a : Fin k → ℝ)
    {K : ℝ} (hK : 0 < K) (hKa : (∑i, |a i|) ≤ K)
    (c : ℤ → ℝ) (χ : ℝ → ℝ) (hc : Summable (fun j => |c j|))
    (hexp : ∀ x ∈ Icc (-K) K, HasSum
      (fun j => c j*(scaledChebyshev K j).eval x) (χ x)) :
    Tendsto (fun n => ∫ sample, spectralTest k s a n χ sample ∂probability k)
      atTop (𝓝 (smoothGenusValue k a K c s)) := by
  have hlim := tendsto_tsum_of_dominated_convergence (f := fun n j =>
      c j * ∫ sample, spectralTest k s a n (scaledChebyshev K j).eval sample ∂probability k)
    hc
    (fun j => (expected_spectralTest_polynomial_tendsto_genus hk hs.1 hs.2 a
      (scaledChebyshev K j) (j.natAbs+1) (scaledChebyshev_natDegree_le_succ K j)).const_mul (c j))
    (Eventually.of_forall fun n j => by
      rw [Real.norm_eq_abs, abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (expected_spectralTest_abs_le k s a n hKa (fun x hx => scaledChebyshev_abs_le hK hx j))
        (abs_nonneg (c j)))
  apply hlim.congr'
  exact Eventually.of_forall fun n =>
    (expected_spectralTest_chebyshev_hasSum k s a n hK hKa c χ hc hexp).tsum_eq

/-- Positivity of the actual spectral tests passes to the smooth genus
functional, without any continuity assumption on the density-dependent laws. -/
theorem smoothGenusValue_nonneg {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ)
    {K : ℝ} (hK : 0 < K) (hKa : (∑i, |a i|) ≤ K)
    (c : ℤ → ℝ) (χ : ℝ → ℝ) (hc : Summable (fun j => |c j|))
    (hexp : ∀ x ∈ Icc (-K) K, HasSum
      (fun j => c j*(scaledChebyshev K j).eval x) (χ x))
    (hχ : ∀x, 0 ≤ χ x) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    0 ≤ smoothGenusValue k a K c s := by
  apply ge_of_tendsto' (expected_spectralTest_smooth_tendsto_genus hk hs a hK hKa c χ hc hexp)
  intro n
  exact integral_nonneg fun sample => spectralTest_nonneg k s a n hχ sample

/-- The moment identities identify every polynomial genus test with its
integral against the actual limiting probability measure. -/
theorem testRankCoefficient_eval_eq_integral {k : ℕ} {t K : ℝ}
    (a : Fin k → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hs : ∀ᵐ x ∂ν, x ∈ Icc (-K) K)
    (hmom : ∀m : ℕ, (∫x, x^m ∂ν) = (normalizedMomentCoefficient k m a 0).eval t)
    (p : ℝ[X]) (q : ℕ) (hp : p.natDegree ≤ q) :
    (testRankCoefficient k q a p 0).eval t = ∫x, p.eval x ∂ν := by
  rw [testRankCoefficient_stable_degree a p hp,
    integral_polynomial_eq_moments hs p]
  simp only [testRankCoefficient, Polynomial.eval_finset_sum, Polynomial.eval_smul, smul_eq_mul]
  simp_rw [hmom]

/-- Identification of the smooth genus series with a law uses only its
moments, compact support, and the absolutely convergent Chebyshev expansion. -/
theorem smoothGenusValue_eq_integral {k : ℕ} {t : ℝ} (a : Fin k → ℝ)
    {K : ℝ} (hK : 0 < K) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hs : ∀ᵐ x ∂ν, x ∈ Icc (-K) K)
    (hmom : ∀m : ℕ, (∫x, x^m ∂ν) = (normalizedMomentCoefficient k m a 0).eval t)
    (c : ℤ → ℝ) (χ : ℝ → ℝ) (hc : Summable (fun j => |c j|))
    (hexp : ∀ x ∈ Icc (-K) K, HasSum
      (fun j => c j*(scaledChebyshev K j).eval x) (χ x)) :
    smoothGenusValue k a K c t = ∫x, χ x ∂ν := by
  have hi := StrongConvergence.hasSum_integrals_of_bounded_expansion ν c
    (fun j x => (scaledChebyshev K j).eval x) χ hc
    (fun j => (scaledChebyshev K j).continuous.aestronglyMeasurable)
    (fun j => hs.mono fun x hx => scaledChebyshev_abs_le hK hx j)
    (hs.mono fun x hx => hexp x hx)
  rw [smoothGenusValue]
  simp_rw [testRankCoefficient_eval_eq_integral a ν hs hmom _ _
    (scaledChebyshev_natDegree_le_succ K _)]
  exact hi.tsum_eq

#print axioms smoothGenusValue_nonneg
#print axioms smoothGenusValue_eq_integral
end ProjectionChannels.Canonical
