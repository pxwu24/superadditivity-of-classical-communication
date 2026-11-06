import StrongConvergence.StrongConvergencePolyCoeffNorm
import StrongConvergence.StrongConvergenceGenusCoefficients
import StrongConvergence.StrongConvergenceGenusMomentBound
import StrongConvergence.StrongConvergenceSmoothSpectralTests

/-! Weighted monomial errors for polynomial spectral tests. -/
open Polynomial Set
open scoped BigOperators
noncomputable section

namespace ProjectionChannels.StrongConvergence

lemma genus_test_exponential_constant (q : ℕ) (hq : 0 < q) :
    4 * (q : ℝ)^2 * (3 : ℝ)^(q+1) ≤ 5 * (8 : ℝ)^q * (q : ℝ)^q := by
  have hpow : 4 * (3 : ℝ)^(q+1) ≤ 5 * (8 : ℝ)^q := by
    induction q, hq using Nat.le_induction with
    | base => norm_num
    | succ q hq ih =>
      rw [show q+1+1 = (q+1)+1 from rfl, pow_succ 3 (q+1), pow_succ 8 q]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) q]
  have hqp : (q : ℝ)^2 ≤ (q : ℝ)^q := by
    by_cases hq1 : q = 1
    · simp [hq1]
    · exact pow_le_pow_right₀ (by exact_mod_cast hq : (1 : ℝ) ≤ q) (by omega)
  calc
    _ = (4 * (3 : ℝ)^(q+1)) * (q : ℝ)^2 := by ring
    _ ≤ (5 * (8 : ℝ)^q) * (q : ℝ)^q :=
      mul_le_mul hpow hqp (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- The exponential coefficient loss is absorbed by the uniform genus tail. -/
theorem polynomial_error_of_monomial_errors (p : ℝ[X]) (q : ℕ)
    {K H N : ℝ} (hq : 0 < q) (hN : 0 < N) (hK : 0 ≤ K)
    (hdeg : p.natDegree ≤ q) (hb : ∀ x ∈ Icc (-K) K, |p.eval x| ≤ H)
    (u v : ℕ → ℝ)
    (herr : ∀ m ∈ Finset.range (q+1), |u m-v m| ≤
      4*(q:ℝ)^2*K^m/((8:ℝ)^q*(q:ℝ)^q*N^2)) :
    |(∑ m ∈ Finset.range (q+1), p.coeff m*u m) -
      (∑ m ∈ Finset.range (q+1), p.coeff m*v m)| ≤ 5*H/N^2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hden : 0 < (8:ℝ)^q*(q:ℝ)^q*N^2 := by positivity
  have hH : 0 ≤ H := (abs_nonneg (p.eval 0)).trans (hb 0 ⟨by linarith, hK⟩)
  calc
    _ = |∑ m ∈ Finset.range (q+1), p.coeff m*(u m-v m)| := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ ∑ m ∈ Finset.range (q+1), |p.coeff m| * |u m-v m| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun m => p.coeff m*(u m-v m)) (Finset.range (q+1))
    _ ≤ ∑ m ∈ Finset.range (q+1), |p.coeff m| *
        (4*(q:ℝ)^2*K^m/((8:ℝ)^q*(q:ℝ)^q*N^2)) := by
      exact Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (herr m hm) (abs_nonneg _))
    _ = (4*(q:ℝ)^2/((8:ℝ)^q*(q:ℝ)^q*N^2))*
        (∑ m ∈ Finset.range (q+1), |p.coeff m| *K^m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ (4*(q:ℝ)^2/((8:ℝ)^q*(q:ℝ)^q*N^2))*((3:ℝ)^(q+1)*H) := by
      exact mul_le_mul_of_nonneg_left
        (sum_abs_coeff_mul_pow_le_of_interval_bound p q hdeg hK hb) (by positivity)
    _ = (4*(q:ℝ)^2*(3:ℝ)^(q+1))*H/((8:ℝ)^q*(q:ℝ)^q*N^2) := by ring
    _ ≤ (5*(8:ℝ)^q*(q:ℝ)^q)*H/((8:ℝ)^q*(q:ℝ)^q*N^2) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (genus_test_exponential_constant q hq) hH) hden.le
    _ = 5*H/N^2 := by field_simp; ring

end ProjectionChannels.StrongConvergence

namespace ProjectionChannels.Canonical
open MeasureTheory TensorHaar PolyChebyshev

lemma integral_spectralTest_power (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n m : ℕ) :
    (∫ sample, spectralTest k t a n (fun x => x^m) sample ∂probability k) =
      if m=0 then 1 else (expectedNormalizedMoment k t n (m-1) a).re := by
  cases m with
  | zero => simp [spectralTest, StrongConvergenceMoments.integral_empiricalMeasure]
  | succ m => simpa using integral_spectralTest_power_succ k t a n m

lemma spectralTest_polynomial_of_degree (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n q : ℕ)
    (p : ℝ[X]) (hp : p.natDegree ≤ q) (sample : Sample k) :
    spectralTest k t a n p.eval sample =
      ∑ m ∈ Finset.range (q+1), p.coeff m * spectralTest k t a n (fun x => x^m) sample := by
  rw [spectralTest_polynomial]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hp 1))
  intro m hm hnot
  have hmdeg : p.natDegree < m := by simpa using hnot
  rw [coeff_eq_zero_of_natDegree_lt hmdeg, zero_mul]

lemma integral_spectralTest_polynomial_of_degree (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (n q : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ q) :
    (∫ sample, spectralTest k t a n p.eval sample ∂probability k) =
      ∑ m ∈ Finset.range (q+1), p.coeff m *
        (if m=0 then 1 else (expectedNormalizedMoment k t n (m-1) a).re) := by
  simp_rw [spectralTest_polynomial_of_degree k t a n q p hp]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul, integral_spectralTest_power]
  · intro m hm
    exact ((continuous_spectralTest_power k t a n m).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _

lemma expected_spectralTest_abs_le (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    {f : ℝ → ℝ} {K H : ℝ} (hK : (∑ i, |a i|) ≤ K)
    (hf : ∀ x ∈ Icc (-K) K, |f x| ≤ H) :
    |∫ sample, spectralTest k t a n f sample ∂probability k| ≤ H := by
  have hb : ∀ᵐ sample ∂probability k, ‖spectralTest k t a n f sample‖ ≤ H :=
    Filter.Eventually.of_forall fun sample => by
      simpa only [Real.norm_eq_abs] using spectralTest_abs_le k t a n hK hf sample
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const hb

lemma normalizedMomentCoefficient_zero_truncation (k R : ℕ) (a : Fin k → ℝ) (s : ℝ) :
    xPolynomial (fun i : Fin (R+1) => normalizedMomentCoefficient k 0 a i.val) s = 1 := by
  classical
  unfold xPolynomial
  rw [Finset.sum_eq_single (0 : Fin (R+1))]
  · simp [normalizedMomentCoefficient]
  · intro i hi hi0
    have hv : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    simp [normalizedMomentCoefficient, hv]
  · simp

/-- The actual monomial expectation obeys the uniform genus truncation bound,
including the constant monomial. -/
lemma expected_power_truncation_error {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0≤t) (ht1 : t≤1) (n q m : ℕ)
    (hmq : m≤q) (hqn : q≤n+1) (a : Fin k → ℝ)
    (hN : 8*q^4≤(n+1)*k) :
    |(if m=0 then 1 else (expectedNormalizedMoment k t n (m-1) a).re) -
      (xPolynomial (fun i : Fin (2*q+1) => normalizedMomentCoefficient k m a i.val)
        ((rankSequence k t n:ℝ)/(((n+1)*k:ℕ):ℝ))).eval
          ((((n+1)*k:ℕ):ℝ)⁻¹)| ≤
      4*(q:ℝ)^2*(∑ i, |a i|)^m/
        ((8:ℝ)^q*(q:ℝ)^q*((((n+1)*k:ℕ):ℝ)^2)) := by
  cases m with
  | zero =>
    rw [normalizedMomentCoefficient_zero_truncation]
    simp only [ite_true, eval_one, sub_self, abs_zero]
    positivity
  | succ m =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
      normalizedMomentCoefficient]
    change |(expectedNormalizedMoment k t n m a).re -
      (genusRankTruncation k (m+1) a (2*q)
        ((rankSequence k t n:ℝ)/(((n+1)*k:ℕ):ℝ))).eval _| ≤ _
    rw [genusRankTruncation_eq_degreeTruncation (Nat.succ_pos m) a (2*q) _
      (2*q+(m+1)) (by omega)]
    have h := expectedNormalizedMoment_degree_uniform_error hk ht0 ht1 n m q
      (by omega) hmq a hN
    have hre := Complex.abs_re_le_norm
      (expectedNormalizedMoment k t n m a - complexPolynomialEval
        ((((n+1)*k:ℕ):ℝ)⁻¹)
        (degreeTruncation (2*q) (genusMomentPolynomial k (m+1) a
          ((rankSequence k t n:ℝ)/(((n+1)*k:ℕ):ℝ)) (2*q+(m+1)))))
    simpa only [Complex.sub_re, complexPolynomialEval_apply,
      Complex.ofReal_re] using hre.trans h

/-- B3a for the actual expected polynomial trace, with no assumed moment error. -/
theorem expected_polynomial_truncation_error {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0≤t) (ht1 : t≤1) (n q : ℕ)
    (hq : 0<q) (hqn : q≤n+1) (a : Fin k → ℝ) (p : ℝ[X])
    (hdeg : p.natDegree≤q) {H : ℝ}
    (hb : ∀ x ∈ Icc (-(∑ i, |a i|)) (∑ i, |a i|), |p.eval x|≤H)
    (hN : 8*q^4≤(n+1)*k) :
    |(∫ sample, spectralTest k t a n p.eval sample ∂probability k) -
      (xPolynomial (fun i : Fin (2*q+1) => testRankCoefficient k q a p i.val)
        ((rankSequence k t n:ℝ)/(((n+1)*k:ℕ):ℝ))).eval
          ((((n+1)*k:ℕ):ℝ)⁻¹)| ≤ 5*H/((((n+1)*k:ℕ):ℝ)^2) := by
  rw [integral_spectralTest_polynomial_of_degree k t a n q p hdeg,
    testRankCoefficient_truncation_eval]
  exact StrongConvergence.polynomial_error_of_monomial_errors p q hq
    (by exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hk)
    (Finset.sum_nonneg (fun i _ => abs_nonneg (a i))) hdeg hb _ _
    (fun m hm => expected_power_truncation_error hk ht0 ht1 n q m
      (by have := Finset.mem_range.mp hm; omega) hqn a hN)

#print axioms expected_polynomial_truncation_error
end ProjectionChannels.Canonical
