import StrongConvergence.StrongConvergenceGenusTail

/-! Degree-truncation bounds for the actual normalized Haar moment expansion. -/
open Polynomial Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

/-- Retain the coefficients through degree `R`. -/
def degreeTruncation (R : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ∑ j ∈ Finset.range (R + 1), Polynomial.monomial j (p.coeff j)

lemma degreeTruncation_coeff (R : ℕ) (p : ℝ[X]) (n : ℕ) :
    (degreeTruncation R p).coeff n = if n ≤ R then p.coeff n else 0 := by
  simp [degreeTruncation, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', Nat.lt_succ_iff]

lemma polynomial_sub_degreeTruncation (R : ℕ) (p : ℝ[X]) :
    p - degreeTruncation R p =
      ∑ j ∈ p.support.filter (fun j => R + 1 ≤ j), Polynomial.monomial j (p.coeff j) := by
  ext n
  rw [Polynomial.coeff_sub, degreeTruncation_coeff]
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.mem_filter, Polynomial.mem_support_iff]
  by_cases hn : n ≤ R
  · simp [hn, show ¬R + 1 ≤ n by omega]
  · by_cases hp : p.coeff n = 0
    · simp [hn, hp]
    · simp [hn, hp, show R + 1 ≤ n by omega]

lemma polynomial_eval_sub_degreeTruncation (R : ℕ) (p : ℝ[X]) (x : ℝ) :
    p.eval x - (degreeTruncation R p).eval x =
      ∑ j ∈ p.support.filter (fun j => R + 1 ≤ j), p.coeff j * x ^ j := by
  rw [← Polynomial.eval_sub, polynomial_sub_degreeTruncation]
  simp [Polynomial.eval_finset_sum, Polynomial.eval_monomial]

/-- Coefficientwise domination implies a quantitative degree-tail bound. -/
theorem degreeTruncation_error_le (R : ℕ) (p q : ℝ[X]) {C x y : ℝ}
    (hC : 0 ≤ C) (hq : ∀ n, 0 ≤ q.coeff n)
    (hpq : ∀ n, |p.coeff n| ≤ C * q.coeff n)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    |p.eval x - (degreeTruncation R p).eval x| ≤
      C * (x / y) ^ (R + 1) * q.eval y := by
  have hsupp : p.support.filter (fun j => R + 1 ≤ j) ⊆
      q.support.filter (fun j => R + 1 ≤ j) := by
    intro j hj
    obtain ⟨hj, hR⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Polynomial.mem_support_iff.mpr ?_, hR⟩
    intro hqj
    have h := hpq j
    rw [hqj, mul_zero] at h
    exact (Polynomial.mem_support_iff.mp hj)
      (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  rw [polynomial_eval_sub_degreeTruncation]
  calc
    _ ≤ ∑ j ∈ p.support.filter (fun j => R + 1 ≤ j), |p.coeff j * x ^ j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ p.support.filter (fun j => R + 1 ≤ j), |p.coeff j| * x ^ j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (pow_nonneg hx j)]
    _ ≤ ∑ j ∈ p.support.filter (fun j => R + 1 ≤ j), (C * q.coeff j) * x ^ j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hpq j) (pow_nonneg hx j)
    _ = C * ∑ j ∈ p.support.filter (fun j => R + 1 ≤ j), q.coeff j * x ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ C * ∑ j ∈ q.support.filter (fun j => R + 1 ≤ j), q.coeff j * x ^ j := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum_of_subset_of_nonneg hsupp
        (fun j _ _ => mul_nonneg (hq j) (pow_nonneg hx j))
    _ ≤ C * ((x / y) ^ (R + 1) * q.eval y) :=
      mul_le_mul_of_nonneg_left (nonnegative_polynomial_tail_le q (R + 1) hq hx hxy hy) hC
    _ = _ := by ring

lemma degreeTruncation_succ (R : ℕ) (p : ℝ[X]) :
    degreeTruncation (R + 1) p = degreeTruncation R p +
      Polynomial.monomial (R + 1) (p.coeff (R + 1)) := by
  exact Finset.sum_range_succ _ _

lemma degreeTruncation_even_eq_succ (R : ℕ) (p : ℝ[X])
    (heven : ∀ n, n % 2 = 1 → p.coeff n = 0) (hR : R % 2 = 0) :
    degreeTruncation (R + 1) p = degreeTruncation R p := by
  rw [degreeTruncation_succ, heven (R + 1) (by omega)]
  simp

/-- The coefficient-tail component for the concrete finite moment polynomial. -/
theorem genusMomentPolynomial_truncation_error {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (a : Fin k → ℝ) {s : ℝ} (hs : |s| ≤ 1) (L R : ℕ)
    {x : ℝ} (hx : 0 ≤ x) (hxy : x ≤ genusRadius m) :
    |(genusMomentPolynomial k m a s L).eval x -
      (degreeTruncation R (genusMomentPolynomial k m a s L)).eval x| ≤
      (∑ i, |a i|) ^ m * (x / genusRadius m) ^ (R + 1) *
        ((m.factorial : ℝ) / ((genusRadius m) ^ (m - 1) *
          (1 - genusRowError m (genusRadius m)))) := by
  have hypos := genusRadius_pos hm
  have hmajor := degreeTruncation_error_le R (genusMomentPolynomial k m a s L)
    (genusMajorantPolynomial m L) (C := (∑ i, |a i|) ^ m) (by positivity)
    (genusMajorantPolynomial_coeff_nonneg hm L)
    (genusMomentPolynomial_coeff_abs_le hk hm a hs L) hx hxy (genusRadius_pos hm)
  exact hmajor.trans (mul_le_mul_of_nonneg_left
    (genusMajorantPolynomial_eval_radius_le hm L) (by positivity))

/-- For even cutoffs, odd-coefficient cancellation gains one additional power. -/
theorem genusMomentPolynomial_truncation_error_even {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (a : Fin k → ℝ) {s : ℝ} (hs : |s| ≤ 1) (L R : ℕ) (hR : R % 2 = 0)
    {x : ℝ} (hx : 0 ≤ x) (hxy : x ≤ genusRadius m) :
    |(genusMomentPolynomial k m a s L).eval x -
      (degreeTruncation R (genusMomentPolynomial k m a s L)).eval x| ≤
      (∑ i, |a i|) ^ m * (x / genusRadius m) ^ (R + 2) *
        ((m.factorial : ℝ) / ((genusRadius m) ^ (m - 1) *
          (1 - genusRowError m (genusRadius m)))) := by
  have h := genusMomentPolynomial_truncation_error hk hm a hs L (R + 1) hx hxy
  rw [degreeTruncation_even_eq_succ R _
    (fun n hn => genusMomentPolynomial_odd_coeff hm a s L n hn) hR] at h
  exact h

#print axioms degreeTruncation_error_le
#print axioms genusMomentPolynomial_truncation_error_even
end ProjectionChannels.TensorHaar
