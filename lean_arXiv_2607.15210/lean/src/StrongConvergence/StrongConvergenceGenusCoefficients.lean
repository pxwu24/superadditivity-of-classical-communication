import StrongConvergence.StrongConvergenceGenusTail
import StrongConvergence.StrongConvergenceGenusTruncation
import StrongConvergence.StrongConvergencePolyInterpolation

/-! Polynomial dependence on the exact rank density in the genus expansion.
These polynomials supply the finite-dimensional interpolation variables. -/

open Polynomial
open scoped BigOperators

noncomputable section
namespace ProjectionChannels.TensorHaar

def genusRankCoefficient (k m : ℕ) (a : Fin k → ℝ) (j : ℕ) : ℝ[X] :=
  ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
    ∑ l ∈ Finset.range (j + (m - 1) + 1),
      C ((-1 : ℝ) ^ l * genusWeight a σ *
        (genusNumerator σ τ l).coeff (j + (m - 1))) * X ^ cycleCount τ

theorem genusRankCoefficient_natDegree_le {k m : ℕ} (a : Fin k → ℝ) (j : ℕ) :
    (genusRankCoefficient k m a j).natDegree ≤ m := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro τ _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro l _
  rw [C_mul_X_pow_eq_monomial]
  exact (natDegree_monomial_le _).trans (cycleCount_le τ)

theorem genusRankCoefficient_eval_base {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (j : ℕ) :
    (genusRankCoefficient k m a j).eval s =
      (genusMomentPolynomial k m a s (j + (m - 1))).coeff j := by
  rw [genusMomentPolynomial_coeff hm, genusMomentNumerator_expansion]
  simp only [genusRankCoefficient, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Every retained coefficient is independent of the auxiliary Neumann cutoff
once the cutoff is large enough. Its rank dependence is a genuine polynomial. -/
theorem genusRankCoefficient_eval {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (j L : ℕ) (hL : j + (m - 1) ≤ L) :
    (genusRankCoefficient k m a j).eval s =
      (genusMomentPolynomial k m a s L).coeff j := by
  rw [genusMomentPolynomial_coeff_stable hm a s j L hL]
  exact genusRankCoefficient_eval_base hm a s j

theorem genusRankCoefficient_odd {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (j : ℕ) (hj : j % 2 = 1) :
    genusRankCoefficient k m a j = 0 := by
  apply Polynomial.funext
  intro s
  rw [genusRankCoefficient_eval_base hm, genusMomentPolynomial_odd_coeff hm _ _ _ _ hj]
  simp

@[simp] theorem genusRankCoefficient_one {k m : ℕ} (hm : 0 < m) (a : Fin k → ℝ) :
    genusRankCoefficient k m a 1 = 0 :=
  genusRankCoefficient_odd hm a 1 rfl

/-- The inverse-dimension truncation, with rank-polynomial coefficients. -/
def genusRankTruncation (k m : ℕ) (a : Fin k → ℝ) (R : ℕ) (s : ℝ) : ℝ[X] :=
  PolyChebyshev.xPolynomial (fun i : Fin (R + 1) => genusRankCoefficient k m a i.val) s

theorem genusRankTruncation_natDegree_le {k m : ℕ} (a : Fin k → ℝ) (R : ℕ) (s : ℝ) :
    (genusRankTruncation k m a R s).natDegree ≤ R :=
  PolyChebyshev.xPolynomial_natDegree_le _ _

/-- The rank-polynomial construction is exactly the degree truncation used in
the analytic error estimate, independently of the larger Neumann cutoff. -/
theorem genusRankTruncation_eq_degreeTruncation {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (R : ℕ) (s : ℝ) (L : ℕ) (hL : R + (m - 1) ≤ L) :
    genusRankTruncation k m a R s = degreeTruncation R (genusMomentPolynomial k m a s L) := by
  rw [genusRankTruncation, PolyChebyshev.xPolynomial, degreeTruncation,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [C_mul_X_pow_eq_monomial, genusRankCoefficient_eval hm a s i.val L (by omega)]

/-- The zeroth moment is one; the positive moments use the genus expansion. -/
def normalizedMomentCoefficient (k m : ℕ) (a : Fin k → ℝ) (j : ℕ) : ℝ[X] :=
  if m = 0 then (if j = 0 then 1 else 0) else genusRankCoefficient k m a j

theorem normalizedMomentCoefficient_natDegree_le {k m : ℕ} (a : Fin k → ℝ) (j : ℕ) :
    (normalizedMomentCoefficient k m a j).natDegree ≤ m := by
  unfold normalizedMomentCoefficient
  split_ifs <;> simp_all [genusRankCoefficient_natDegree_le]

theorem normalizedMomentCoefficient_odd {k m : ℕ}
    (a : Fin k → ℝ) (j : ℕ) (hj : j % 2 = 1) :
    normalizedMomentCoefficient k m a j = 0 := by
  unfold normalizedMomentCoefficient
  split_ifs with hm hj0
  · omega
  · rfl
  · exact genusRankCoefficient_odd (Nat.pos_of_ne_zero hm) a j hj

/-- Rank-polynomial coefficients for an arbitrary polynomial spectral test. -/
def testRankCoefficient (k q : ℕ) (a : Fin k → ℝ) (p : ℝ[X]) (j : ℕ) : ℝ[X] :=
  ∑ m ∈ Finset.range (q + 1), p.coeff m • normalizedMomentCoefficient k m a j

theorem testRankCoefficient_natDegree_le {k q : ℕ}
    (a : Fin k → ℝ) (p : ℝ[X]) (j : ℕ) :
    (testRankCoefficient k q a p j).natDegree ≤ q := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply (natDegree_smul_le _ _).trans
  exact (normalizedMomentCoefficient_natDegree_le a j).trans (by have := Finset.mem_range.mp hm; omega)

theorem testRankCoefficient_odd {k q : ℕ}
    (a : Fin k → ℝ) (p : ℝ[X]) (j : ℕ) (hj : j % 2 = 1) :
    testRankCoefficient k q a p j = 0 := by
  simp only [testRankCoefficient, normalizedMomentCoefficient_odd a j hj, smul_zero,
    Finset.sum_const_zero]

/-- Evaluation of a polynomial test is the same finite linear combination
of the normalized monomial approximants. -/
theorem testRankCoefficient_truncation_eval {k q R : ℕ}
    (a : Fin k → ℝ) (p : ℝ[X]) (s x : ℝ) :
    (PolyChebyshev.xPolynomial
      (fun i : Fin (R + 1) => testRankCoefficient k q a p i.val) s).eval x =
      ∑ m ∈ Finset.range (q + 1), p.coeff m *
        (PolyChebyshev.xPolynomial
          (fun i : Fin (R + 1) => normalizedMomentCoefficient k m a i.val) s).eval x := by
  simp only [PolyChebyshev.xPolynomial, testRankCoefficient, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms genusRankCoefficient_eval
#print axioms genusRankCoefficient_odd
#print axioms testRankCoefficient_natDegree_le
#print axioms genusRankTruncation_eq_degreeTruncation

end ProjectionChannels.TensorHaar
