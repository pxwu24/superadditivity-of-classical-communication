import StrongConvergence.StrongConvergencePowerSeriesEvaluation
import Mathlib.Tactic

/-! The algebraic passage from first-block convolution recurrences to the
native formal moment--cumulant substitution identity. -/
open PowerSeries
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.MomentCumulantRecurrence

section Algebra
variable {R : Type*} [CommRing R]

/-- Absorb the final convolution term using the empty-size boundary value. -/
theorem convolution_of_split_recurrence (M : ℕ → R) (B : ℕ → ℕ → R)
    (hzero : ∀ r, B 0 r = if r=0 then 1 else 0)
    (hrec : ∀ n r, B (n+1) (r+1) = (if r=0 then M n else 0) +
      ∑ p ∈ Finset.range n, M p*B (n-p) r) :
    ∀ n r, B (n+1) (r+1) = ∑ p ∈ Finset.range (n+1), M p*B (n-p) r := by
  intro n r
  rw [hrec, Finset.sum_range_succ, Nat.sub_self, hzero]
  split_ifs <;> ring

/-- The recursive block counts are exactly the coefficients of powers of
`X M(X)`. This assertion is over an arbitrary commutative coefficient ring. -/
theorem blockConvolution_eq_coeff (M : ℕ → R) (B : ℕ → ℕ → R)
    (hzero : ∀ r, B 0 r = if r=0 then 1 else 0)
    (hsucc_zero : ∀ n, B (n+1) 0=0)
    (hrec : ∀ n r, B (n+1) (r+1) = ∑ p ∈ Finset.range (n+1), M p*B (n-p) r)
    (n r : ℕ) :
    B n r = coeff R n ((X * mk M)^r) := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    cases n with
    | zero =>
      rw [hzero, coeff_zero_eq_constantCoeff_apply]
      simp only [map_pow, map_mul, constantCoeff_X, zero_mul]
      cases r <;> simp
    | succ n =>
      cases r with
      | zero => simp [hsucc_zero]
      | succ r =>
        rw [hrec, pow_succ', mul_assoc, coeff_succ_X_mul, coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_congr rfl
        intro p hp
        rw [coeff_mk, ih (n-p) (by omega) r]

end Algebra

/-- A finite coefficient formula for the native formal substitution. -/
theorem coeff_formalSubst_finite (F W : PowerSeries ℝ)
    (hW : constantCoeff ℝ W=0) (n : ℕ) :
    coeff ℝ n (FreeCumulant.formalSubst W hW F) =
      ∑ r ∈ Finset.range (n+1), coeff ℝ r F * coeff ℝ n (W^r) := by
  rw [PowerSeriesEvaluation.coeff_formalSubst]
  apply tsum_eq_sum
  intro r hr
  rw [PowerSeriesEvaluation.coeff_pow_eq_zero_of_lt hW (by
    simp only [Finset.mem_range, not_lt] at hr
    omega), mul_zero]

/-- The first-block moment recurrence implies the formal free-cumulant
identity, without any analytic convergence assumptions. -/
theorem formalSubst_of_convolution_recurrence (f M : ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (hf0 : f 0=0) (hM0 : M 0=1)
    (hzero : ∀ r, B 0 r = if r=0 then 1 else 0)
    (hsucc_zero : ∀ n, B (n+1) 0=0)
    (hrec : ∀ n r, B (n+1) (r+1) = ∑ p ∈ Finset.range (n+1), M p*B (n-p) r)
    (hMrec : ∀ n, M (n+1) = ∑ r ∈ Finset.range (n+2), f r*B (n+1) r) :
    FreeCumulant.formalSubst (X * mk M) (by simp) (mk f) = mk M-1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_formalSubst_finite]
  simp only [coeff_mk, map_sub]
  cases n with
  | zero => simp [hf0, hM0]
  | succ n =>
    rw [coeff_one, if_neg (Nat.succ_ne_zero n), sub_zero, hMrec]
    apply Finset.sum_congr rfl
    intro r hr
    rw [blockConvolution_eq_coeff M B hzero hsucc_zero hrec]

theorem formalSubst_of_split_recurrence (f M : ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (hf0 : f 0=0) (hM0 : M 0=1)
    (hzero : ∀ r, B 0 r = if r=0 then 1 else 0)
    (hsucc_zero : ∀ n, B (n+1) 0=0)
    (hrec : ∀ n r, B (n+1) (r+1) = (if r=0 then M n else 0) +
      ∑ p ∈ Finset.range n, M p*B (n-p) r)
    (hMrec : ∀ n, M (n+1) = ∑ r ∈ Finset.range (n+2), f r*B (n+1) r) :
    FreeCumulant.formalSubst (X * mk M) (by simp) (mk f) = mk M-1 :=
  formalSubst_of_convolution_recurrence f M B hf0 hM0 hzero hsucc_zero
    (convolution_of_split_recurrence M B hzero hrec) hMrec

#print axioms formalSubst_of_convolution_recurrence
end ProjectionChannels.MomentCumulantRecurrence
