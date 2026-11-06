import StrongConvergence.StrongConvergencePolyChebyshev
import StrongConvergence.StrongConvergencePolyOrthogonality
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-! The sum of the absolute coefficients of a Chebyshev polynomial grows at
most as `3^n`. These estimates control ordinary coefficients when the
polynomial method uses Chebyshev expansions. -/

open Polynomial Set
open scoped BigOperators

namespace ProjectionChannels.StrongConvergence

noncomputable def coefficientMass (p : Polynomial ℝ) : ℝ := ∑' n : ℕ, |p.coeff n|

theorem summable_abs_coeff (p : Polynomial ℝ) : Summable (fun n : ℕ => |p.coeff n|) := by
  apply summable_of_ne_finset_zero (s := p.support)
  intro n hn
  have hc : p.coeff n = 0 := by simpa using hn
  simp [hc]

theorem coefficientMass_nonneg (p : Polynomial ℝ) : 0 ≤ coefficientMass p :=
  tsum_nonneg (fun _ => abs_nonneg _)

@[simp] theorem coefficientMass_zero : coefficientMass (0 : Polynomial ℝ) = 0 := by
  simp [coefficientMass]

@[simp] theorem coefficientMass_one : coefficientMass (1 : Polynomial ℝ) = 1 := by
  simp [coefficientMass, Polynomial.coeff_one, apply_ite]

theorem coefficientMass_add_le (p q : Polynomial ℝ) :
    coefficientMass (p + q) ≤ coefficientMass p + coefficientMass q := by
  unfold coefficientMass
  calc
    _ ≤ ∑' n : ℕ, (|p.coeff n| + |q.coeff n|) :=
      Summable.tsum_le_tsum (fun n => by simpa using abs_add_le (p.coeff n) (q.coeff n))
        (summable_abs_coeff (p + q)) ((summable_abs_coeff p).add (summable_abs_coeff q))
    _ = _ := (summable_abs_coeff p).tsum_add (summable_abs_coeff q)

theorem coefficientMass_sub_le (p q : Polynomial ℝ) :
    coefficientMass (p - q) ≤ coefficientMass p + coefficientMass q := by
  unfold coefficientMass
  calc
    _ ≤ ∑' n : ℕ, (|p.coeff n| + |q.coeff n|) :=
      Summable.tsum_le_tsum (fun n => by simpa using abs_sub (p.coeff n) (q.coeff n))
        (summable_abs_coeff (p - q)) ((summable_abs_coeff p).add (summable_abs_coeff q))
    _ = _ := (summable_abs_coeff p).tsum_add (summable_abs_coeff q)

@[simp] theorem coefficientMass_smul (c : ℝ) (p : Polynomial ℝ) :
    coefficientMass (c • p) = |c| * coefficientMass p := by
  simp only [coefficientMass, Polynomial.coeff_smul, smul_eq_mul, abs_mul]
  exact tsum_mul_left

@[simp] theorem coefficientMass_X_mul (p : Polynomial ℝ) :
    coefficientMass (X * p) = coefficientMass p := by
  unfold coefficientMass
  rw [(summable_abs_coeff (X * p)).tsum_eq_zero_add]
  simp [Polynomial.coeff_X_mul]

@[simp] theorem coefficientMass_X : coefficientMass (X : Polynomial ℝ) = 1 := by
  simpa using coefficientMass_X_mul (1 : Polynomial ℝ)

theorem coefficientMass_finset_sum_le {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℝ) :
    coefficientMass (∑ i ∈ s, p i) ≤ ∑ i ∈ s, coefficientMass (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (coefficientMass_add_le _ _).trans (add_le_add_left ih _)

/-- Absolute coefficient mass bound for the first-kind Chebyshev polynomial. -/
theorem coefficientMass_chebyshev_T_le (n : ℕ) :
    coefficientMass (Polynomial.Chebyshev.T ℝ (n : ℤ)) ≤ (3 : ℝ) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num
  | more n hn hn1 =>
    have hrec : Polynomial.Chebyshev.T ℝ ((n + 2 : ℕ) : ℤ) =
        (2 : ℝ) • (X * Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) -
          Polynomial.Chebyshev.T ℝ (n : ℤ) := by
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
        Polynomial.Chebyshev.T_add_two]
      simp only [Nat.cast_add, Nat.cast_one, smul_eq_C_mul, map_ofNat]
      ring
    rw [hrec]
    calc
      _ ≤ coefficientMass ((2 : ℝ) • (X * Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ))) +
          coefficientMass (Polynomial.Chebyshev.T ℝ (n : ℤ)) := coefficientMass_sub_le _ _
      _ = 2 * coefficientMass (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) +
          coefficientMass (Polynomial.Chebyshev.T ℝ (n : ℤ)) := by simp
      _ ≤ 2 * (3 : ℝ) ^ (n + 1) + (3 : ℝ) ^ n := by linarith
      _ ≤ (3 : ℝ) ^ (n + 2) := by
        simp only [pow_add, pow_one]
        norm_num
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n]

/-- The ordinary coefficient mass is bounded by an exponential in the degree
times the sup norm on the unit interval. -/
theorem coefficientMass_le_of_interval_bound (p : Polynomial ℝ) (D : ℕ) {M : ℝ}
    (hD : p.natDegree ≤ D)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    coefficientMass p ≤ (3 : ℝ) ^ (D + 1) * M := by
  have hM : 0 ≤ M := (abs_nonneg (p.eval 0)).trans (hb 0 (by constructor <;> norm_num))
  obtain ⟨c, hc⟩ := PolyChebyshev.exists_chebyshev_expansion p D hD
  have hg : (∑ i : Fin (D + 1), (3 : ℝ) ^ i.val) * 2 = (3 : ℝ) ^ (D + 1) - 1 := by
    have h := geom_sum_mul (3 : ℝ) (D + 1)
    norm_num at h
    simpa only [Fin.sum_univ_eq_sum_range] using h
  calc
    coefficientMass p = coefficientMass (∑ i, c i • Polynomial.Chebyshev.T ℝ (i.val : ℤ)) := by rw [hc]
    _ ≤ ∑ i, coefficientMass (c i • Polynomial.Chebyshev.T ℝ (i.val : ℤ)) :=
      coefficientMass_finset_sum_le Finset.univ _
    _ ≤ ∑ i : Fin (D + 1), (2 * M) * (3 : ℝ) ^ i.val := by
      apply Finset.sum_le_sum
      intro i _
      rw [coefficientMass_smul]
      exact mul_le_mul (abs_chebyshev_expansion_coeff_le_two p c hc hb i)
        (coefficientMass_chebyshev_T_le i.val) (coefficientMass_nonneg _) (by positivity)
    _ ≤ (3 : ℝ) ^ (D + 1) * M := by
      rw [← Finset.mul_sum]
      have hgm := congrArg (fun x : ℝ => M * x) hg
      nlinarith

/-- Rescaling the variable encodes the weighted coefficient mass. -/
theorem coefficientMass_comp_C_mul_X (p : Polynomial ℝ) {K : ℝ} (hK : 0 ≤ K) :
    coefficientMass (p.comp (C K * X)) = ∑' n : ℕ, |p.coeff n| * K ^ n := by
  simp [coefficientMass, Polynomial.comp_C_mul_X_coeff, abs_mul, abs_pow, abs_of_nonneg hK]

/-- The coefficient estimate needed to sum the moment-expansion errors.
It includes the degenerate interval `K = 0`. -/
theorem weighted_coefficientMass_le_of_interval_bound (p : Polynomial ℝ) (D : ℕ)
    {K M : ℝ} (hD : p.natDegree ≤ D) (hK : 0 ≤ K)
    (hb : ∀ x ∈ Icc (-K) K, |p.eval x| ≤ M) :
    (∑' n : ℕ, |p.coeff n| * K ^ n) ≤ (3 : ℝ) ^ (D + 1) * M := by
  let q := p.comp (C K * X)
  have hdeg : q.natDegree ≤ D := by
    have hlin : (C K * X : Polynomial ℝ).natDegree ≤ 1 := by
      simpa using Polynomial.natDegree_C_mul_le K (X : Polynomial ℝ)
    exact Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul_left p.natDegree hlin).trans (by simpa using hD))
  have hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |q.eval x| ≤ M := by
    intro x hx
    have hxK : K * x ∈ Icc (-K) K := by constructor <;> nlinarith [hx.1, hx.2]
    simpa [q, Polynomial.eval_comp] using hb (K * x) hxK
  rw [← coefficientMass_comp_C_mul_X p hK]
  exact coefficientMass_le_of_interval_bound q D hdeg hbound

theorem summable_abs_coeff_mul_pow (p : Polynomial ℝ) (K : ℝ) :
    Summable (fun n : ℕ => |p.coeff n| * K ^ n) := by
  apply summable_of_ne_finset_zero (s := p.support)
  intro n hn
  have hc : p.coeff n = 0 := by simpa using hn
  simp [hc]

/-- Finite-sum version, in the form used for the first `D` compression moments. -/
theorem sum_abs_coeff_mul_pow_le_of_interval_bound (p : Polynomial ℝ) (D : ℕ)
    {K M : ℝ} (hD : p.natDegree ≤ D) (hK : 0 ≤ K)
    (hb : ∀ x ∈ Icc (-K) K, |p.eval x| ≤ M) :
    (∑ n ∈ Finset.range (D + 1), |p.coeff n| * K ^ n) ≤ (3 : ℝ) ^ (D + 1) * M := by
  exact (Summable.sum_le_tsum (Finset.range (D + 1))
    (fun n _ => mul_nonneg (abs_nonneg _) (pow_nonneg hK n))
    (summable_abs_coeff_mul_pow p K)).trans
    (weighted_coefficientMass_le_of_interval_bound p D hD hK hb)

#print axioms coefficientMass_chebyshev_T_le
#print axioms weighted_coefficientMass_le_of_interval_bound

end ProjectionChannels.StrongConvergence
