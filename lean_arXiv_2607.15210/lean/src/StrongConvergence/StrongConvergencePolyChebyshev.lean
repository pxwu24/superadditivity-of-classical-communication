import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic

/-! Chebyshev interval bounds and finite polynomial expansions used in the
polynomial method for Haar compression moments. -/

open Polynomial Set
open scoped BigOperators

namespace ProjectionChannels.PolyChebyshev

theorem abs_eval_T_le_one (n : ℤ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ n).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

theorem U_add_two_eq_add_two_T (n : ℤ) :
    Polynomial.Chebyshev.U ℝ (n + 2) = Polynomial.Chebyshev.U ℝ n +
      2 * Polynomial.Chebyshev.T ℝ (n + 2) := by
  have hU := Polynomial.Chebyshev.U_add_two ℝ n
  have hT := Polynomial.Chebyshev.T_eq_U_sub_X_mul_U ℝ (n + 2)
  have hi : n + 2 - 1 = n + 1 := by ring
  rw [hi] at hT
  linear_combination -hU - 2 * hT

theorem abs_eval_U_le (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x| ≤ (n : ℝ) + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      simp only [Nat.cast_one, Int.cast_one, Polynomial.Chebyshev.U_one,
        eval_mul, eval_ofNat, eval_X, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h : |x| ≤ 1 := abs_le.mpr hx
      linarith
  | more n hn _ =>
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
        U_add_two_eq_add_two_T, eval_add, eval_mul, eval_ofNat]
      have ht := abs_eval_T_le_one ((n : ℤ) + 2) hx
      have ha := abs_add ((Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x)
        (2 * (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 2)).eval x)
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ha
      push_cast
      linarith

theorem abs_eval_derivative_T_le (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval x| ≤ (n : ℝ) ^ 2 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Polynomial.Chebyshev.T_derivative_eq_U]
      have hi : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
      rw [hi, eval_mul]
      simp only [eval_intCast, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
        eval_add, eval_natCast, eval_one,
        abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      have h := mul_le_mul_of_nonneg_left (abs_eval_U_le n hx)
        (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      nlinarith

/-- Multiplication by `X` raises a Chebyshev index by at most one. -/
theorem X_mul_T_succ (n : ℕ) :
    (X : Polynomial ℝ) * Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) =
      (1 / 2 : ℝ) • (Polynomial.Chebyshev.T ℝ ((n + 2 : ℕ) : ℤ) +
        Polynomial.Chebyshev.T ℝ (n : ℤ)) := by
  have h := Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [smul_eq_C_mul]
  have hc : C (1 / 2 : ℝ) * (2 : Polynomial ℝ) = 1 := by
    have hc := congrArg (C : ℝ → Polynomial ℝ)
      (by norm_num : (1 / 2 : ℝ) * 2 = 1)
    simpa only [map_mul, map_ofNat, map_one] using hc
  linear_combination -(C (1 / 2 : ℝ)) * h -
    (X * Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)) * hc

noncomputable def chebyshevSpan (D : ℕ) : Submodule ℝ (Polynomial ℝ) :=
  Submodule.span ℝ (Set.range (fun i : Fin (D + 1) => Polynomial.Chebyshev.T ℝ (i.val : ℤ)))

theorem T_mem_chebyshevSpan {n D : ℕ} (hn : n ≤ D) :
    Polynomial.Chebyshev.T ℝ (n : ℤ) ∈ chebyshevSpan D :=
  Submodule.subset_span ⟨⟨n, by omega⟩, rfl⟩

theorem chebyshevSpan_mono {D E : ℕ} (hDE : D ≤ E) : chebyshevSpan D ≤ chebyshevSpan E := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact T_mem_chebyshevSpan (by omega)

theorem X_mul_mem_chebyshevSpan {D : ℕ} {p : Polynomial ℝ} (hp : p ∈ chebyshevSpan D) :
    X * p ∈ chebyshevSpan (D + 1) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      rcases Nat.eq_zero_or_pos i.val with hi | hi
      · simp only [hi, Int.cast_zero, Polynomial.Chebyshev.T_zero, mul_one]
        simpa using T_mem_chebyshevSpan (n := 1) (D := D + 1) (by omega)
      · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
        change X * Polynomial.Chebyshev.T ℝ (i.val : ℤ) ∈ chebyshevSpan (D + 1)
        rw [hn, Nat.succ_eq_add_one, X_mul_T_succ]
        apply Submodule.smul_mem
        apply Submodule.add_mem
        · exact T_mem_chebyshevSpan (by omega)
        · exact T_mem_chebyshevSpan (by omega)
  | zero => simp
  | add p q hp hq ihp ihq => simpa [mul_add] using Submodule.add_mem _ ihp ihq
  | smul c p hp ih => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ih

theorem X_pow_mem_chebyshevSpan (n : ℕ) :
    (X : Polynomial ℝ) ^ n ∈ chebyshevSpan n := by
  induction n with
  | zero => simpa using T_mem_chebyshevSpan (n := 0) (D := 0) le_rfl
  | succ n ih => simpa only [pow_succ', Nat.succ_eq_add_one] using X_mul_mem_chebyshevSpan ih

/-- Every polynomial of degree at most `D` has a finite Chebyshev expansion. -/
theorem exists_chebyshev_expansion (p : Polynomial ℝ) (D : ℕ) (hD : p.natDegree ≤ D) :
    ∃ c : Fin (D + 1) → ℝ,
      ∑ i, c i • Polynomial.Chebyshev.T ℝ (i.val : ℤ) = p := by
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mp
  change p ∈ chebyshevSpan D
  rw [p.as_sum_range' (D + 1) (by omega)]
  apply Submodule.sum_mem
  intro n hn
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul]
  apply Submodule.smul_mem
  exact chebyshevSpan_mono (by have := Finset.mem_range.mp hn; omega) (X_pow_mem_chebyshevSpan n)

#print axioms abs_eval_derivative_T_le
#print axioms exists_chebyshev_expansion

end ProjectionChannels.PolyChebyshev
