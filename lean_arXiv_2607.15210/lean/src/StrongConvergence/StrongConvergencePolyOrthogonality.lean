import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Tactic

/-! Orthogonality of cosine modes and sup-norm bounds for the coefficients
of a finite Chebyshev expansion. -/

open Set Polynomial
open scoped BigOperators Interval

namespace ProjectionChannels.StrongConvergence

theorem integral_cos_int_mul_pi (n : ℤ) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos ((n : ℝ) * x)) =
      if n = 0 then Real.pi else 0 := by
  split_ifs with hn
  · simp [hn]
  · rw [intervalIntegral.integral_comp_mul_left Real.cos (by exact_mod_cast hn)]
    simp [integral_cos, Real.sin_int_mul_pi]

theorem integral_cos_nat_mul_cos_nat (i j : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi,
      Real.cos ((i : ℝ) * x) * Real.cos ((j : ℝ) * x)) =
      if i = j then (if i = 0 then Real.pi else Real.pi / 2) else 0 := by
  have hpoint : (fun x : ℝ => 2 * (Real.cos ((i : ℝ) * x) * Real.cos ((j : ℝ) * x))) =
      fun x => Real.cos ((((i : ℤ) - (j : ℤ) : ℤ) : ℝ) * x) +
        Real.cos ((((i : ℤ) + (j : ℤ) : ℤ) : ℝ) * x) := by
    funext x
    have h := Real.two_mul_cos_mul_cos ((i : ℝ) * x) ((j : ℝ) * x)
    simpa [sub_mul, add_mul, mul_assoc] using h
  have hint := congrArg (fun f : ℝ → ℝ => ∫ x in (0 : ℝ)..Real.pi, f x) hpoint
  dsimp only at hint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add] at hint
  · rw [integral_cos_int_mul_pi, integral_cos_int_mul_pi] at hint
    split_ifs with hij hi
    · subst j
      subst i
      norm_num at hint ⊢
    · subst j
      have hsum : (i : ℤ) + (i : ℤ) ≠ 0 := by omega
      simp [hsum] at hint
      linarith
    · have hdiff : (i : ℤ) - (j : ℤ) ≠ 0 := by omega
      have hsum : (i : ℤ) + (j : ℤ) ≠ 0 := by omega
      simp [hdiff, hsum] at hint
      linarith
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.cos ((((i : ℤ) - (j : ℤ) : ℤ) : ℝ) * x))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.cos ((((i : ℤ) + (j : ℤ) : ℤ) : ℝ) * x))).intervalIntegrable _ _

/-- Integrating against one cosine mode extracts one Chebyshev coefficient. -/
theorem integral_chebyshev_expansion_cos {D : ℕ} (p : Polynomial ℝ)
    (c : Fin (D + 1) → ℝ)
    (hexp : ∑ i, c i • Polynomial.Chebyshev.T ℝ (i.val : ℤ) = p)
    (j : Fin (D + 1)) :
    (∫ x in (0 : ℝ)..Real.pi, p.eval (Real.cos x) * Real.cos ((j.val : ℝ) * x)) =
      c j * (if j.val = 0 then Real.pi else Real.pi / 2) := by
  have hpoint (x : ℝ) : p.eval (Real.cos x) =
      ∑ i, c i * Real.cos ((i.val : ℝ) * x) := by
    have h := congrArg (fun q : Polynomial ℝ => q.eval (Real.cos x)) hexp
    simpa [Polynomial.eval_finset_sum, Polynomial.eval_smul] using h.symm
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi,
        ∑ i, c i * (Real.cos ((i.val : ℝ) * x) * Real.cos ((j.val : ℝ) * x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [hpoint, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, c i * ∫ x in (0 : ℝ)..Real.pi,
        Real.cos ((i.val : ℝ) * x) * Real.cos ((j.val : ℝ) * x) := by
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i _
        exact intervalIntegral.integral_const_mul _ _
      · intro i _
        exact (by fun_prop : Continuous (fun x : ℝ =>
          c i * (Real.cos ((i.val : ℝ) * x) * Real.cos ((j.val : ℝ) * x)))).intervalIntegrable _ _
    _ = _ := by
      simp only [integral_cos_nat_mul_cos_nat, Fin.val_inj]
      simp

/-- Uniform bounds on a polynomial give the standard coefficient bounds in
its finite Chebyshev expansion. -/
theorem abs_chebyshev_expansion_coeff_le {D : ℕ} (p : Polynomial ℝ)
    (c : Fin (D + 1) → ℝ) {M : ℝ}
    (hexp : ∑ i, c i • Polynomial.Chebyshev.T ℝ (i.val : ℤ) = p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    (j : Fin (D + 1)) :
    |c j| ≤ if j.val = 0 then M else 2 * M := by
  have hM : 0 ≤ M := (abs_nonneg (p.eval 0)).trans (hb 0 (by constructor <;> norm_num))
  have hpoint (x : ℝ) : ‖p.eval (Real.cos x) * Real.cos ((j.val : ℝ) * x)‖ ≤ M := by
    rw [Real.norm_eq_abs, abs_mul]
    have hp := hb (Real.cos x) ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
    calc
      _ ≤ M * 1 := mul_le_mul hp (Real.abs_cos_le_one _) (abs_nonneg _) hM
      _ = M := mul_one _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.pi) (fun x _ => hpoint x)
  rw [integral_chebyshev_expansion_cos p c hexp j, Real.norm_eq_abs, abs_mul] at h
  simp only [sub_zero, abs_of_pos Real.pi_pos] at h
  split_ifs with hj
  · simp only [hj, if_true, abs_of_pos Real.pi_pos] at h
    nlinarith [Real.pi_pos]
  · simp only [hj, if_false, abs_of_pos (half_pos Real.pi_pos)] at h
    nlinarith [Real.pi_pos]

theorem abs_chebyshev_expansion_coeff_le_two {D : ℕ} (p : Polynomial ℝ)
    (c : Fin (D + 1) → ℝ) {M : ℝ}
    (hexp : ∑ i, c i • Polynomial.Chebyshev.T ℝ (i.val : ℤ) = p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    (j : Fin (D + 1)) : |c j| ≤ 2 * M := by
  have h := abs_chebyshev_expansion_coeff_le p c hexp hb j
  split_ifs at h with hj
  · have hM : 0 ≤ M := (abs_nonneg (c j)).trans h
    linarith
  · exact h

#print axioms integral_cos_nat_mul_cos_nat
#print axioms abs_chebyshev_expansion_coeff_le

end ProjectionChannels.StrongConvergence
