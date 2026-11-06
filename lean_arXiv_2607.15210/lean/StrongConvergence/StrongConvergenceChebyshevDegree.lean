import StrongConvergence.StrongConvergenceSmoothSpectralTests

open Polynomial
noncomputable section
namespace ProjectionChannels
namespace PolyChebyshev

/-- The recurrence bounds the degree of the `n`th Chebyshev polynomial. -/
theorem natDegree_T_nat_le (n : ℕ) : (Chebyshev.T ℝ (n : ℤ)).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
    have hcast : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
    rw [hcast, Chebyshev.T_add_two]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply Polynomial.natDegree_mul_le.trans
      have hfirst : (2 * (X : ℝ[X])).natDegree ≤ 1 := by
        simpa only [map_ofNat] using
          (Polynomial.natDegree_C_mul_le (2 : ℝ) (X : ℝ[X])).trans Polynomial.natDegree_X_le
      have h1' : (Chebyshev.T ℝ ((n : ℤ)+1)).natDegree ≤ n+1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using h1
      omega
    · omega

/-- Negative Chebyshev indices agree with their absolute indices. -/
theorem natDegree_T_le_natAbs (j : ℤ) : (Chebyshev.T ℝ j).natDegree ≤ j.natAbs := by
  rw [← Chebyshev.T_natAbs]
  exact natDegree_T_nat_le _

end PolyChebyshev
namespace Canonical

theorem scaledChebyshev_natDegree_le (K : ℝ) (j : ℤ) :
    (scaledChebyshev K j).natDegree ≤ j.natAbs := by
  apply Polynomial.natDegree_comp_le.trans
  have hlin : (C K⁻¹ * (X : ℝ[X])).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  calc
    _ ≤ (Chebyshev.T ℝ j).natDegree * 1 := Nat.mul_le_mul_left _ hlin
    _ ≤ j.natAbs := by simpa only [mul_one] using PolyChebyshev.natDegree_T_le_natAbs j

theorem scaledChebyshev_natDegree_le_succ (K : ℝ) (j : ℤ) :
    (scaledChebyshev K j).natDegree ≤ j.natAbs + 1 :=
  (scaledChebyshev_natDegree_le K j).trans (Nat.le_add_right _ _)

#print axioms scaledChebyshev_natDegree_le
end Canonical
end ProjectionChannels
