import StrongConvergence.StrongConvergenceTensorWeingarten
import StrongConvergence.StrongConvergenceFourthFinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Exact fourth-order projection coefficients. The finite combinatorial
certificates below are checked by Lean's kernel; no numerical oracle or
asymptotic-convergence assumption is used. -/

open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

theorem cycleCount_fourth (σ : Equiv.Perm (Fin 4)) :
    cycleCount σ = (fourthCycleNumber σ).val := by
  apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
  have h := fixedTupleCount_eq (E := Fin 2) σ
  simp only [Fintype.card_fin] at h
  exact h.symm.trans (fourthCycleNumber_certificate σ)

def fourthCoefficient (N d : ℂ) : Fin 5 → ℂ :=
  let D := (N^2-1)*(N^2-4)*(N^2-9)
  ![d*(N^4*d^3-6*N^3*d^2-8*N^2*d^3+19*N^2*d+24*N*d^2-30*N+6*d^3-6*d)/(N^2*D),
    d*(N-d)*(N^2*d^2-5*N*d-4*d^2+10)/(N*D),
    d*(N-d)*(N^3*d-N^2*d^2-4*N^2+6*N*d-6*d^2+6)/(N^2*D),
    d*(N-d)*(N^3*d-2*N^2*d^2-3*N^2+6*N*d+3*d^2-3)/(N^2*D),
    d*(N-d)*(N^2-5*N*d+5*d^2+1)/(N*D)]

def fourthGramRow (N : ℂ) (b : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![N^4*b 0 + 6*N^3*b 1 + 3*N^2*b 2 + 8*N^2*b 3 + 6*N*b 4,
    N^3*b 0 + (N^4+5*N^2)*b 1 + (N^3+2*N)*b 2 + (4*N^3+4*N)*b 3 + 6*N^2*b 4,
    N^2*b 0 + (2*N^3+4*N)*b 1 + (N^4+2*N^2)*b 2 + 8*N^2*b 3 + (4*N^3+2*N)*b 4,
    N^2*b 0 + (3*N^3+3*N)*b 1 + 3*N^2*b 2 + (N^4+7*N^2)*b 3 + (3*N^3+3*N)*b 4,
    N*b 0 + 6*N^2*b 1 + (2*N^3+N)*b 2 + (4*N^3+4*N)*b 3 + (N^4+5*N^2)*b 4]

theorem fourthGramRow_eq_histogram (N : ℂ) (b : Fin 5 → ℂ) (i : Fin 5) :
    (∑ j : Fin 5, ∑ r : Fin 5,
      (fourthGramHistogram i j r : ℂ) * (N ^ r.val * b j)) =
        fourthGramRow N b i := by
  fin_cases i <;> norm_num [fourthGramHistogram, fourthGramRow, Fin.sum_univ_succ, Fin.succ] <;> ring!

theorem fourthGramRow_eq_sum (N : ℂ) (b : Fin 5 → ℂ)
    (σ : Equiv.Perm (Fin 4)) :
    (∑ τ : Equiv.Perm (Fin 4), N ^ cycleCount (τ * σ.symm) * b (fourthClass τ)) =
      fourthGramRow N b (fourthClass σ) := by
  have h := Finset.sum_fiberwise' (s := (Finset.univ : Finset (Equiv.Perm (Fin 4))))
    (fun τ => (fourthClass τ, fourthCycleNumber (τ * σ.symm)))
    (fun v : Fin 5 × Fin 5 => N ^ v.2.val * b v.1)
  simp only [Finset.sum_const, nsmul_eq_mul, fourthGramHistogram_certificate] at h
  rw [Fintype.sum_prod_type] at h
  simp only [cycleCount_fourth]
  exact h.symm.trans (fourthGramRow_eq_histogram N b (fourthClass σ))

/-- Polynomial numerators after taking the common fourth-order denominator. -/
def fourthCoefficientNumerator (N d : ℂ) : Fin 5 → ℂ :=
  ![d*(N^4*d^3-6*N^3*d^2-8*N^2*d^3+19*N^2*d+24*N*d^2-30*N+6*d^3-6*d),
    N*(d*(N-d)*(N^2*d^2-5*N*d-4*d^2+10)),
    d*(N-d)*(N^3*d-N^2*d^2-4*N^2+6*N*d-6*d^2+6),
    d*(N-d)*(N^3*d-2*N^2*d^2-3*N^2+6*N*d+3*d^2-3),
    N*(d*(N-d)*(N^2-5*N*d+5*d^2+1))]

set_option maxHeartbeats 0 in
theorem fourthCoefficient_linear_system (N d : ℂ)
    (hN : N ≠ 0) (h1 : N^2-1 ≠ 0) (h4 : N^2-4 ≠ 0) (h9 : N^2-9 ≠ 0)
    (j : Fin 5) :
    fourthGramRow N (fourthCoefficient N d) j = d ^ (![4,3,2,2,1] j : ℕ) := by
  let D := (N^2-1)*(N^2-4)*(N^2-9)
  let T := N^2*D
  have hD : D ≠ 0 := mul_ne_zero (mul_ne_zero h1 h4) h9
  have hT : T ≠ 0 := mul_ne_zero (pow_ne_zero 2 hN) hD
  have hND : N*D ≠ 0 := mul_ne_zero hN hD
  have cancel (x : ℂ) : (x/(N*D))*T = N*x := by
    calc
      _ = (x/(N*D))*((N*D)*N) := by dsimp [T]; congr 1; ring
      _ = x*N := by rw [← mul_assoc, div_mul_cancel₀ x hND]
      _ = _ := mul_comm _ _
  have hc (i : Fin 5) : fourthCoefficient N d i * T =
      fourthCoefficientNumerator N d i := by
    fin_cases i <;> simp only [fourthCoefficient, fourthCoefficientNumerator,
      Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    all_goals first | exact div_mul_cancel₀ _ hT | exact cancel _
  have hr (b : Fin 5 → ℂ) (i : Fin 5) :
      fourthGramRow N b i * T = fourthGramRow N (fun l => b l*T) i := by
    fin_cases i <;> simp only [fourthGramRow,
      Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] <;> ring
  apply mul_right_cancel₀ hT
  rw [hr]
  simp_rw [hc]
  fin_cases j <;> simp only [fourthGramRow, fourthCoefficientNumerator,
    Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  all_goals dsimp [T, D]; ring

/-- An explicit solution of the fourth-order Gram system equals the actual
inverse-Gram coefficient. -/
theorem projectionMomentCoefficients_fourth
    {E : Type*} [Fintype E] [DecidableEq E] (e : Fin 4 ↪ E) (d : ℕ) :
    projectionMomentCoefficients E 4 d =
      fun σ => fourthCoefficient (Fintype.card E : ℂ) (d : ℂ) (fourthClass σ) := by
  have hcard : 4 ≤ Fintype.card E := by
    simpa using Fintype.card_le_of_injective e e.injective
  have hreal : (4 : ℝ) ≤ Fintype.card E := by exact_mod_cast hcard
  have hN : (Fintype.card E : ℂ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card E ≠ 0)
  have h1 : (Fintype.card E : ℂ)^2-1 ≠ 0 := by
    have h : (Fintype.card E : ℝ)^2-1 ≠ 0 := by nlinarith
    exact_mod_cast h
  have h4 : (Fintype.card E : ℂ)^2-4 ≠ 0 := by
    have h : (Fintype.card E : ℝ)^2-4 ≠ 0 := by nlinarith
    exact_mod_cast h
  have h9 : (Fintype.card E : ℂ)^2-9 ≠ 0 := by
    have h : (Fintype.card E : ℝ)^2-9 ≠ 0 := by nlinarith
    exact_mod_cast h
  have hsystem : permutationGram E 4 *ᵥ
      (fun σ => fourthCoefficient (Fintype.card E : ℂ) (d : ℂ) (fourthClass σ)) =
      (fun σ => (d : ℂ) ^ cycleCount σ.symm) := by
    funext σ
    change (∑ τ, permutationGram E 4 σ τ *
      fourthCoefficient (Fintype.card E : ℂ) (d : ℂ) (fourthClass τ)) = _
    simp_rw [permutationGram_cycles]
    rw [fourthGramRow_eq_sum, fourthCoefficient_linear_system _ _ hN h1 h4 h9]
    simp only [cycleCount_fourth, fourthCycleNumber, fourthClass_symm]
    generalize fourthClass σ = j
    fin_cases j <;> rfl
  unfold projectionMomentCoefficients
  rw [← hsystem, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (permutationGram_isUnit e)), Matrix.one_mulVec]

#print axioms projectionMomentCoefficients_fourth

end ProjectionChannels.TensorHaar
