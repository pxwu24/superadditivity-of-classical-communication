import StrongConvergence.StrongConvergenceFourthCoefficients
import StrongConvergence.StrongConvergenceSecondVarianceAsymptotics

/-!
# Normalization of the fourth-order Haar variance calculation

The finite complex inverse-Gram expressions are identified with the real
rational kernels whose asymptotics are proved in `SecondVarianceAsymptotics`.
-/

open Matrix
noncomputable section
namespace ProjectionChannels.TensorHaar

private def realFourthCoefficient (N d : ℝ) : Fin 5 → ℝ :=
  let D := (N^2-1)*(N^2-4)*(N^2-9)
  ![d*(N^4*d^3-6*N^3*d^2-8*N^2*d^3+19*N^2*d+24*N*d^2-30*N+6*d^3-6*d)/(N^2*D),
    d*(N-d)*(N^2*d^2-5*N*d-4*d^2+10)/(N*D),
    d*(N-d)*(N^3*d-N^2*d^2-4*N^2+6*N*d-6*d^2+6)/(N^2*D),
    d*(N-d)*(N^3*d-2*N^2*d^2-3*N^2+6*N*d+3*d^2-3)/(N^2*D),
    d*(N-d)*(N^2-5*N*d+5*d^2+1)/(N*D)]

/-- The five class coefficients after scaling the ambient dimension. -/
def fourthScaledCoefficient (N d : ℝ) : Fin 5 → ℝ :=
  let q := d/N
  let x := (1/N)^2
  ![SecondVariance.coeffId q x,
    SecondVariance.coeffTransposition q x / N,
    SecondVariance.coeffDoubleTransposition q x / N^2,
    SecondVariance.coeffThreeCycle q x / N^2,
    SecondVariance.coeffFourCycle q x / N^3]

private lemma inverse_square_factor_ne (N c : ℝ) (hN : N ≠ 0)
    (hc : N^2-c ≠ 0) : 1-c*(1/N)^2 ≠ 0 := by
  intro h
  apply hc
  field_simp [hN] at h
  linarith

private lemma realFourthCoefficient_normalized (N d : ℝ)
    (hN : N ≠ 0) (h₁ : N^2-1 ≠ 0) (h₄ : N^2-4 ≠ 0) (h₉ : N^2-9 ≠ 0)
    (j : Fin 5) :
    realFourthCoefficient N d j = fourthScaledCoefficient N d j := by
  have hx₁ : 1-(1/N)^2 ≠ 0 := by
    simpa using inverse_square_factor_ne N 1 hN h₁
  have hx₄ := inverse_square_factor_ne N 4 hN h₄
  have hx₉ := inverse_square_factor_ne N 9 hN h₉
  fin_cases j <;>
    simp only [realFourthCoefficient, fourthScaledCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero',
      Matrix.cons_val_succ']
  all_goals simp only [SecondVariance.coeffId, SecondVariance.coeffTransposition,
    SecondVariance.coeffDoubleTransposition, SecondVariance.coeffThreeCycle,
    SecondVariance.coeffFourCycle, SecondVariance.denominator]
  all_goals field_simp [hN, h₁, h₄, h₉, hx₁, hx₄, hx₉] <;> ring

/-- Complex Haar coefficients are the real normalized scalar kernels. -/
theorem fourthCoefficient_normalized (N d : ℝ)
    (hN : N ≠ 0) (h₁ : N^2-1 ≠ 0) (h₄ : N^2-4 ≠ 0) (h₉ : N^2-9 ≠ 0)
    (j : Fin 5) :
    fourthCoefficient (N:ℂ) (d:ℂ) j = (fourthScaledCoefficient N d j : ℂ) := by
  rw [← realFourthCoefficient_normalized N d hN h₁ h₄ h₉ j]
  fin_cases j <;>
    simp only [fourthCoefficient, realFourthCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero',
      Matrix.cons_val_succ']
  all_goals push_cast <;> rfl

/-- The two-trace class sum, divided by the input dimension squared, is the
same real expression used by the variance-limit calculation. -/
theorem fourthGramRow_normalized (n k d p₁ p₂ p₃ p₄ : ℝ)
    (hn : n ≠ 0) (hk : k ≠ 0)
    (h₁ : (k*n)^2-1 ≠ 0) (h₄ : (k*n)^2-4 ≠ 0) (h₉ : (k*n)^2-9 ≠ 0) :
    fourthGramRow (n:ℂ)
      (fun j => fourthCoefficient ((k*n : ℝ):ℂ) (d:ℂ) j *
        ![(p₁:ℂ)^4, (p₁:ℂ)^2*(p₂:ℂ), (p₂:ℂ)^2,
          (p₁:ℂ)*(p₃:ℂ), (p₄:ℂ)] j) 2 / (n:ℂ)^2 =
      (SecondVariance.squareMean k (d/(k*n)) ((1/(k*n))^2) p₁ p₂ p₃ p₄ : ℂ) := by
  have hkn : k*n ≠ 0 := mul_ne_zero hk hn
  simp only [fourthGramRow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero',
      Matrix.cons_val_succ']
  simp_rw [fourthCoefficient_normalized (k*n) d hkn h₁ h₄ h₉]
  simp only [fourthScaledCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero',
      Matrix.cons_val_succ', SecondVariance.squareMean]
  norm_cast
  field_simp [hn, hk]
  <;> ring

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.fourthCoefficient_normalized
#print axioms ProjectionChannels.TensorHaar.fourthGramRow_normalized
