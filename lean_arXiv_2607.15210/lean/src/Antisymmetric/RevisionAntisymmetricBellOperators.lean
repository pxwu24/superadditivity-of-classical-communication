import Antisymmetric.RevisionAntisymmetricOrthonormal
import Antisymmetric.RevisionAntisymmetricRecursion
import Preliminaries.PreliminariesMatrix

/-! Exact matrix-unit contractions underlying the Bell-output/partial-trace
 Gram identity. All matrices and partial traces are explicitly represented. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Depolarizing one tensor factor is the sum of matrix-unit Kraus terms. -/
theorem matrixUnit_twirl (Y : Matrix (A × B) (A × B) ℂ) :
    (∑ a : A, ∑ b : A,
      Matrix.kronecker (matrixUnit a b) (1 : Matrix B B ℂ) * Y *
        Matrix.kronecker (matrixUnit b a) (1 : Matrix B B ℂ)) =
      Matrix.kronecker (1 : Matrix A A ℂ) (traceA Y) := by
  classical
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases h : i = j
  · subst j
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, matrixUnit, Matrix.one_apply, ite_and, traceA,
      Finset.sum_mul, Finset.mul_sum]
  · simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, matrixUnit, Matrix.one_apply, ite_and, traceA,
      Finset.sum_mul, Finset.mul_sum, h]

/-- Compressing the matrix-unit twirl gives exactly the positive Gram map
 `Y ↦ Π(I ⊗ Tr_first Y)Π`. -/
theorem compressed_matrixUnit_twirl (P Y : Matrix (A × B) (A × B) ℂ)
    (hPY : P * Y = Y) (hYP : Y * P = Y) :
    (∑ a : A, ∑ b : A,
      (P * Matrix.kronecker (matrixUnit a b) (1 : Matrix B B ℂ) * P) * Y *
        (P * Matrix.kronecker (matrixUnit b a) (1 : Matrix B B ℂ) * P)) =
      P * Matrix.kronecker (1 : Matrix A A ℂ) (traceA Y) * P := by
  calc
    _ = ∑ a : A, ∑ b : A, P *
        (Matrix.kronecker (matrixUnit a b) (1 : Matrix B B ℂ) * Y *
          Matrix.kronecker (matrixUnit b a) (1 : Matrix B B ℂ)) * P := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      calc
        _ = P * Matrix.kronecker (matrixUnit a b) (1 : Matrix B B ℂ) *
            (P * Y * P) * Matrix.kronecker (matrixUnit b a) (1 : Matrix B B ℂ) * P := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hPY, hYP]; simp only [Matrix.mul_assoc]
    _ = P * (∑ a : A, ∑ b : A,
        Matrix.kronecker (matrixUnit a b) (1 : Matrix B B ℂ) * Y *
          Matrix.kronecker (matrixUnit b a) (1 : Matrix B B ℂ)) * P := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by rw [matrixUnit_twirl]

/-- The Hilbert--Schmidt adjoint of partial trace is tensoring with identity. -/
theorem partialTrace_hilbertSchmidt_adjoint (Y : Matrix (A × B) (A × B) ℂ)
    (Z : Matrix B B ℂ) :
    Matrix.trace ((Matrix.kronecker (1 : Matrix A A ℂ) Z).conjTranspose * Y) =
      Matrix.trace (Z.conjTranspose * traceA Y) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, traceA, Fintype.sum_prod_type,
    star_mul, apply_ite, star_one, star_zero, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul]
  conv_lhs =>
    enter [2, a, 2, i]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

/-- The paper's `ell² R_ell* R_ell` identity, once the compressed sum of one-body
 matrix units is written as `ell` times any one-leg compression. -/
theorem scaled_compressed_twirl (P Y : Matrix (A × B) (A × B) ℂ)
    (hPY : P * Y = Y) (hYP : Y * P = Y) (ell : ℂ) :
    (∑ a : A, ∑ b : A,
      (ell • (P * Matrix.kronecker (matrixUnit a b) (1 : Matrix B B ℂ) * P)) * Y *
        (ell • (P * Matrix.kronecker (matrixUnit b a) (1 : Matrix B B ℂ) * P))) =
      ell ^ 2 • (P * Matrix.kronecker (1 : Matrix A A ℂ) (traceA Y) * P) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [← Finset.smul_sum]
  rw [compressed_matrixUnit_twirl P Y hPY hYP]
  congr 1
  ring

end AntisymmetricVerification
