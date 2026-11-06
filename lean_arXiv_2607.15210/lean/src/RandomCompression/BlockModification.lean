import RandomCompression.CompressionSpectral
import Preliminaries.CompletePositivity

open scoped BigOperators
open Matrix PreliminariesMatrix

namespace ProjectionChannels
noncomputable section

variable {n k : Type} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-- The Hermiticity-preserving block-modification map as a complex linear map. -/
def diagonalTraceLinearMap (a : k → ℝ) : Matrix k k ℂ →ₗ[ℂ] Matrix k k ℂ where
  toFun X := (∑ i, (a i : ℂ) * X i i) • (1 : Matrix k k ℂ)
  map_add' X Y := by
    simp [mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' z X := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    have h : (∑ x, (a x : ℂ) * (z * X x x)) = z * ∑ x, (a x : ℂ) * X x x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h]
    simp only [RingHom.id_apply]
    ring

lemma diagonalTraceLinearMap_eq (a : k → ℝ) (X : Matrix k k ℂ) :
    diagonalTraceLinearMap a X =
      Matrix.trace (Matrix.diagonal (fun i => (a i : ℂ)) * X) • (1 : Matrix k k ℂ) := by
  simp [diagonalTraceLinearMap, Matrix.trace, Matrix.diagonal_mul]

/-- Exact block-modification identity used before the random-matrix input. -/
theorem amplified_diagonalTrace (a : k → ℝ)
    (P : Matrix (n × k) (n × k) ℂ) :
    ProjectionChannelsCP.amplify (diagonalTraceLinearMap a) P =
      Matrix.kronecker (blockCompression (diagonalBlock P) a) (1 : Matrix k k ℂ) := by
  ext ⟨u, i⟩ ⟨v, j⟩
  simp [ProjectionChannelsCP.amplify, diagonalTraceLinearMap,
    Matrix.kronecker_apply, blockCompression, diagonalBlock,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]

/-- Matrix-unit insertion of the blocks, making the modification a fixed
noncommutative polynomial in P and the tensor matrix units. -/
theorem matrixUnit_block_insertion (P : Matrix (n × k) (n × k) ℂ) (i j : k) :
    Matrix.kronecker (1 : Matrix n n ℂ) (matrixUnit j i) * P *
      Matrix.kronecker (1 : Matrix n n ℂ) (matrixUnit i j) =
      Matrix.kronecker (diagonalBlock P i) (matrixUnit j j) := by
  ext ⟨u, a⟩ ⟨v, b⟩
  simp [Matrix.mul_apply, Matrix.kronecker_apply, matrixUnit, diagonalBlock,
    Matrix.submatrix_apply, Fintype.sum_prod_type, Matrix.one_apply,
    ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  split_ifs <;> rfl

/-- The exact polynomial expression used by the strong-convergence theorem. -/
theorem blockModification_polynomial (P : Matrix (n × k) (n × k) ℂ) (a : k → ℝ) :
    Matrix.kronecker (blockCompression (diagonalBlock P) a) (1 : Matrix k k ℂ) =
      ∑ i, ∑ j, (a i : ℂ) •
        (Matrix.kronecker (1 : Matrix n n ℂ) (matrixUnit j i) * P *
          Matrix.kronecker (1 : Matrix n n ℂ) (matrixUnit i j)) := by
  simp_rw [matrixUnit_block_insertion]
  ext ⟨u, l⟩ ⟨v, m⟩
  simp [Matrix.kronecker_apply, blockCompression, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, matrixUnit, Matrix.one_apply,
    Finset.sum_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.sum_ite_eq', eq_comm]

end
end ProjectionChannels

