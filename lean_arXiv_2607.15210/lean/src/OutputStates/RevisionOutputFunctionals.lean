import OutputStates.RevisionOutputGeometry

/-!
# Real dual functionals on Hermitian matrices

Every real continuous functional on matrices is represented by a Hermitian
trace pairing when restricted to Hermitian matrices. This permits using the
proved normed-space separation results directly, without assuming a matrix
separation theorem.
-/

open Matrix PreliminariesMatrix ProjectionChannels
open scoped BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

lemma complex_smul_matrixUnit_decompose (z : ℂ) (i j : A) :
    z • matrixUnit i j = z.re • matrixUnit i j + z.im • (Complex.I • matrixUnit i j) := by
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.real_smul]
  rw [← mul_assoc, ← add_mul]
  congr 1
  simpa [mul_comm] using (Complex.re_add_im z).symm

lemma real_matrixUnit_expansion (X : Matrix A A ℂ) :
    (∑ i : A, ∑ j : A,
      ((X i j).re • matrixUnit i j + (X i j).im • (Complex.I • matrixUnit i j))) = X := by
  simpa only [← complex_smul_matrixUnit_decompose] using matrixUnit_expansion X

/-- The coefficient matrix of a real functional in the real/imaginary
matrix-unit basis. -/
def functionalMatrix (f : Matrix A A ℂ →L[ℝ] ℝ) : Matrix A A ℂ :=
  fun i j => ⟨f (matrixUnit j i), -f (Complex.I • matrixUnit j i)⟩

lemma functionalMatrix_trace (f : Matrix A A ℂ →L[ℝ] ℝ) (X : Matrix A A ℂ) :
    (Matrix.trace (functionalMatrix f * X)).re = f X := by
  have heq := congrArg f (real_matrixUnit_expansion X)
  simp only [map_sum, map_add, map_smul, smul_eq_mul] at heq
  rw [← heq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, functionalMatrix,
    Complex.re_sum, Complex.mul_re, neg_mul, sub_neg_eq_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma re_trace_conjTranspose_mul {M X : Matrix A A ℂ} (hX : X.IsHermitian) :
    (Matrix.trace (M.conjTranspose * X)).re = (Matrix.trace (M * X)).re := by
  have heq : Matrix.trace (M.conjTranspose * X) = star (Matrix.trace (M * X)) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.eq, Matrix.trace_mul_comm]
  rw [heq]
  rfl

/-- Hermitian representative of the same real functional on Hermitian matrices. -/
def hermitianFunctionalMatrix (f : Matrix A A ℂ →L[ℝ] ℝ) : Matrix A A ℂ :=
  (1 / 2 : ℂ) • (functionalMatrix f + (functionalMatrix f).conjTranspose)

lemma hermitianFunctionalMatrix_isHermitian (f : Matrix A A ℂ →L[ℝ] ℝ) :
    (hermitianFunctionalMatrix f).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [hermitianFunctionalMatrix, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]

/-- Every real functional has a trace-Hermitian representation on the
entire Hermitian subspace, not just on density matrices. -/
theorem hermitian_trace_representation (f : Matrix A A ℂ →L[ℝ] ℝ)
    {X : Matrix A A ℂ} (hX : X.IsHermitian) :
    (Matrix.trace (hermitianFunctionalMatrix f * X)).re = f X := by
  simp only [hermitianFunctionalMatrix, Matrix.smul_mul, Matrix.add_mul,
    Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, Complex.mul_re,
    Complex.add_re, Complex.add_im]
  norm_num
  rw [re_trace_conjTranspose_mul hX, functionalMatrix_trace]
  ring

end
end RevisionOutput
