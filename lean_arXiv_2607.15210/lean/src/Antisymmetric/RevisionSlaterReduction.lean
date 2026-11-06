import Antisymmetric.RevisionAntisymmetricCoordinates

/-! Normalized Slater-coordinate partial traces and their adjoints. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

def rowSlice (U : Matrix (A × B) C ℂ) (a : A) : Matrix B C ℂ := fun x I => U (a,x) I

def reductionKraus (U : Matrix (A × B) C ℂ) (V : Matrix B D ℂ) (a : A) : Matrix D C ℂ :=
  V.conjTranspose * rowSlice U a

def downCoordinates (U : Matrix (A × B) C ℂ) (V : Matrix B D ℂ)
    (Y : Matrix C C ℂ) : Matrix D D ℂ :=
  V.conjTranspose * traceA (U * Y * U.conjTranspose) * V

def upCoordinates [DecidableEq A] (U : Matrix (A × B) C ℂ) (V : Matrix B D ℂ)
    (Z : Matrix D D ℂ) : Matrix C C ℂ :=
  U.conjTranspose * Matrix.kronecker (1 : Matrix A A ℂ) (V * Z * V.conjTranspose) * U

lemma traceA_gram_rows (U : Matrix (A × B) C ℂ) (Y : Matrix C C ℂ) :
    traceA (U * Y * U.conjTranspose) = ∑ a : A, rowSlice U a * Y * (rowSlice U a).conjTranspose := by
  ext x y
  simp only [traceA, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, rowSlice]

/-- The coordinate partial trace is an actual Kraus map. -/
theorem downCoordinates_eq_kraus (U : Matrix (A × B) C ℂ) (V : Matrix B D ℂ)
    (Y : Matrix C C ℂ) :
    downCoordinates U V Y = ∑ a : A, reductionKraus U V a * Y * (reductionKraus U V a).conjTranspose := by
  rw [downCoordinates, traceA_gram_rows]
  simp only [Matrix.mul_sum, Matrix.sum_mul, reductionKraus, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma gram_kronecker_rows [DecidableEq A] (U : Matrix (A × B) C ℂ) (W : Matrix B B ℂ) :
    U.conjTranspose * Matrix.kronecker (1 : Matrix A A ℂ) W * U =
      ∑ a : A, (rowSlice U a).conjTranspose * W * rowSlice U a := by
  ext I J
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.sum_apply, rowSlice, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_mul]
  conv_lhs => enter [2, a, 2, x]; rw [Finset.sum_comm]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ,
    if_true, sum_const_zero, one_mul]

/-- The coordinate Hilbert--Schmidt adjoint is the adjoint Kraus map. -/
theorem upCoordinates_eq_kraus [DecidableEq A] (U : Matrix (A × B) C ℂ) (V : Matrix B D ℂ)
    (Z : Matrix D D ℂ) :
    upCoordinates U V Z = ∑ a : A, (reductionKraus U V a).conjTranspose * Z * reductionKraus U V a := by
  rw [upCoordinates, gram_kronecker_rows]
  simp only [reductionKraus, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

variable {k r : ℕ}
/-- The `(r+1)`-particle Slater isometry with its first tensor factor separated. -/
def slaterProduct : Matrix (Fin k × TensorIndex k r) (SubsetIndex k (r + 1)) ℂ :=
  (slaterIsometry (k := k) (r := r + 1)).submatrix firstTensorEquiv id

lemma slaterProduct_conjTranspose : (slaterProduct (k := k) (r := r)).conjTranspose =
    (slaterIsometry (k := k) (r := r + 1)).conjTranspose.submatrix id firstTensorEquiv := by
  rw [slaterProduct, Matrix.conjTranspose_submatrix]

lemma slaterProduct_isometry :
    (slaterProduct (k := k) (r := r)).conjTranspose * (slaterProduct (k := k) (r := r)) = 1 := by
  rw [slaterProduct_conjTranspose, slaterProduct, Matrix.submatrix_mul_equiv,
    slaterIsometry_isometry]
  rfl

lemma slaterProduct_range_projection :
    (slaterProduct (k := k) (r := r)) * slaterProduct.conjTranspose = antisymMatrixProduct := by
  rw [slaterProduct_conjTranspose, slaterProduct,
    show (slaterIsometry.submatrix firstTensorEquiv id) *
      slaterIsometry.conjTranspose.submatrix id firstTensorEquiv =
      (slaterIsometry * slaterIsometry.conjTranspose).submatrix firstTensorEquiv firstTensorEquiv
      from Matrix.submatrix_mul_equiv _ _ firstTensorEquiv (Equiv.refl _) firstTensorEquiv,
    slaterIsometry_range_projection]
  rfl

/-- Actual partial trace in normalized Slater bases. -/
def slaterDown (k r : ℕ) (Y : Matrix (SubsetIndex k (r + 1)) (SubsetIndex k (r + 1)) ℂ) :
    Matrix (SubsetIndex k r) (SubsetIndex k r) ℂ :=
  downCoordinates slaterProduct slaterIsometry Y

/-- Its actual Hilbert--Schmidt adjoint in those bases. -/
def slaterUp (k r : ℕ) (Z : Matrix (SubsetIndex k r) (SubsetIndex k r) ℂ) :
    Matrix (SubsetIndex k (r + 1)) (SubsetIndex k (r + 1)) ℂ :=
  upCoordinates slaterProduct slaterIsometry Z

/-- Embedding the coordinate composition `R R*` recovers the exact compressed
 full-tensor partial trace, with no additional spectral hypothesis. -/
theorem slaterDown_up_formula (Z : Matrix (SubsetIndex k r) (SubsetIndex k r) ℂ) :
    slaterDown k r (slaterUp k r Z) =
      slaterIsometry.conjTranspose * traceA
        (antisymMatrixProduct * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
          (slaterIsometry * Z * slaterIsometry.conjTranspose) * antisymMatrixProduct) * slaterIsometry := by
  unfold slaterDown slaterUp downCoordinates upCoordinates
  congr 2
  congr 1
  simp only [← Matrix.mul_assoc, slaterProduct_range_projection]
  simp only [Matrix.mul_assoc, slaterProduct_range_projection]

end AntisymmetricVerification
