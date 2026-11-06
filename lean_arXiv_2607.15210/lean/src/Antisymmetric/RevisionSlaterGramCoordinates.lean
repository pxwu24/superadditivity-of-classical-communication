import Antisymmetric.RevisionSlaterReduction

/-! Identification of the one-leg Gram map with successive Slater-coordinate
 partial trace and adjoint. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

def oneLegGram (h : Fin r) (Y : Matrix (TensorIndex k r) (TensorIndex k r) ℂ) :
    Matrix (TensorIndex k r) (TensorIndex k r) ℂ :=
  ∑ a : Fin k, ∑ b : Fin k,
    (antisymMatrix * oneLegMatrix (matrixUnit b a) h * antisymMatrix) * Y *
      (antisymMatrix * oneLegMatrix (matrixUnit a b) h * antisymMatrix)

lemma submatrix_fintypeSum {ι A B C D : Type*} [Fintype ι]
    (M : ι → Matrix A B ℂ) (e : C → A) (f : D → B) :
    (∑ i, M i).submatrix e f = ∑ i, (M i).submatrix e f := by
  ext x y
  simp [Matrix.submatrix_apply, Matrix.sum_apply]

lemma oneLegGram_product
    (Y : Matrix (TensorIndex k (r + 1)) (TensorIndex k (r + 1)) ℂ)
    (hPY : antisymMatrix * Y = Y) (hYP : Y * antisymMatrix = Y) :
    (oneLegGram 0 Y).submatrix firstTensorEquiv firstTensorEquiv =
      antisymMatrixProduct * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
        (traceA (Y.submatrix firstTensorEquiv firstTensorEquiv)) * antisymMatrixProduct := by
  let e := firstTensorEquiv (k := k) (r := r)
  have hmul (M N : Matrix (TensorIndex k (r + 1)) (TensorIndex k (r + 1)) ℂ) :
      (M * N).submatrix e e = M.submatrix e e * N.submatrix e e :=
    (Matrix.submatrix_mul_equiv M N e e e).symm
  have hPY' : antisymMatrixProduct * Y.submatrix e e = Y.submatrix e e := by
    have h := congrArg (fun M => M.submatrix e e) hPY
    simpa only [hmul] using h
  have hYP' : Y.submatrix e e * antisymMatrixProduct = Y.submatrix e e := by
    have h := congrArg (fun M => M.submatrix e e) hYP
    simpa only [hmul] using h
  change (oneLegGram 0 Y).submatrix e e = _
  simp only [oneLegGram, submatrix_fintypeSum, hmul]
  change (∑ a : Fin k, ∑ b : Fin k,
    (antisymMatrixProduct * (oneLegMatrix (matrixUnit b a) 0).submatrix firstTensorEquiv firstTensorEquiv * antisymMatrixProduct) *
      Y.submatrix e e *
      (antisymMatrixProduct * (oneLegMatrix (matrixUnit a b) 0).submatrix firstTensorEquiv firstTensorEquiv * antisymMatrixProduct)) = _
  simp only [oneLegMatrix_zero_product]
  rw [Finset.sum_comm]
  exact compressed_matrixUnit_twirl _ _ hPY' hYP'

lemma slater_sandwich_reindex
    (F : Matrix (TensorIndex k (r + 1)) (TensorIndex k (r + 1)) ℂ) :
    slaterIsometry.conjTranspose * F * slaterIsometry =
      slaterProduct.conjTranspose * F.submatrix firstTensorEquiv firstTensorEquiv * slaterProduct := by
  rw [slaterProduct_conjTranspose, slaterProduct, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

lemma slater_embed_product
    (Z : Matrix (SubsetIndex k (r + 1)) (SubsetIndex k (r + 1)) ℂ) :
    (slaterIsometry * Z * slaterIsometry.conjTranspose).submatrix firstTensorEquiv firstTensorEquiv =
      slaterProduct * Z * slaterProduct.conjTranspose := by
  rw [slaterProduct_conjTranspose, slaterProduct]
  conv_rhs => enter [1,2]; rw [← Matrix.submatrix_id_id Z]
  have h1 := Matrix.submatrix_mul_equiv (slaterIsometry (k := k) (r := r + 1)) Z
    firstTensorEquiv (Equiv.refl (SubsetIndex k (r + 1))) id
  have h2 := Matrix.submatrix_mul_equiv (slaterIsometry * Z)
    (slaterIsometry (k := k) (r := r + 1)).conjTranspose
    firstTensorEquiv (Equiv.refl (SubsetIndex k (r + 1))) firstTensorEquiv
  simpa only [Equiv.coe_refl, h1] using h2.symm

lemma slaterProduct_projection_left :
    (antisymMatrixProduct (k := k) (r := r)) * slaterProduct = slaterProduct := by
  rw [← slaterProduct_range_projection, Matrix.mul_assoc, slaterProduct_isometry, Matrix.mul_one]

lemma slaterProduct_projection_right :
    (slaterProduct (k := k) (r := r)).conjTranspose * antisymMatrixProduct = slaterProduct.conjTranspose := by
  rw [← slaterProduct_range_projection, ← Matrix.mul_assoc, slaterProduct_isometry, Matrix.one_mul]

lemma slaterEmbed_projection_left
    (Z : Matrix (SubsetIndex k r) (SubsetIndex k r) ℂ) :
    antisymMatrix * (slaterIsometry * Z * slaterIsometry.conjTranspose) =
      slaterIsometry * Z * slaterIsometry.conjTranspose := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, antisymMatrix_mul_slaterIsometry]

lemma slaterEmbed_projection_right
    (Z : Matrix (SubsetIndex k r) (SubsetIndex k r) ℂ) :
    (slaterIsometry * Z * slaterIsometry.conjTranspose) * antisymMatrix =
      slaterIsometry * Z * slaterIsometry.conjTranspose := by
  have h : slaterIsometry.conjTranspose * (antisymMatrix (k := k) (r := r)) = slaterIsometry.conjTranspose := by
    have hh := congrArg Matrix.conjTranspose (antisymMatrix_mul_slaterIsometry (k := k) (r := r))
    simpa only [Matrix.conjTranspose_mul, antisymMatrix_isHermitian.eq] using hh
  rw [Matrix.mul_assoc, h]

/-- The one-leg Gram map in normalized Slater coordinates is exactly `R*R`. -/
theorem slater_oneLegGram_coordinates
    (Z : Matrix (SubsetIndex k (r + 1)) (SubsetIndex k (r + 1)) ℂ) :
    slaterIsometry.conjTranspose *
      oneLegGram 0 (slaterIsometry * Z * slaterIsometry.conjTranspose) * slaterIsometry =
      slaterUp k r (slaterDown k r Z) := by
  rw [slater_sandwich_reindex, oneLegGram_product _ (slaterEmbed_projection_left Z)
    (slaterEmbed_projection_right Z), slater_embed_product]
  simp only [Matrix.mul_assoc, slaterProduct_projection_left]
  rw [← Matrix.mul_assoc slaterProduct.conjTranspose antisymMatrixProduct,
    slaterProduct_projection_right, ← Matrix.mul_assoc]
  let Y := slaterProduct * Z * (slaterProduct (k := k) (r := r)).conjTranspose
  have hPY : antisymMatrixProduct * Y = Y := by
    dsimp [Y]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, slaterProduct_projection_left]
  have hYP : Y * antisymMatrixProduct = Y := by
    dsimp [Y]
    rw [Matrix.mul_assoc, slaterProduct_projection_right]
  have hs := antisym_partialTrace_support Y hPY hYP
  have hrecon : slaterIsometry *
      (slaterIsometry.conjTranspose * traceA Y * slaterIsometry) * slaterIsometry.conjTranspose = traceA Y := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, slaterIsometry_range_projection]
    rw [Matrix.mul_assoc, slaterIsometry_range_projection]
    exact hs
  unfold slaterUp slaterDown upCoordinates downCoordinates
  dsimp [Y] at hrecon
  rw [hrecon]
  simp only [Matrix.mul_assoc]

end AntisymmetricVerification
