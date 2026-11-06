import Antisymmetric.RevisionAntisymmetricLegMatrix
import Antisymmetric.RevisionAntisymmetricOrthonormal
import Preliminaries.CompletePositivity
import Antisymmetric.RevisionSlaterReduction
import OutputStates.RevisionOutputGeometry
import Mathlib.LinearAlgebra.Trace

/-! Complete positivity of the actual antisymmetric compression, via explicit
Kraus operators for the identity ancilla and compression to Slater coordinates. -/
open Matrix ProjectionChannelsCP
open scoped BigOperators ComplexOrder
noncomputable section
namespace AntisymmetricVerification

variable {A E D : Type} [Fintype A] [Fintype E] [Fintype D]
  [DecidableEq A] [DecidableEq E] [DecidableEq D]

def ancillaEmbedding (e : E) : Matrix (A × E) A ℂ :=
  fun x a => if x.1 = a ∧ x.2 = e then 1 else 0

lemma identity_ancilla_kraus (X : Matrix A A ℂ) :
    Matrix.kronecker X (1 : Matrix E E ℂ) =
      ∑ e, ancillaEmbedding e * X * (ancillaEmbedding e).conjTranspose := by
  ext ⟨a,e⟩ ⟨b,f⟩
  simp [ancillaEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_and, mul_ite, ite_mul, Finset.sum_ite_irrel, eq_comm, apply_ite]
  by_cases h : e = f <;> simp [h, eq_comm]

def compressedTensorMap (C : Matrix D (A × E) ℂ) :
    Matrix A A ℂ →ₗ[ℂ] Matrix D D ℂ where
  toFun X := C * Matrix.kronecker X (1 : Matrix E E ℂ) * C.conjTranspose
  map_add' X Y := by
    simp [Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp [Matrix.smul_kronecker, Matrix.mul_smul, Matrix.smul_mul]

lemma compressedTensorMap_completelyPositive (C : Matrix D (A × E) ℂ) :
    CompletelyPositive (compressedTensorMap C) := by
  apply completelyPositive_of_kraus (compressedTensorMap C)
    (fun e : E => C * ancillaEmbedding e)
  intro X
  change C * Matrix.kronecker X (1 : Matrix E E ℂ) * C.conjTranspose = _
  rw [identity_ancilla_kraus, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

variable {k r : ℕ}

/-- The normalized antisymmetric channel in a fixed orthonormal Slater basis.
The parameter `r` here denotes one less than the particle number. -/
def antisymmetricChannel :
    Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ]
      Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ :=
  compressedTensorMap ((Real.sqrt ((k:ℝ)/(Nat.choose k (r+1):ℝ)) : ℂ) •
    (slaterProduct (k := k) (r := r)).conjTranspose)

theorem antisymmetricChannel_completelyPositive :
    CompletelyPositive (antisymmetricChannel (k := k) (r := r)) :=
  compressedTensorMap_completelyPositive _

lemma antisymmetricChannel_product_formula (X : Matrix (Fin k) (Fin k) ℂ) :
    antisymmetricChannel (r := r) X = ((k:ℂ)/(Nat.choose k (r+1):ℂ)) •
      ((slaterProduct (k := k) (r := r)).conjTranspose *
        Matrix.kronecker X (1 : Matrix (TensorIndex k r) (TensorIndex k r) ℂ) *
        slaterProduct) := by
  have hnon : 0 ≤ (k:ℝ)/(Nat.choose k (r+1):ℝ) := by positivity
  have hs : (Real.sqrt ((k:ℝ)/(Nat.choose k (r+1):ℝ)) : ℂ) *
      (Real.sqrt ((k:ℝ)/(Nat.choose k (r+1):ℝ)) : ℂ) =
      (k:ℂ)/(Nat.choose k (r+1):ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnon]
    push_cast
    rfl
  simp only [antisymmetricChannel, compressedTensorMap, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]

lemma antisymmetricChannel_tensor_formula (X : Matrix (Fin k) (Fin k) ℂ) :
    antisymmetricChannel (r := r) X = ((k:ℂ)/(Nat.choose k (r+1):ℂ)) •
      ((slaterIsometry (k := k) (r := r+1)).conjTranspose *
        oneLegMatrix X 0 * slaterIsometry) := by
  rw [antisymmetricChannel_product_formula, ← oneLegMatrix_zero_product X]
  simp only [slaterProduct, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

def slaterCoordinateEquiv : (SubsetIndex k r → ℂ) ≃ₗ[ℂ] alternatingSpace k r where
  toFun v := ⟨slaterIsometry.mulVec v, by
    have h : antisymmetrize (slaterIsometry.mulVec v) = slaterIsometry.mulVec v := by
      rw [← antisymMatrix_mulVec, Matrix.mulVec_mulVec, antisymMatrix_mul_slaterIsometry]
    rw [← h]
    exact antisymmetrize_alternating _⟩
  invFun v := slaterIsometry.conjTranspose.mulVec v.val
  left_inv v := by
    change slaterIsometry.conjTranspose.mulVec (slaterIsometry.mulVec v) = v
    rw [Matrix.mulVec_mulVec, slaterIsometry_isometry, Matrix.one_mulVec]
  right_inv v := by
    apply Subtype.ext
    change slaterIsometry.mulVec (slaterIsometry.conjTranspose.mulVec v.val) = v.val
    rw [Matrix.mulVec_mulVec, slaterIsometry_range_projection, antisymMatrix_mulVec,
      antisymmetrize_of_alternating v.property]
  map_add' u v := by
    apply Subtype.ext
    change slaterIsometry.mulVec (u+v) = slaterIsometry.mulVec u + slaterIsometry.mulVec v
    exact Matrix.mulVec_add _ _ _
  map_smul' c v := by
    apply Subtype.ext
    change slaterIsometry.mulVec (c • v) = c • slaterIsometry.mulVec v
    exact Matrix.mulVec_smul _ _ _

lemma slater_conjTranspose_mul_antisymMatrix :
    (slaterIsometry (k := k) (r := r)).conjTranspose * antisymMatrix =
      slaterIsometry.conjTranspose := by
  have h := congrArg Matrix.conjTranspose (antisymMatrix_mul_slaterIsometry (k:=k) (r:=r))
  simpa only [Matrix.conjTranspose_mul, antisymMatrix_isHermitian.eq] using h

lemma antisymmetricChannel_restriction_conjugate (X : Matrix (Fin k) (Fin k) ℂ) :
    (slaterCoordinateEquiv (k:=k) (r:=r+1)).symm.conj (postprocessRestriction X 0) =
      Matrix.toLin' (antisymmetricChannel (r:=r) X) := by
  apply LinearMap.ext
  intro v
  change slaterIsometry.conjTranspose.mulVec
      (postprocess X 0 (slaterIsometry.mulVec v)) =
    (antisymmetricChannel X).mulVec v
  rw [antisymmetricChannel_tensor_formula]
  simp only [postprocess, Matrix.smul_mulVec_assoc, Matrix.mulVec_smul]
  simp_rw [← antisymMatrix_mulVec, ← oneLegMatrix_mulVec]
  simp only [Matrix.mulVec_mulVec, antisymMatrix_mul_slaterIsometry,
    ← Matrix.mul_assoc, slater_conjTranspose_mul_antisymMatrix]

lemma sum_shuffle (hrk : r+1 ≤ k) (q : Fin k → ℝ) :
    ∑ I : SubsetIndex k (r+1), AppendixB.shuffle k (r+1) q I.val = ∑ a, q a := by
  classical
  rw [← Finset.sum_subtype (AppendixB.subsets k (r+1))
    (fun I => by simp [AppendixB.subsets, Finset.mem_powersetCard])]
  simp only [AppendixB.shuffle, Nat.add_sub_cancel, ← Finset.sum_div]
  rw [AppendixB.sum_over_subsets]
  have hn : (Nat.choose (k-1) r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : r ≤ k-1)).ne'
  field_simp

lemma restriction_trace_hermitian (hrk : r+1 ≤ k)
    (X : Matrix (Fin k) (Fin k) ℂ) (hX : X.IsHermitian) :
    LinearMap.trace ℂ (alternatingSpace k (r+1)) (postprocessRestriction X 0) =
      Matrix.trace X := by
  classical
  letI : NeZero k := ⟨by omega⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ (eigenSlaterBasis hX),
    postprocess_matrix_diagonal (by omega) hrk hX 0, Matrix.trace_diagonal,
    ← Complex.ofReal_sum, sum_shuffle hrk,
    RevisionOutput.trace_eq_sum_eigenvalues X hX]
  simp only [Complex.ofReal_sum]

lemma antisymmetricChannel_trace_hermitian (hrk : r+1 ≤ k)
    (X : Matrix (Fin k) (Fin k) ℂ) (hX : X.IsHermitian) :
    Matrix.trace (antisymmetricChannel (r:=r) X) = Matrix.trace X := by
  classical
  have h := LinearMap.trace_conj' (postprocessRestriction X (0:Fin (r+1)))
    (slaterCoordinateEquiv (k:=k) (r:=r+1)).symm
  rw [antisymmetricChannel_restriction_conjugate,
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (SubsetIndex k (r+1)))] at h
  have heq : LinearMap.toMatrix (Pi.basisFun ℂ (SubsetIndex k (r+1)))
      (Pi.basisFun ℂ (SubsetIndex k (r+1)))
      (Matrix.toLin' (antisymmetricChannel (r:=r) X)) = antisymmetricChannel X :=
    LinearMap.toMatrix'_toLin' _
  rw [heq, restriction_trace_hermitian hrk X hX] at h
  exact h

/-- Trace preservation is established on every complex matrix, using the
Hermitian decomposition after the spectral trace computation. -/
theorem antisymmetricChannel_tracePreserving (hrk : r+1 ≤ k) :
    TracePreserving (antisymmetricChannel (k:=k) (r:=r)) := by
  intro X
  have hr := antisymmetricChannel_trace_hermitian hrk (realPart X : Matrix (Fin k) (Fin k) ℂ)
    selfAdjoint.isSelfAdjoint
  have hi := antisymmetricChannel_trace_hermitian hrk (imaginaryPart X : Matrix (Fin k) (Fin k) ℂ)
    selfAdjoint.isSelfAdjoint
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart X]
  rw [map_add, map_smul, Matrix.trace_add, Matrix.trace_smul, hr, hi]
  rw [← Matrix.trace_smul, ← Matrix.trace_add, realPart_add_I_smul_imaginaryPart]

/-- The antisymmetric postprocessing map really is a finite-dimensional
quantum channel, not just an eigenvalue prescription. -/
theorem antisymmetricChannel_quantumChannel (hrk : r+1 ≤ k) :
    CompletelyPositive (antisymmetricChannel (k:=k) (r:=r)) ∧
    TracePreserving (antisymmetricChannel (k:=k) (r:=r)) :=
  ⟨antisymmetricChannel_completelyPositive, antisymmetricChannel_tracePreserving hrk⟩

end AntisymmetricVerification
