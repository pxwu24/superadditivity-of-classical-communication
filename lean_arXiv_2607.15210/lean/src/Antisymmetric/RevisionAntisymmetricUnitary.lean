import Antisymmetric.RevisionAntisymmetricChannel
import Entropy.RevisionMatrixEntropy

/-! A fixed-coordinate unitary spectral decomposition of the actual
antisymmetric channel, bridging Proposition V.2 to matrix entropy. -/
noncomputable section
open Matrix Finset Equiv
open scoped BigOperators
namespace AntisymmetricVerification
set_option maxHeartbeats 600000
variable {k r : ℕ}

lemma tensorMatrix_conjTranspose (U : Matrix (Fin k) (Fin k) ℂ) :
    (tensorMatrix (r:=r) U).conjTranspose = tensorMatrix U.conjTranspose := by
  ext x y
  simp [tensorMatrix, Matrix.conjTranspose_apply]

lemma tensorMatrix_unitary_star_mul (U : Matrix.unitaryGroup (Fin k) ℂ) :
    (tensorMatrix (r:=r) (U : Matrix (Fin k) (Fin k) ℂ)).conjTranspose *
      tensorMatrix (U : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  rw [tensorMatrix_conjTranspose, ← tensorMatrix_mul,
    show (U:Matrix (Fin k) (Fin k) ℂ).conjTranspose*(U:Matrix (Fin k) (Fin k) ℂ)=1 from U.prop.1, tensorMatrix_one]

lemma antisymMatrix_mul_tensor_slater (U : Matrix (Fin k) (Fin k) ℂ) :
    (antisymMatrix (k:=k) (r:=r)) * (tensorMatrix (r:=r) U * slaterIsometry (k:=k) (r:=r)) =
      tensorMatrix (r:=r) U * slaterIsometry (k:=k) (r:=r) := by
  apply Matrix.ext_of_mulVec_single
  intro I
  simp only [← Matrix.mulVec_mulVec, antisymMatrix_mulVec]
  exact antisymmetrize_of_alternating (tensorMatrix_preserves_alternating U
    (slaterCoordinateEquiv (Pi.single I 1)).property)

/-- Change of one-particle orthonormal basis, restricted to the exterior power. -/
def exteriorUnitary (U : Matrix.unitaryGroup (Fin k) ℂ) :
    Matrix.unitaryGroup (SubsetIndex k r) ℂ := by
  let S : Matrix (TensorIndex k r) (SubsetIndex k r) ℂ := slaterIsometry
  let T : Matrix (TensorIndex k r) (TensorIndex k r) ℂ := tensorMatrix (U:Matrix (Fin k) (Fin k) ℂ)
  let V : Matrix (SubsetIndex k r) (SubsetIndex k r) ℂ := S.conjTranspose*T*S
  have hV : V.conjTranspose * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      _ = S.conjTranspose*T.conjTranspose*(S*S.conjTranspose)*(T*S) := by
        simp only [Matrix.mul_assoc]
      _ = S.conjTranspose*T.conjTranspose*(T*S) := by
        have heq : (S*S.conjTranspose)*(T*S)=T*S := by
          dsimp only [S,T]
          rw [slaterIsometry_range_projection,antisymMatrix_mul_tensor_slater]
        rw [Matrix.mul_assoc (S.conjTranspose*T.conjTranspose),heq]
      _ = S.conjTranspose*(T.conjTranspose*T)*S := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        have hT : T.conjTranspose*T=1 := tensorMatrix_unitary_star_mul U
        rw [hT,Matrix.mul_one]
        exact slaterIsometry_isometry
  exact ⟨V, ⟨hV, (Matrix.mul_eq_one_comm).mp hV⟩⟩

lemma slater_mul_exteriorUnitary (U : Matrix.unitaryGroup (Fin k) ℂ) :
    slaterIsometry * (exteriorUnitary (r:=r) U : Matrix (SubsetIndex k r) (SubsetIndex k r) ℂ) =
      tensorMatrix (U : Matrix (Fin k) (Fin k) ℂ) * slaterIsometry := by
  change slaterIsometry * (slaterIsometry.conjTranspose * tensorMatrix _ * slaterIsometry) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, slaterIsometry_range_projection,
    Matrix.mul_assoc, antisymMatrix_mul_tensor_slater]

lemma tensor_eigenSlater_column {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) (I : SubsetIndex k r) :
    (tensorMatrix (hX.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) *
      slaterIsometry).mulVec (Pi.single I 1) =
      ((Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹) • eigenSlater hX I := by
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  change (tensorMatrix (hX.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)).mulVec
    (fun x=>slaterIsometry x I) = _
  rw [slaterIsometry_column, Matrix.mulVec_smul, tensorMatrix_standardSlater]
  rfl

lemma slaterCoordinateEquiv_apply (v : SubsetIndex k r → ℂ) :
    (slaterCoordinateEquiv v).val = slaterIsometry.mulVec v := rfl

lemma channel_slater_intertwining (X : Matrix (Fin k) (Fin k) ℂ)
    (v : SubsetIndex k (r+1) → ℂ) :
    slaterIsometry.mulVec ((antisymmetricChannel (r:=r) X).mulVec v) =
      postprocess X 0 (slaterIsometry.mulVec v) := by
  have h := congrArg (fun L => L v) (antisymmetricChannel_restriction_conjugate X)
  have h' := congrArg (fun w => (slaterCoordinateEquiv w).val) h
  simpa only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
    slaterCoordinateEquiv_apply, postprocessRestriction, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.toLin'_apply] using h'.symm

lemma antisymmetricChannel_eigenmatrix (hrk : r+1 ≤ k)
    (X : Matrix (Fin k) (Fin k) ℂ) (hX : X.IsHermitian) :
    antisymmetricChannel (r:=r) X * (exteriorUnitary (r:=r+1) hX.eigenvectorUnitary :
        Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ) =
      (exteriorUnitary (r:=r+1) hX.eigenvectorUnitary :
        Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ) *
        diagonal (fun I => (AppendixB.shuffle k (r+1) hX.eigenvalues I.val : ℂ)) := by
  apply Matrix.ext_of_mulVec_single
  intro I
  apply (slaterCoordinateEquiv (k:=k) (r:=r+1)).injective
  apply Subtype.ext
  simp only [slaterCoordinateEquiv_apply, ← Matrix.mulVec_mulVec,
    channel_slater_intertwining]
  rw [Matrix.mulVec_mulVec, slater_mul_exteriorUnitary, tensor_eigenSlater_column,
    postprocess_smul, postprocess_eigenSlater (by omega) hrk hX 0]
  rw [Matrix.diagonal_mulVec_single]
  have hsingle : (Pi.single I ((AppendixB.shuffle k (r+1) hX.eigenvalues I.val:ℂ)*1) :
      SubsetIndex k (r+1) → ℂ) =
      (AppendixB.shuffle k (r+1) hX.eigenvalues I.val:ℂ) •
        (Pi.single I 1 : SubsetIndex k (r+1) → ℂ) := by
    ext J
    by_cases h : J=I
    · subst J; simp
    · simp [h,Pi.single_apply]
  rw [hsingle, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    slater_mul_exteriorUnitary, tensor_eigenSlater_column]
  simp only [smul_smul]
  congr 1
  ring

/-- Exact unitary diagonalization of the actual channel on a Hermitian input. -/
theorem antisymmetricChannel_unitaryDiagonal (hrk : r+1 ≤ k)
    (X : Matrix (Fin k) (Fin k) ℂ) (hX : X.IsHermitian) :
    antisymmetricChannel (r:=r) X =
      RevisionMatrixEntropy.unitaryDiagonal (exteriorUnitary (r:=r+1) hX.eigenvectorUnitary)
        (fun I => AppendixB.shuffle k (r+1) hX.eigenvalues I.val) := by
  have h := congrArg (fun M => M*star (exteriorUnitary (r:=r+1) hX.eigenvectorUnitary :
    Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ))
      (antisymmetricChannel_eigenmatrix hrk X hX)
  dsimp only at h
  rw [Matrix.mul_assoc, (exteriorUnitary (r:=r+1) hX.eigenvectorUnitary).prop.2,Matrix.mul_one] at h
  exact h

lemma unitaryDiagonal_column_eigenvector (U : Matrix.unitaryGroup (Fin k) ℂ)
    (v : Fin k→ℝ) (a : Fin k) :
    (RevisionMatrixEntropy.unitaryDiagonal U v).mulVec (fun b => U b a) =
      (v a:ℂ) • (fun b => U b a) := by
  have hmat : RevisionMatrixEntropy.unitaryDiagonal U v * (U:Matrix (Fin k) (Fin k) ℂ) =
      (U:Matrix (Fin k) (Fin k) ℂ)*diagonal (fun i=>(v i:ℂ)) := by
    change ((U:Matrix (Fin k) (Fin k) ℂ)*diagonal _*star (U:Matrix (Fin k) (Fin k) ℂ)) * _ = _
    rw [Matrix.mul_assoc,Matrix.mul_assoc,unitary.coe_star_mul_self,Matrix.mul_one]
  ext b
  have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℂ => M b a) hmat
  dsimp only at h
  rw [Matrix.mul_diagonal] at h
  simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,
    mul_comm (v a:ℂ)] using h

lemma tensor_transformedSlater_column (U : Matrix.unitaryGroup (Fin k) ℂ)
    (I : SubsetIndex k r) :
    (tensorMatrix (U:Matrix (Fin k) (Fin k) ℂ)*slaterIsometry).mulVec (Pi.single I 1) =
      ((Real.sqrt (r.factorial:ℝ):ℂ)⁻¹) • slater (fun j b=>U b (subsetEnum I j)) := by
  rw [←Matrix.mulVec_mulVec,Matrix.mulVec_single_one]
  change (tensorMatrix (U:Matrix (Fin k) (Fin k) ℂ)).mulVec (fun x=>slaterIsometry x I) = _
  rw [slaterIsometry_column,Matrix.mulVec_smul,tensorMatrix_standardSlater]

lemma antisymmetricChannel_eigenmatrix_of_unitary (hrk : r+1 ≤ k)
    (U : Matrix.unitaryGroup (Fin k) ℂ) (v : Fin k→ℝ) :
    antisymmetricChannel (r:=r) (RevisionMatrixEntropy.unitaryDiagonal U v) *
      (exteriorUnitary (r:=r+1) U : Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ) =
      (exteriorUnitary (r:=r+1) U : Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ)*
        diagonal (fun I=>(AppendixB.shuffle k (r+1) v I.val:ℂ)) := by
  apply Matrix.ext_of_mulVec_single
  intro I
  apply (slaterCoordinateEquiv (k:=k) (r:=r+1)).injective
  apply Subtype.ext
  simp only [slaterCoordinateEquiv_apply,←Matrix.mulVec_mulVec,channel_slater_intertwining]
  rw [Matrix.mulVec_mulVec,slater_mul_exteriorUnitary,tensor_transformedSlater_column,postprocess_smul]
  have hs := subset_shuffling_eigenvector (by omega) hrk
    (RevisionMatrixEntropy.unitaryDiagonal U v) (fun a b=>U b a) v
    (unitaryDiagonal_column_eigenvector U v) I.val I.property (0:Fin (r+1))
  change postprocess (RevisionMatrixEntropy.unitaryDiagonal U v) 0
    (slater (fun j b=>U b (subsetEnum I j))) = _ at hs
  rw [hs,Matrix.diagonal_mulVec_single]
  have hsingle : (Pi.single I ((AppendixB.shuffle k (r+1) v I.val:ℂ)*1) : SubsetIndex k (r+1)→ℂ) =
      (AppendixB.shuffle k (r+1) v I.val:ℂ) • (Pi.single I 1 : SubsetIndex k (r+1)→ℂ) := by
    ext J
    by_cases h : J=I
    · subst J; simp
    · simp [h,Pi.single_apply]
  rw [hsingle,Matrix.mulVec_smul,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    slater_mul_exteriorUnitary,tensor_transformedSlater_column]
  exact smul_comm _ _ _

/-- The exterior unitary diagonalizes the actual channel in any prescribed
one-particle eigenbasis, so no eigenvalue-ordering convention is required. -/
theorem antisymmetricChannel_of_unitaryDiagonal (hrk : r+1 ≤ k)
    (U : Matrix.unitaryGroup (Fin k) ℂ) (v : Fin k→ℝ) :
    antisymmetricChannel (r:=r) (RevisionMatrixEntropy.unitaryDiagonal U v) =
      RevisionMatrixEntropy.unitaryDiagonal (exteriorUnitary (r:=r+1) U)
        (fun I=>AppendixB.shuffle k (r+1) v I.val) := by
  have h := congrArg (fun M=>M*star (exteriorUnitary (r:=r+1) U :
    Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ))
      (antisymmetricChannel_eigenmatrix_of_unitary hrk U v)
  dsimp only at h
  rw [Matrix.mul_assoc, (exteriorUnitary (r:=r+1) U).prop.2,Matrix.mul_one] at h
  exact h

lemma renyi_subsetIndex (p : ℝ) (v : Finset (Fin k)→ℝ) :
    AppendixB.renyi p univ (fun _ : SubsetIndex k r=>1) (fun I=>v I.val)=
      AppendixB.renyi p (AppendixB.subsets k r) (fun _=>1) v := by
  have hs (f : Finset (Fin k)→ℝ) : (∑ I : SubsetIndex k r, f I.val)=
      ∑ I∈AppendixB.subsets k r, f I := by
    exact (Finset.sum_subtype (AppendixB.subsets k r)
      (fun I=>by simp [AppendixB.subsets,Finset.mem_powersetCard]) f).symm
  unfold AppendixB.renyi
  split_ifs
  · simpa only [one_mul] using congrArg Neg.neg (hs (fun I=>v I*Real.log (v I)))
  · simpa only [one_mul] using congrArg (fun x=>Real.log x/(1-p)) (hs (fun I=>v I^p))

/-- Proposition V.2 at the entropy level for actual output matrices. -/
theorem antisymmetricChannel_entropy (hrk : r+1 ≤ k) (p : ℝ) (hp : 0<p)
    (U : Matrix.unitaryGroup (Fin k) ℂ) (v : Fin k→ℝ) :
    RevisionMatrixEntropy.matrixRenyiEntropy p
      (antisymmetricChannel (r:=r) (RevisionMatrixEntropy.unitaryDiagonal U v)) =
      AppendixB.renyi p (AppendixB.subsets k (r+1)) (fun _=>1) (AppendixB.shuffle k (r+1) v) := by
  rw [antisymmetricChannel_of_unitaryDiagonal hrk U v,
    RevisionMatrixEntropy.matrixRenyiEntropy_unitaryDiagonal p hp,renyi_subsetIndex]

end AntisymmetricVerification
