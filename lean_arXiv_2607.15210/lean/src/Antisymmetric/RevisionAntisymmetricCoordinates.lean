import Antisymmetric.RevisionAntisymmetricLadder

/-! Normalized Slater coordinates identify the actual antisymmetric subspace
 with the subset coordinate space. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

lemma slaterIsometry_column (I : SubsetIndex k r) :
    (fun x => slaterIsometry x I) =
      ((Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹) • standardSlater I := rfl

/-- Each Slater column belongs to the actual antisymmetric projection range. -/
theorem antisymMatrix_mul_slaterIsometry :
    (antisymMatrix (k := k) (r := r)) * slaterIsometry = slaterIsometry := by
  ext x I
  change (antisymMatrix.mulVec (fun y => slaterIsometry y I)) x = _
  rw [slaterIsometry_column, antisymMatrix_mulVec, antisymmetrize_smul,
    standardSlater, antisymmetrize_slater]
  rfl

/-- The Slater isometry has range exactly the antisymmetric projection. -/
theorem slaterIsometry_range_projection :
    (slaterIsometry (k := k) (r := r)) * slaterIsometry.conjTranspose = antisymMatrix := by
  let S := slaterIsometry (k := k) (r := r)
  let M := S * S.conjTranspose
  have hSSS : M * S = S := by
    dsimp [M,S]
    rw [Matrix.mul_assoc, slaterIsometry_isometry, Matrix.mul_one]
  have hc : ((Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹) ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < r.factorial)).ne'
  have hfix : ∀ I : SubsetIndex k r, M.mulVec (standardSlater I) = standardSlater I := by
    intro I
    have hh : M.mulVec (fun y => S y I) = fun y => S y I := by
      ext x
      exact congrFun (congrFun hSSS x) I
    change M.mulVec (fun y => slaterIsometry y I) = (fun y => slaterIsometry y I) at hh
    rw [slaterIsometry_column, Matrix.mulVec_smul] at hh
    ext x
    have hx := congrFun hh x
    exact mul_left_cancel₀ hc hx
  have hfixAll : ∀ f : TensorVector k r, alternating f → M.mulVec f = f := by
    intro f hf
    have h := alternating_expansion_vector hf
    calc
      M.mulVec f = M.mulVec (∑ I : SubsetIndex k r, f (subsetEnum I) • standardSlater I) := congrArg _ h
      _ = ∑ I : SubsetIndex k r, f (subsetEnum I) • standardSlater I := by
        simp only [mulVec_fintype_sum, Matrix.mulVec_smul, hfix]
      _ = f := h.symm
  have hMP : M * antisymMatrix = antisymMatrix := by
    apply Matrix.ext_of_mulVec_single
    intro y
    rw [← Matrix.mulVec_mulVec, antisymMatrix_mulVec]
    exact hfixAll _ (antisymmetrize_alternating _)
  have hPM : antisymMatrix * M = M := by
    dsimp [M,S]
    rw [← Matrix.mul_assoc, antisymMatrix_mul_slaterIsometry]
  have h := congrArg Matrix.conjTranspose hMP
  simp only [Matrix.conjTranspose_mul, antisymMatrix_isHermitian.eq] at h
  have hM : M.conjTranspose = M := by simp [M, Matrix.conjTranspose_mul]
  rw [hM, hPM] at h
  exact h

/-- Reconstruction of every antisymmetrically supported operator from its
 normalized Slater-coordinate matrix. -/
theorem slater_coordinates_reconstruct
    (Y : Matrix (TensorIndex k r) (TensorIndex k r) ℂ)
    (hPY : antisymMatrix * Y = Y) (hYP : Y * antisymMatrix = Y) :
    slaterIsometry * (slaterIsometry.conjTranspose * Y * slaterIsometry) * slaterIsometry.conjTranspose = Y := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, slaterIsometry_range_projection, hPY]
  rw [Matrix.mul_assoc, slaterIsometry_range_projection, hYP]

end AntisymmetricVerification
