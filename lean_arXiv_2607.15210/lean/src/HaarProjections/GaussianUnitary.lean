import HaarProjections.HaarMeasure
import Mathlib.Analysis.InnerProductSpace.LinearMap

open scoped BigOperators ComplexOrder
open Matrix

namespace HaarProjection
noncomputable section

variable {E D : Type*} [Fintype E] [Fintype D] [DecidableEq E] [DecidableEq D]

/-- A unitary matrix acts as a complex linear isometry on Euclidean coordinate vectors. -/
def unitaryEuclideanIsometry (U : Matrix.unitaryGroup E ℂ) :
    EuclideanSpace ℂ E ≃ₗᵢ[ℂ] EuclideanSpace ℂ E :=
  ((WithLp.linearEquiv 2 ℂ (E → ℂ)).trans
    ((Matrix.UnitaryGroup.toLinearEquiv U).trans
      (WithLp.linearEquiv 2 ℂ (E → ℂ)).symm)).isometryOfInner (by
    intro x y
    change (U.val *ᵥ (WithLp.equiv 2 (E → ℂ)) y) ⬝ᵥ
      star (U.val *ᵥ (WithLp.equiv 2 (E → ℂ)) x) =
      (WithLp.equiv 2 (E → ℂ)) y ⬝ᵥ star ((WithLp.equiv 2 (E → ℂ)) x)
    have hu : U.val.conjTranspose * U.val = 1 := U.prop.1
    rw [dotProduct_comm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hu, Matrix.one_mulVec, dotProduct_comm])

/-- Tensoring a unitary matrix with an identity matrix gives a unitary matrix. -/
def unitaryTensorIdentity (U : Matrix.unitaryGroup E ℂ) : Matrix.unitaryGroup (E × D) ℂ := by
  refine ⟨Matrix.kronecker (U : Matrix E E ℂ) (1 : Matrix D D ℂ), ?_⟩
  apply Matrix.mem_unitaryGroup_iff'.mpr
  have hs : (Matrix.kronecker (U : Matrix E E ℂ) (1 : Matrix D D ℂ)).conjTranspose =
      Matrix.kronecker (U : Matrix E E ℂ).conjTranspose (1 : Matrix D D ℂ) := by
    ext ⟨i, d⟩ ⟨j, e⟩
    by_cases hde : d = e
    · subst e
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply]
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, hde, Ne.symm hde]
  change (Matrix.kronecker (U : Matrix E E ℂ) (1 : Matrix D D ℂ)).conjTranspose * _ = _
  rw [hs]
  have hu : (U : Matrix E E ℂ).conjTranspose * U = 1 := U.prop.1
  calc
    _ = Matrix.kronecker ((U : Matrix E E ℂ).conjTranspose * (U : Matrix E E ℂ))
        ((1 : Matrix D D ℂ) * 1) :=
      (Matrix.mul_kronecker_mul _ _ _ _).symm
    _ = 1 := by rw [hu, Matrix.one_mul]; simp

/-- Left multiplication of a rectangular matrix, viewed as a real Euclidean isometry. -/
def gaussianLeftUnitaryIsometry (U : Matrix.unitaryGroup E ℂ) :
    EuclideanSpace ℂ (E × D) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (E × D) :=
  { (unitaryEuclideanIsometry (unitaryTensorIdentity (D := D) U)).toLinearEquiv.restrictScalars ℝ with
    norm_map' := (unitaryEuclideanIsometry (unitaryTensorIdentity (D := D) U)).norm_map }

/-- Coordinate formula identifying the real isometry with left matrix multiplication. -/
theorem gaussianLeftUnitaryIsometry_apply (U : Matrix.unitaryGroup E ℂ)
    (x : EuclideanSpace ℂ (E × D)) (i : E) (d : D) :
    gaussianLeftUnitaryIsometry U x (i, d) = ∑ j : E, U i j * x (j, d) := by
  change (Matrix.kronecker (U : Matrix E E ℂ) (1 : Matrix D D ℂ) *ᵥ
    (WithLp.equiv 2 (E × D → ℂ)) x) (i, d) = _
  simp [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type]

end
end HaarProjection

