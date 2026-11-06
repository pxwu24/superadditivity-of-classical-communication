import RandomCompression.BlockModification
import RandomCompression.ProjectionStrongConvergence
import Mathlib.Analysis.CStarAlgebra.Hom

open Matrix
open scoped Matrix.L2OpNorm

noncomputable section
namespace ProjectionChannels

local instance matrixCStarAlgebra {n : Type*} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance
  norm_mul_self_le := CStarRing.norm_mul_self_le

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- The identity-output tensor embedding as an actual star algebra homomorphism. -/
def matrixTensorIdentity : Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ where
  toFun M := Matrix.kronecker M (1 : Matrix k k ℂ)
  map_zero' := by simp
  map_one' := Matrix.one_kronecker_one
  map_add' M N := Matrix.add_kronecker M N 1
  map_mul' M N := by
    simpa only [Matrix.one_mul] using Matrix.mul_kronecker_mul M N (1 : Matrix k k ℂ) 1
  commutes' c := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [Matrix.kronecker_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply,
      Matrix.one_apply]
    split_ifs <;> simp_all
  map_star' M := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
      Matrix.one_apply]
    split_ifs <;> simp_all

theorem matrixTensorIdentity_injective [Nonempty k] :
    Function.Injective (matrixTensorIdentity (n := n) (k := k)) := by
  intro M N h
  let a : k := Classical.choice inferInstance
  ext i j
  have hh := congrArg (fun A : Matrix (n × k) (n × k) ℂ => A (i,a) (j,a)) h
  simpa [matrixTensorIdentity, Matrix.kronecker_apply] using hh

/-- Tensoring by an identity preserves the Euclidean operator norm. -/
theorem norm_kronecker_identity [Nonempty k] (M : Matrix n n ℂ) :
    ‖Matrix.kronecker M (1 : Matrix k k ℂ)‖ = ‖M‖ := by
  exact NonUnitalStarAlgHom.norm_map (matrixTensorIdentity (n := n) (k := k))
    matrixTensorIdentity_injective M

end ProjectionChannels
