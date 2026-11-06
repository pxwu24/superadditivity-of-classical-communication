import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Nonzero spectral multiplicities of rectangular Gram operators.

The equivalence is given explicitly by A, with inverse λ⁻¹ A*.
This is the dimension-transfer step used by the antisymmetric Bell ladder.
-/
namespace AntisymmetricVerification
open Module.End LinearMap
open scoped ComplexOrder
noncomputable section

variable {𝕜 E F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

def productEigenspaceEquiv (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E)
    (lam : 𝕜) (hlam : lam ≠ 0) :
    eigenspace (B.comp A) lam ≃ₗ[𝕜] eigenspace (A.comp B) lam where
  toFun x := ⟨A x, by
    have hx := mem_eigenspace_iff.mp x.property
    apply mem_eigenspace_iff.mpr
    change A (B (A x)) = lam • A x
    change B (A x) = lam • (x:E) at hx
    rw [hx, map_smul]⟩
  invFun y := ⟨lam⁻¹ • B y, by
    have hy := mem_eigenspace_iff.mp y.property
    apply mem_eigenspace_iff.mpr
    change B (A (lam⁻¹ • B y)) = lam • (lam⁻¹ • B y)
    change A (B y) = lam • (y:F) at hy
    rw [map_smul, map_smul, hy, map_smul]
    simp only [smul_smul, inv_mul_cancel₀ hlam, mul_inv_cancel₀ hlam, one_smul]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := mem_eigenspace_iff.mp x.property
    change B (A x) = lam • (x:E) at hx
    change lam⁻¹ • B (A x) = x
    rw [hx, inv_smul_smul₀ hlam]
  right_inv y := by
    apply Subtype.ext
    have hy := mem_eigenspace_iff.mp y.property
    change A (B y) = lam • (y:F) at hy
    change A (lam⁻¹ • B y) = y
    rw [map_smul, hy, inv_smul_smul₀ hlam]
  map_add' x y := by apply Subtype.ext; exact map_add A (x:E) (y:E)
  map_smul' c x := by apply Subtype.ext; exact map_smul A c (x:E)

theorem product_eigenspace_finrank (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E)
    (lam : 𝕜) (hlam : lam ≠ 0) :
    Module.finrank 𝕜 (eigenspace (B.comp A) lam) =
      Module.finrank 𝕜 (eigenspace (A.comp B) lam) :=
  (productEigenspaceEquiv A B lam hlam).finrank_eq

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def gramEigenspaceEquiv (A : Matrix m n ℂ) (lam : ℂ) (hlam : lam ≠ 0) :
    eigenspace (Matrix.toLin' (A.conjTranspose*A)) lam ≃ₗ[ℂ]
      eigenspace (Matrix.toLin' (A*A.conjTranspose)) lam := by
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact productEigenspaceEquiv (Matrix.toLin' A) (Matrix.toLin' A.conjTranspose) lam hlam

theorem gram_eigenspace_finrank (A : Matrix m n ℂ) (lam : ℂ) (hlam : lam ≠ 0) :
    Module.finrank ℂ (eigenspace (Matrix.toLin' (A.conjTranspose*A)) lam) =
      Module.finrank ℂ (eigenspace (Matrix.toLin' (A*A.conjTranspose)) lam) :=
  (gramEigenspaceEquiv A lam hlam).finrank_eq

theorem gram_kernel (A : Matrix m n ℂ) :
    LinearMap.ker (Matrix.toLin' (A.conjTranspose*A)) =
      LinearMap.ker (Matrix.toLin' A) := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
  constructor
  · intro hx
    apply dotProduct_star_self_eq_zero.mp
    have h : dotProduct (star x) ((A.conjTranspose*A).mulVec x) = 0 := by rw [hx, dotProduct_zero]
    simpa only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_conjTranspose, star_star] using h
  · intro hx
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

theorem gram_zero_multiplicity (A : Matrix m n ℂ)
    (hA : Function.Surjective (Matrix.toLin' A)) :
    Module.finrank ℂ (eigenspace (Matrix.toLin' (A.conjTranspose*A)) 0) +
      Fintype.card m = Fintype.card n := by
  rw [eigenspace_zero, gram_kernel]
  have h := (Matrix.toLin' A).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hA, finrank_top, Module.finrank_pi] at h
  simpa [Module.finrank_pi, add_comm] using h

end
end AntisymmetricVerification
