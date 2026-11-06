import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Tactic

/-! Exact vectorization of Kraus maps and their Hilbert--Schmidt adjoints.
These identities identify the rectangular partial-trace matrices used in
the antisymmetric Gram ladder. -/

open Matrix Finset
open scoped BigOperators
noncomputable section
namespace AntisymmetricVerification

variable {A C D : Type*} [Fintype A] [Fintype C] [Fintype D]

def matrixVec (Y : Matrix C D ℂ) : C×D → ℂ := fun ij => Y ij.1 ij.2

lemma matrixVec_injective : Function.Injective (matrixVec : Matrix C D ℂ → C×D → ℂ) := by
  intro Y Z h
  ext i j
  exact congrFun h (i,j)

/-- Coordinate matrix of Y ↦ Σ_a K_a Y K_a*. -/
def krausSupermatrix (K : A → Matrix D C ℂ) : Matrix (D×D) (C×C) ℂ :=
  fun ij IJ => ∑ a, K a ij.1 IJ.1 * star (K a ij.2 IJ.2)

lemma krausSupermatrix_mulVec (K : A → Matrix D C ℂ) (Y : Matrix C C ℂ) :
    (krausSupermatrix K).mulVec (matrixVec Y) =
      matrixVec (∑ a, K a * Y * (K a).conjTranspose) := by
  ext ⟨i,j⟩
  simp only [krausSupermatrix,matrixVec,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
  simp only [Finset.sum_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext J
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro I _
  ring

lemma krausSupermatrix_conjTranspose (K : A → Matrix D C ℂ) :
    (krausSupermatrix K).conjTranspose =
      krausSupermatrix (fun a => (K a).conjTranspose) := by
  ext ⟨I,J⟩ ⟨i,j⟩
  simp only [krausSupermatrix,Matrix.conjTranspose_apply,star_sum,StarMul.star_mul,star_star]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma krausSupermatrix_conjTranspose_mulVec (K : A → Matrix D C ℂ) (Z : Matrix D D ℂ) :
    (krausSupermatrix K).conjTranspose.mulVec (matrixVec Z) =
      matrixVec (∑ a, (K a).conjTranspose * Z * K a) := by
  rw [krausSupermatrix_conjTranspose,krausSupermatrix_mulVec]
  simp only [Matrix.conjTranspose_conjTranspose]

end AntisymmetricVerification
