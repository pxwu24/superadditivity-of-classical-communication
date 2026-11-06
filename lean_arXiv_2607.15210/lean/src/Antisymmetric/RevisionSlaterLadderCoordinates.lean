import Antisymmetric.RevisionSlaterGramCoordinates
import Preliminaries.RevisionKrausVectorization

/-! The actual partial-trace ladder in normalized Slater coordinates. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

lemma slater_sandwich_embed (Z : Matrix (SubsetIndex k r) (SubsetIndex k r) ℂ) :
    slaterIsometry.conjTranspose * (slaterIsometry * Z * slaterIsometry.conjTranspose) * slaterIsometry = Z := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, slaterIsometry_isometry, Matrix.one_mul]
  rw [Matrix.mul_assoc, slaterIsometry_isometry, Matrix.mul_one]

/-- `R_(r+2) R_(r+2)*` in actual normalized Slater coordinates. -/
theorem slaterDown_up_successor
    (Z : Matrix (SubsetIndex k (r + 1)) (SubsetIndex k (r + 1)) ℂ) :
    slaterDown k (r + 1) (slaterUp k (r + 1) Z) =
      ((((r + 2 : ℕ) : ℂ)⁻¹) ^ 2) •
        (((k : ℂ) - 2 * (r + 1 : ℕ)) • Z + (((r + 1 : ℕ) : ℂ) ^ 2) •
          slaterUp k r (slaterDown k r Z)) := by
  rw [slaterDown_up_formula]
  have hl := antisymmetric_partialTrace_ladder (k := k) (r := r + 1) 0
    (slaterIsometry * Z * slaterIsometry.conjTranspose)
    (slaterEmbed_projection_left Z) (slaterEmbed_projection_right Z)
  change traceA _ = (((((r + 1) + 1 : ℕ) : ℂ)⁻¹) ^ 2) •
    (((k : ℂ) - 2 * (r + 1 : ℕ)) •
      (slaterIsometry * Z * slaterIsometry.conjTranspose) + (((r + 1 : ℕ) : ℂ) ^ 2) •
        oneLegGram 0 (slaterIsometry * Z * slaterIsometry.conjTranspose)) at hl
  rw [hl]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    slater_sandwich_embed, slater_oneLegGram_coordinates]

/-- The one-particle base case, `R_1 R_1* = k id`, is derived from the same
 actual permutation/partial-trace definitions. -/
theorem slaterDown_up_zero (Z : Matrix (SubsetIndex k 0) (SubsetIndex k 0) ℂ) :
    slaterDown k 0 (slaterUp k 0 Z) = (k : ℂ) • Z := by
  rw [slaterDown_up_formula, coset_sandwich _ (slaterEmbed_projection_left Z)
    (slaterEmbed_projection_right Z)]
  simp only [cosetOperator, Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
    Nat.zero_add, Nat.cast_one, inv_one, one_pow, one_smul, Matrix.one_mul, Matrix.mul_one,
    traceA_kronecker, Matrix.trace_one, Fintype.card_fin]
  rw [Matrix.mul_smul, Matrix.smul_mul, slater_sandwich_embed]

/-- The actual rectangular matrix of the Slater-coordinate partial trace. -/
def slaterReductionMatrix (k r : ℕ) :
    Matrix (SubsetIndex k r × SubsetIndex k r)
      (SubsetIndex k (r + 1) × SubsetIndex k (r + 1)) ℂ :=
  krausSupermatrix (reductionKraus (slaterProduct (k := k) (r := r)) slaterIsometry)

/-- The weighted lowering matrix used to avoid denominators in the spectral
 induction. -/
def weightedSlaterReduction (k r : ℕ) :
    Matrix (SubsetIndex k r × SubsetIndex k r)
      (SubsetIndex k (r + 1) × SubsetIndex k (r + 1)) ℂ :=
  ((r + 1 : ℕ) : ℂ) • slaterReductionMatrix k r

lemma slaterReductionMatrix_mulVec
    (Y : Matrix (SubsetIndex k (r + 1)) (SubsetIndex k (r + 1)) ℂ) :
    (slaterReductionMatrix k r).mulVec (matrixVec Y) = matrixVec (slaterDown k r Y) := by
  rw [slaterReductionMatrix, krausSupermatrix_mulVec]
  rw [slaterDown, downCoordinates_eq_kraus]

lemma slaterReductionMatrix_adj_mulVec
    (Z : Matrix (SubsetIndex k r) (SubsetIndex k r) ℂ) :
    (slaterReductionMatrix k r).conjTranspose.mulVec (matrixVec Z) = matrixVec (slaterUp k r Z) := by
  rw [slaterReductionMatrix, krausSupermatrix_conjTranspose_mulVec]
  rw [slaterUp, upCoordinates_eq_kraus]

end AntisymmetricVerification
