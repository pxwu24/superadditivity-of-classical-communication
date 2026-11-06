import Antisymmetric.RevisionSlaterLadderCoordinates

/-! The exact rectangular Gram ladder of the actual normalized Slater partial
trace. No spectral recurrence is assumed: it follows from the permutation
formula for the antisymmetric projection. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

lemma matrix_eq_of_mulVec_matrixVec {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Matrix κ (ι × ι) ℂ}
    (h : ∀ Z : Matrix ι ι ℂ, M.mulVec (matrixVec Z) = N.mulVec (matrixVec Z)) : M = N := by
  apply Matrix.ext_of_mulVec_single
  intro i
  exact h (fun a b => (Pi.single i (1 : ℂ) : (ι × ι) → ℂ) (a,b))

lemma matrixVec_smul {ι : Type*} (c : ℂ) (Z : Matrix ι ι ℂ) :
    matrixVec (c • Z) = c • matrixVec Z := rfl
lemma matrixVec_add {ι : Type*} (Z W : Matrix ι ι ℂ) :
    matrixVec (Z + W) = matrixVec Z + matrixVec W := rfl

lemma slaterReductionMatrix_gram_zero :
    slaterReductionMatrix k 0 * (slaterReductionMatrix k 0).conjTranspose =
      (k : ℂ) • (1 : Matrix (SubsetIndex k 0 × SubsetIndex k 0) _ ℂ) := by
  apply matrix_eq_of_mulVec_matrixVec
  intro Z
  rw [← Matrix.mulVec_mulVec, slaterReductionMatrix_adj_mulVec,
    slaterReductionMatrix_mulVec, slaterDown_up_zero, matrixVec_smul,
    Matrix.smul_mulVec_assoc, Matrix.one_mulVec]

lemma slaterReductionMatrix_gram_successor :
    slaterReductionMatrix k (r+1) * (slaterReductionMatrix k (r+1)).conjTranspose =
      ((((r+2 : ℕ) : ℂ)⁻¹)^2) •
        ((((k:ℂ)-2*(r+1:ℕ)) • 1) +
          (((r+1:ℕ):ℂ)^2) •
            ((slaterReductionMatrix k r).conjTranspose * slaterReductionMatrix k r)) := by
  apply matrix_eq_of_mulVec_matrixVec
  intro Z
  rw [← Matrix.mulVec_mulVec, slaterReductionMatrix_adj_mulVec,
    slaterReductionMatrix_mulVec, slaterDown_up_successor]
  simp only [matrixVec_smul, matrixVec_add, Matrix.smul_mulVec_assoc,
    Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    slaterReductionMatrix_mulVec, slaterReductionMatrix_adj_mulVec]

/-- The actual positive Gram operator at every exterior degree. -/
def slaterLadderGram (k : ℕ) : (r : ℕ) →
    Matrix (SubsetIndex k r × SubsetIndex k r) (SubsetIndex k r × SubsetIndex k r) ℂ
  | 0 => 0
  | r+1 => (weightedSlaterReduction k r).conjTranspose * weightedSlaterReduction k r

@[simp] lemma slaterLadderGram_zero : slaterLadderGram k 0 = 0 := rfl
@[simp] lemma slaterLadderGram_successor : slaterLadderGram k (r+1) =
    (weightedSlaterReduction k r).conjTranspose * weightedSlaterReduction k r := rfl

lemma weightedSlaterReduction_gram :
    (weightedSlaterReduction k r).conjTranspose * weightedSlaterReduction k r =
      (((r+1:ℕ):ℂ)^2) •
        ((slaterReductionMatrix k r).conjTranspose * slaterReductionMatrix k r) := by
  simp only [weightedSlaterReduction, Matrix.conjTranspose_smul, star_natCast,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

/-- The paper's Gram recurrence, proved for the actual rectangular reduction
matrices. The particle index is `r+1`; weighting by this index removes all
normalizing denominators. -/
theorem weightedSlaterReduction_ladder (k r : ℕ) :
    weightedSlaterReduction k r * (weightedSlaterReduction k r).conjTranspose =
      ((k:ℂ)-2*(r:ℂ)) • 1 + slaterLadderGram k r := by
  cases r with
  | zero =>
    simp only [weightedSlaterReduction, Nat.zero_add, Nat.cast_one, one_smul,
      slaterLadderGram_zero, Nat.cast_zero, mul_zero, sub_zero, add_zero]
    exact slaterReductionMatrix_gram_zero
  | succ r =>
    rw [slaterLadderGram_successor, weightedSlaterReduction_gram]
    simp only [weightedSlaterReduction, Matrix.conjTranspose_smul, star_natCast,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [slaterReductionMatrix_gram_successor, smul_smul]
    have hc : (((r+1+1:ℕ):ℂ) * ((r+1+1:ℕ):ℂ)) *
        ((((r+2:ℕ):ℂ)⁻¹)^2) = 1 := by
      have hz : ((r+2:ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : r+2≠0)
      simp only [show r+1+1=r+2 by omega]
      rw [← pow_two, ← mul_pow]
      simp only [mul_inv_cancel₀ hz, one_pow]
    rw [hc, one_smul]

end AntisymmetricVerification
