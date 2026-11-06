import Antisymmetric.RevisionAntisymmetricNesting

/-! The actual partial-trace ladder recurrence from the paper. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

def cosetOperator : Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ :=
  1 - ∑ j : Fin r, swapFirstMatrix j

def liftedAntisym : Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) antisymMatrix

lemma swapFirstMatrix_isHermitian (j : Fin r) : (swapFirstMatrix (k := k) j).IsHermitian := by
  ext x y
  have he : swapFirstIndex j y = x ↔ swapFirstIndex j x = y := by
    rw [(swapFirstIndex_involutive j).eq_iff]
    exact eq_comm
  simp only [Matrix.conjTranspose_apply, swapFirstMatrix, he]
  split_ifs <;> simp

lemma cosetOperator_isHermitian : (cosetOperator (k := k) (r := r)).IsHermitian := by
  change (1 - ∑ j : Fin r, swapFirstMatrix (k := k) j).conjTranspose = _
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_sum,
    show ∀ j : Fin r, (swapFirstMatrix (k := k) j).conjTranspose = swapFirstMatrix j from
      fun j => (swapFirstMatrix_isHermitian j).eq]
  rfl

lemma antisymMatrixProduct_coset_right : (antisymMatrixProduct (k := k) (r := r)) =
    (((r + 1 : ℕ) : ℂ)⁻¹) • (liftedAntisym * cosetOperator) := by
  have h := congrArg Matrix.conjTranspose (antisymMatrixProduct_coset (k := k) (r := r))
  change antisymMatrixProduct.conjTranspose =
    ((((r + 1 : ℕ) : ℂ)⁻¹) • (cosetOperator * liftedAntisym)).conjTranspose at h
  simpa only [Matrix.conjTranspose_smul, star_inv₀, star_natCast, Matrix.conjTranspose_mul,
    antisymMatrixProduct_isHermitian.eq, cosetOperator_isHermitian.eq,
    show (liftedAntisym (k := k) (r := r)).conjTranspose = liftedAntisym from liftedAntisym_isHermitian] using h

lemma antisymMatrixProduct_idempotent :
    (antisymMatrixProduct (k := k) (r := r)) * antisymMatrixProduct = antisymMatrixProduct := by
  unfold antisymMatrixProduct
  rw [Matrix.submatrix_mul_equiv, antisymMatrix_idempotent]

lemma coset_sandwich (Z : Matrix (TensorIndex k r) (TensorIndex k r) ℂ)
    (hPZ : antisymMatrix * Z = Z) (hZP : Z * antisymMatrix = Z) :
    antisymMatrixProduct * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * antisymMatrixProduct =
      ((((r + 1 : ℕ) : ℂ)⁻¹) ^ 2) •
        (cosetOperator * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * cosetOperator) := by
  have ht : liftedAntisym * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * liftedAntisym =
      Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z := by
    unfold liftedAntisym
    rw [kronecker_multiply, kronecker_multiply, Matrix.one_mul, Matrix.one_mul, hPZ, hZP]
  conv_lhs =>
    enter [1, 1]
    rw [antisymMatrixProduct_coset]
  conv_lhs =>
    enter [2]
    rw [antisymMatrixProduct_coset_right]
  change (((((r + 1 : ℕ) : ℂ)⁻¹) • (cosetOperator * liftedAntisym)) *
    Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z *
    ((((r + 1 : ℕ) : ℂ)⁻¹) • (liftedAntisym * cosetOperator))) = _
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two]
  congr 1
  calc
    _ = cosetOperator * (liftedAntisym * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * liftedAntisym) * cosetOperator := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [ht]

lemma traceA_coset_sandwich (Z : Matrix (TensorIndex k r) (TensorIndex k r) ℂ) :
    traceA (cosetOperator * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * cosetOperator) =
      (k : ℂ) • Z - (r : ℂ) • Z - (r : ℂ) • Z +
        ∑ i : Fin r, ∑ j : Fin r,
          traceA (swapFirstMatrix i * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * swapFirstMatrix j) := by
  unfold cosetOperator
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Finset.sum_mul, Finset.mul_sum, traceA_add, traceA_sub, traceA_fintype_sum,
    traceA_kronecker, Matrix.trace_one, Fintype.card_fin, traceA_swapFirst_left,
    traceA_swapFirst_right, sum_const, card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul ℂ, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  abel

/-- All terms in the actual coset expansion, after lower-particle compression. -/
theorem compressed_traceA_coset_sandwich (h : Fin r)
    (Z : Matrix (TensorIndex k r) (TensorIndex k r) ℂ)
    (hPZ : antisymMatrix * Z = Z) (hZP : Z * antisymMatrix = Z) :
    antisymMatrix * traceA (cosetOperator *
      Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * cosetOperator) * antisymMatrix =
      ((k : ℂ) - 2 * r) • Z + ((r : ℂ) ^ 2) •
        (∑ a : Fin k, ∑ b : Fin k,
          (antisymMatrix * oneLegMatrix (matrixUnit b a) h * antisymMatrix) * Z *
            (antisymMatrix * oneLegMatrix (matrixUnit a b) h * antisymMatrix)) := by
  rw [traceA_coset_sandwich]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul, hPZ, hZP]
  simp_rw [compressed_traceA_two_swaps _ _ h Z hPZ hZP]
  simp only [sum_const, card_univ, Fintype.card_fin]
  simp only [← Nat.cast_smul_eq_nsmul ℂ]
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  ring

/-- The partial-trace ladder recurrence in actual tensor coordinates. The last
 term is exactly `r² R_r* R_r` by `antisymmetric_bell_gram_identity`, after
 identifying the chosen tail leg with a first tensor factor. -/
theorem antisymmetric_partialTrace_ladder (h : Fin r)
    (Z : Matrix (TensorIndex k r) (TensorIndex k r) ℂ)
    (hPZ : antisymMatrix * Z = Z) (hZP : Z * antisymMatrix = Z) :
    traceA (antisymMatrixProduct *
      Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * antisymMatrixProduct) =
      ((((r + 1 : ℕ) : ℂ)⁻¹) ^ 2) •
        (((k : ℂ) - 2 * r) • Z + ((r : ℂ) ^ 2) •
          (∑ a : Fin k, ∑ b : Fin k,
            (antisymMatrix * oneLegMatrix (matrixUnit b a) h * antisymMatrix) * Z *
              (antisymMatrix * oneLegMatrix (matrixUnit a b) h * antisymMatrix))) := by
  let Y := antisymMatrixProduct * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * antisymMatrixProduct
  have hQY : antisymMatrixProduct * Y = Y := by
    dsimp [Y]
    simp only [← Matrix.mul_assoc, antisymMatrixProduct_idempotent]
  have hYQ : Y * antisymMatrixProduct = Y := by
    dsimp [Y]
    simp only [Matrix.mul_assoc, antisymMatrixProduct_idempotent]
  have hs := antisym_partialTrace_support Y hQY hYQ
  rw [← hs]
  change antisymMatrix * traceA (antisymMatrixProduct *
    Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * antisymMatrixProduct) * antisymMatrix = _
  rw [coset_sandwich Z hPZ hZP, traceA_smul, Matrix.mul_smul, Matrix.smul_mul,
    compressed_traceA_coset_sandwich h Z hPZ hZP]

end AntisymmetricVerification
