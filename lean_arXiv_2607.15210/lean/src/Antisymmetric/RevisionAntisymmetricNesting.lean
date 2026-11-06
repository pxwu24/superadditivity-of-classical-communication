import Antisymmetric.RevisionAntisymmetricPartialTrace

/-! Nesting of actual antisymmetrizers, needed to put partial traces back in
 the lower-particle antisymmetric operator space. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

lemma tailAntisymmetrize_of_alternating {f : TensorVector k (r + 1)}
    (hf : alternating f) : tailAntisymmetrize f = f := by
  ext x
  have hs : ∀ σ : Perm (Fin r),
      signC σ * f (Fin.cons (x 0) (Fin.tail x ∘ σ)) = f x := by
    intro σ
    have h := congrFun (hf (Perm.decomposeFin.symm (0,σ))) x
    simp only [permute, decompose_permute_index, swap_self, Equiv.coe_refl,
      Function.comp_id, Pi.smul_apply, smul_eq_mul, signC_decompose, ite_true, one_mul] at h
    change f (Fin.cons (x 0) (Fin.tail x ∘ σ)) = signC σ * f x at h
    rw [h, ← mul_assoc, signC_mul_self, one_mul]
  simp only [tailAntisymmetrize, antisymmetrize, permute, hs, sum_const, card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hf0 : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  simp [hf0]

lemma antisymMatrixProduct_isHermitian :
    (antisymMatrixProduct (k := k) (r := r)).IsHermitian :=
  antisymMatrix_isHermitian.submatrix firstTensorEquiv

lemma liftedAntisym_isHermitian :
    (Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
      (antisymMatrix (k := k) (r := r))).IsHermitian := by
  ext ⟨a,x⟩ ⟨b,y⟩
  by_cases h : a = b
  · subst b
    simpa [Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply] using
      (antisymMatrix_flip (k := k) (r := r) x y).symm
  · simp [Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, h, Ne.symm h]

/-- `I ⊗ Π_r` fixes the range of `Π_(r+1)`. -/
theorem antisymMatrixProduct_tail_left :
    Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
      (antisymMatrix (k := k) (r := r)) * antisymMatrixProduct = antisymMatrixProduct := by
  classical
  apply Matrix.ext_of_mulVec_single
  intro y
  rw [← Matrix.mulVec_mulVec, antisymMatrixProduct_mulVec, liftedAntisym_mulVec]
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  rw [tailAntisymmetrize_of_alternating (antisymmetrize_alternating _)]

/-- The corresponding right nesting follows from Hermiticity. -/
theorem antisymMatrixProduct_tail_right :
    (antisymMatrixProduct (k := k) (r := r)) *
      Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
        (antisymMatrix (k := k) (r := r)) = antisymMatrixProduct := by
  have h := congrArg Matrix.conjTranspose (antisymMatrixProduct_tail_left (k := k) (r := r))
  simpa only [Matrix.conjTranspose_mul, antisymMatrixProduct_isHermitian.eq,
    liftedAntisym_isHermitian.eq] using h

lemma traceA_second_left (H : Matrix (TensorIndex k r) (TensorIndex k r) ℂ)
    (Y : Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ) :
    traceA (Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) H * Y) = H * traceA Y := by
  ext x y
  simp only [traceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ, if_true, sum_const_zero]
  rw [sum_comm]
  simp only [Finset.mul_sum]

lemma traceA_second_right (H : Matrix (TensorIndex k r) (TensorIndex k r) ℂ)
    (Y : Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ) :
    traceA (Y * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) H) = traceA Y * H := by
  ext x y
  simp only [traceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ, if_true, sum_const_zero]
  rw [sum_comm]
  simp only [Finset.sum_mul]

/-- The reduced operator of an antisymmetrically supported matrix is again
 supported on the smaller antisymmetric subspace. -/
theorem antisym_partialTrace_support
    (Y : Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ)
    (hPY : antisymMatrixProduct * Y = Y) (hYP : Y * antisymMatrixProduct = Y) :
    antisymMatrix * traceA Y * antisymMatrix = traceA Y := by
  rw [← traceA_second_left, ← traceA_second_right]
  congr 1
  have hleft : Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) antisymMatrix * Y = Y := by
    calc
      _ = Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) antisymMatrix *
          (antisymMatrixProduct * Y) := by rw [hPY]
      _ = Y := by rw [← Matrix.mul_assoc, antisymMatrixProduct_tail_left, hPY]
  have hright : Y * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) antisymMatrix = Y := by
    calc
      _ = (Y * antisymMatrixProduct) *
          Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) antisymMatrix := by rw [hYP]
      _ = Y := by rw [Matrix.mul_assoc, antisymMatrixProduct_tail_right, hYP]
  rw [hleft, hright]

end AntisymmetricVerification
