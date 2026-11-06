import Antisymmetric.RevisionAntisymmetricSwap

/-! The signed coset recursion as an actual matrix identity in first-factor
 product coordinates. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

lemma matrix_fintypeSum_mulVec {ι α : Type*} [Fintype ι] [Fintype α]
    (M : ι → Matrix α α ℂ) (f : α → ℂ) :
    (∑ j, M j).mulVec f = ∑ j, (M j).mulVec f := by
  ext x
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]

lemma antisymMatrixProduct_mulVec (f : (Fin k × TensorIndex k r) → ℂ) :
    antisymMatrixProduct.mulVec f =
      antisymmetrize (f ∘ firstTensorEquiv.symm) ∘ firstTensorEquiv := by
  rw [antisymMatrixProduct, Matrix.submatrix_mulVec_equiv, antisymMatrix_mulVec]

lemma liftedAntisym_mulVec (f : (Fin k × TensorIndex k r) → ℂ) :
    (Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
      (antisymMatrix (k := k) (r := r))).mulVec f =
      tailAntisymmetrize (f ∘ firstTensorEquiv.symm) ∘ firstTensorEquiv := by
  ext ⟨a,x⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, if_true, sum_const_zero]
  change (antisymMatrix.mulVec (fun y => f (a,y))) x = _
  rw [antisymMatrix_mulVec]
  simp only [tailAntisymmetrize, firstTensorEquiv, Fin.consEquiv, Function.comp_apply,
    Equiv.coe_fn_mk, Fin.cons_zero, Fin.tail_cons, Fin.cons_self_tail]
  rfl

/-- Matrix form of the exact coset recursion in B.2. -/
theorem antisymMatrixProduct_coset :
    (antisymMatrixProduct (k := k) (r := r)) =
      (((r + 1 : ℕ) : ℂ)⁻¹) •
        ((1 - ∑ j : Fin r, swapFirstMatrix (k := k) j) *
          Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
            (antisymMatrix (k := k) (r := r))) := by
  classical
  apply Matrix.ext_of_mulVec_single
  intro y
  simp only [Matrix.smul_mulVec_assoc, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, matrix_fintypeSum_mulVec, swapFirstMatrix_mulVec,
    liftedAntisym_mulVec, antisymMatrixProduct_mulVec]
  ext x
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply]
  rw [antisymmetrize_recursion]
  simp only [swapFirstIndex_cons]

end AntisymmetricVerification
