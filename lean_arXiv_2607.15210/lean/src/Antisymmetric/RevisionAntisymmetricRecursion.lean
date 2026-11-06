import Antisymmetric.RevisionAntisymmetric
import Mathlib.GroupTheory.Perm.Fin

/-! The exact coset recursion for the antisymmetrizer used by the Bell-output
 ladder calculation. It follows from the actual permutation sum. -/
noncomputable section
open Finset Equiv
namespace AntisymmetricVerification
variable {k r : ℕ}

/-- Antisymmetrize the last `r` coordinates, retaining the first coordinate. -/
def tailAntisymmetrize (f : TensorVector k (r + 1)) : TensorVector k (r + 1) :=
  fun x => antisymmetrize (fun y => f (Fin.cons (x 0) y)) (Fin.tail x)

lemma decompose_permute_index (x : TensorIndex k (r + 1)) (p : Fin (r + 1))
    (σ : Perm (Fin r)) :
    x ∘ (Perm.decomposeFin.symm (p, σ)) =
      Fin.cons ((x ∘ Equiv.swap 0 p) 0)
        (fun j => (x ∘ Equiv.swap 0 p) (σ j).succ) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

lemma signC_decompose (p : Fin (r + 1)) (σ : Perm (Fin r)) :
    signC (Perm.decomposeFin.symm (p, σ)) =
      (if p = 0 then (1 : ℂ) else -1) * signC σ := by
  unfold signC
  rw [Perm.decomposeFin.symm_sign]
  split_ifs <;> simp_all

lemma antisymmetrize_coset_sum (f : TensorVector k (r + 1)) (x : TensorIndex k (r + 1)) :
    antisymmetrize f x = ((r + 1 : ℕ) : ℂ)⁻¹ *
      ∑ p : Fin (r + 1), (if p = 0 then (1 : ℂ) else -1) *
        tailAntisymmetrize f (x ∘ Equiv.swap 0 p) := by
  have hsum :
      (∑ σ : Perm (Fin (r + 1)), signC σ * permute σ f x) =
      ∑ p : Fin (r + 1), (if p = 0 then (1 : ℂ) else -1) *
        ∑ σ : Perm (Fin r), signC σ *
          f (Fin.cons ((x ∘ Equiv.swap 0 p) 0)
            (fun j => (x ∘ Equiv.swap 0 p) (σ j).succ)) := by
    rw [← Equiv.sum_comp Perm.decomposeFin.symm]
    simp only [Fintype.sum_prod_type, signC_decompose, permute, decompose_permute_index,
      mul_assoc, Finset.mul_sum]
  unfold antisymmetrize
  rw [hsum]
  simp only [tailAntisymmetrize, antisymmetrize, permute, Fin.tail, Function.comp_def]
  have hfac : (((r + 1).factorial : ℕ) : ℂ)⁻¹ =
      ((r + 1 : ℕ) : ℂ)⁻¹ * (r.factorial : ℂ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_comm]
  rw [hfac, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The paper's coset recursion, with the singled-out leg first rather than
 last: `Π_(r+1) = (I - Σ_j swap(0,j+1)) (I ⊗ Π_r)/(r+1)`. -/
theorem antisymmetrize_recursion (f : TensorVector k (r + 1)) :
    antisymmetrize f = fun x => ((r + 1 : ℕ) : ℂ)⁻¹ *
      (tailAntisymmetrize f x -
        ∑ j : Fin r, tailAntisymmetrize f (x ∘ Equiv.swap 0 j.succ)) := by
  funext x
  rw [antisymmetrize_coset_sum, Fin.sum_univ_succ]
  simp only [ite_true, swap_self, Equiv.coe_refl, Function.comp_id, one_mul,
    Fin.succ_ne_zero, ite_false, neg_mul, one_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

end AntisymmetricVerification
