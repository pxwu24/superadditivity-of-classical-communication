import StrongConvergence.StrongConvergenceFreePeel
import StrongConvergence.StrongConvergenceFreeMoments

open Equiv Equiv.Perm
namespace ProjectionChannels.TensorHaar

lemma finRotate_val (n : ℕ) (i : Fin n) :
    (finRotate n i).val = if i.val + 1 = n then 0 else i.val + 1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [coe_finRotate]
    simp only [Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega

lemma finRotate_split_arc (p q : ℕ) :
    swap (0 : Fin (p+q+1)) ⟨p,by omega⟩ * finRotate (p+q+1) =
      finSumFinEquiv.permCongr (Equiv.Perm.sumCongr (finRotate p) (finRotate (q+1))) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (m := p) (n := q+1) (fun j => ?_) (fun j => ?_) i
  · change _ = finSumFinEquiv ((Equiv.Perm.sumCongr (finRotate p) (finRotate (q+1))) (finSumFinEquiv.symm _))
    simp only [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
      Equiv.Perm.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left, mul_apply]
    simp only [swap_apply_def]
    split_ifs <;> apply Fin.ext <;>
      simp only [Fin.ext_iff, finRotate_val, Fin.coe_castAdd, Fin.val_zero, Fin.val_mk] at * <;>
      split_ifs at * <;> omega
  · change _ = finSumFinEquiv ((Equiv.Perm.sumCongr (finRotate p) (finRotate (q+1))) (finSumFinEquiv.symm _))
    simp only [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd,
      Equiv.Perm.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right, mul_apply]
    simp only [swap_apply_def]
    split_ifs <;> apply Fin.ext <;>
      simp only [Fin.ext_iff, finRotate_val, Fin.coe_natAdd, Fin.val_zero, Fin.val_mk] at * <;>
      split_ifs at * <;> omega

#print axioms finRotate_split_arc
end ProjectionChannels.TensorHaar
