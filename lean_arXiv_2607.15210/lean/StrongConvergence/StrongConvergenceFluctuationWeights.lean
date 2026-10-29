import StrongConvergence.StrongConvergenceFluctuationMoments

/-! Weighted fourth-order Haar contractions, expressed using scalar power sums. -/

open Matrix MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {K : Type*} [Fintype K] [DecidableEq K]

def coefficientPowerSum (a : K → ℝ) (r : ℕ) : ℂ := ∑ i, (a i : ℂ)^r

lemma coefficientPowerSum_eq_coe_sum (a : K → ℝ) (r : ℕ) :
    coefficientPowerSum a r = ((∑ i, (a i)^r : ℝ) : ℂ) := by
  simp [coefficientPowerSum]

/-- Reordering tensor positions preserves their weighted cycle contraction. -/
lemma weightedCycleMoment_conjugate {m : ℕ} (a : K → ℝ)
    (σ τ : Equiv.Perm (Fin m)) :
    weightedCycleMoment a (τ.symm * σ * τ) = weightedCycleMoment a σ := by
  let e : (Fin m → K) ≃ (Fin m → K) :=
    { toFun := fun b l => b (τ l)
      invFun := fun b l => b (τ.symm l)
      left_inv := by intro b; funext l; simp
      right_inv := by intro b; funext l; simp }
  unfold weightedCycleMoment
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  have hprod : (∏ l, (a (e b l) : ℂ)) = ∏ l, (a (b l) : ℂ) := by
    exact Equiv.prod_comp τ (fun l => (a (b l) : ℂ))
  have hfixed :
      (e b = fun l => e b ((τ.symm * σ * τ) l)) ↔
        (b = fun l => b (σ l)) := by
    constructor
    · intro h
      funext l
      have hh := congrFun h (τ.symm l)
      simpa [e, Equiv.Perm.mul_apply] using hh
    · intro h
      funext l
      have hh := congrFun h (τ l)
      simpa [e, Equiv.Perm.mul_apply] using hh
  simp only [hprod, hfixed]

lemma weightedCycleMoment_identity (a : K → ℝ) (m : ℕ) :
    weightedCycleMoment a (1 : Equiv.Perm (Fin m)) = coefficientPowerSum a 1 ^ m := by
  simp only [weightedCycleMoment, Equiv.Perm.one_apply, ite_true, mul_one]
  calc
    _ = ∏ _ : Fin m, ∑ i : K, (a i : ℂ) :=
      (Fintype.prod_sum (fun _ : Fin m => fun i : K => (a i : ℂ))).symm
    _ = _ := by simp [coefficientPowerSum]

lemma sum_four_tuple (f : (Fin 4 → K) → ℂ) :
    (∑ b, f b) = ∑ i, ∑ j, ∑ k, ∑ l, f ![i,j,k,l] := by
  simp_rw [sum_fin_cons]
  simp only [Fintype.sum_unique]
  rfl

lemma weightedCycleMoment_swap01 (a : K → ℝ) :
    weightedCycleMoment a (Equiv.swap (0 : Fin 4) 1) =
      coefficientPowerSum a 1 ^ 2 * coefficientPowerSum a 2 := by
  rw [weightedCycleMoment, sum_four_tuple]
  simp [Fin.prod_univ_succ, funext_iff, Fin.forall_fin_succ,
    Equiv.swap_apply_def, mul_ite, mul_one, mul_zero,
    and_assoc, and_left_comm, and_comm, eq_comm,
    coefficientPowerSum, pow_two]
  simp_rw [← Finset.mul_sum]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  ring

lemma weightedCycleMoment_twoTwoCycle (a : K → ℝ) :
    weightedCycleMoment a twoTwoCycle = coefficientPowerSum a 2 ^ 2 := by
  rw [weightedCycleMoment, sum_four_tuple]
  simp [Fin.prod_univ_succ, funext_iff, Fin.forall_fin_succ,
    twoTwoCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    mul_ite, mul_one, mul_zero, and_assoc, and_left_comm, and_comm, eq_comm,
    coefficientPowerSum, pow_two]
  simp only [ite_and]
  simp
  simp_rw [← Finset.mul_sum]
  simp_rw [← mul_assoc, ← Finset.sum_mul]

lemma weightedCycleMoment_threeCycle (a : K → ℝ) :
    weightedCycleMoment a (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) =
      coefficientPowerSum a 1 * coefficientPowerSum a 3 := by
  rw [weightedCycleMoment, sum_four_tuple]
  simp [Fin.prod_univ_succ, funext_iff, Fin.forall_fin_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def, mul_ite, mul_one, mul_zero,
    and_assoc, and_left_comm, and_comm, eq_comm, coefficientPowerSum, pow_succ]
  simp only [ite_and]
  simp
  simp_rw [← Finset.mul_sum]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  ring

lemma weightedCycleMoment_fourCycle (a : K → ℝ) :
    weightedCycleMoment a (finRotate 4) = coefficientPowerSum a 4 := by
  rw [weightedCycleMoment, sum_four_tuple]
  simp [Fin.prod_univ_succ, funext_iff, Fin.forall_fin_succ,
    finRotate_succ_apply, mul_ite, mul_one, mul_zero,
    and_assoc, and_left_comm, and_comm, eq_comm, coefficientPowerSum, pow_succ]
  simp only [ite_and]
  simp
  apply Finset.sum_congr rfl
  intro i _
  ring

end ProjectionChannels.TensorHaar
