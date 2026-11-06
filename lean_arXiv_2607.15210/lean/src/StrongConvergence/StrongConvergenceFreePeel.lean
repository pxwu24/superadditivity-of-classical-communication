import StrongConvergence.StrongConvergenceFreeOrder

/-! Fixed-point insertion and the geodesic interval decomposition at zero. -/
open Equiv Equiv.Perm
noncomputable section
namespace ProjectionChannels.TensorHaar

/-- Extend a permutation by a new initial fixed point. -/
def liftPermutation {n : ℕ} (σ : Perm (Fin n)) : Perm (Fin (n+1)) :=
  decomposeFin.symm (0,σ)

@[simp] lemma liftPermutation_zero {n : ℕ} (σ : Perm (Fin n)) :
    liftPermutation σ 0 = 0 := by simp [liftPermutation]

@[simp] lemma liftPermutation_succ {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) :
    liftPermutation σ i.succ = (σ i).succ := by simp [liftPermutation]

@[simp] lemma liftPermutation_mul {n : ℕ} (σ τ : Perm (Fin n)) :
    liftPermutation (σ * τ) = liftPermutation σ * liftPermutation τ := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [Equiv.Perm.mul_apply]

@[simp] lemma liftPermutation_one (n : ℕ) :
    liftPermutation (1 : Perm (Fin n)) = 1 := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

@[simp] lemma liftPermutation_symm {n : ℕ} (σ : Perm (Fin n)) :
    liftPermutation σ.symm = (liftPermutation σ).symm := by
  apply mul_right_cancel (b := liftPermutation σ)
  rw [← liftPermutation_mul]
  simp

/-- Fixed vectors split into the new scalar coordinate and the original fixed space. -/
def cycleFixedSpaceLiftEquiv {n : ℕ} (σ : Perm (Fin n)) :
    cycleFixedSpace (liftPermutation σ) ≃ₗ[ℝ] (ℝ × cycleFixedSpace σ) where
  toFun v := (v.val 0, ⟨fun i => v.val i.succ, by
    funext i
    have h := congrFun v.property i.succ
    simpa using h⟩)
  invFun w := ⟨Fin.cases w.1 w.2.val, by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simpa using congrFun w.2.property i⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  right_inv w := by
    cases w
    rfl
  map_add' v w := rfl
  map_smul' c v := rfl

@[simp] lemma cycleCount_liftPermutation {n : ℕ} (σ : Perm (Fin n)) :
    cycleCount (liftPermutation σ) = cycleCount σ + 1 := by
  rw [← finrank_cycleFixedSpace, (cycleFixedSpaceLiftEquiv σ).finrank_eq]
  simp [finrank_cycleFixedSpace, Nat.add_comm]

@[simp] lemma permutationLength_liftPermutation {n : ℕ} (σ : Perm (Fin n)) :
    permutationLength (liftPermutation σ) = permutationLength σ := by
  simp only [permutationLength, cycleCount_liftPermutation]
  omega

@[simp] theorem absoluteLE_liftPermutation_iff {n : ℕ} (σ τ : Perm (Fin n)) :
    PermutationAbsoluteLE (liftPermutation σ) (liftPermutation τ) ↔
      PermutationAbsoluteLE σ τ := by
  unfold PermutationAbsoluteLE
  have hres : liftPermutation τ * (liftPermutation σ).symm =
      liftPermutation (τ * σ.symm) := by rw [liftPermutation_mul, liftPermutation_symm]
  rw [hres]
  simp only [permutationLength_liftPermutation]

lemma decomposeFin_eq_swap_lift {n : ℕ} (j : Fin (n+1)) (σ : Perm (Fin n)) :
    decomposeFin.symm (j,σ) = swap 0 j * liftPermutation σ := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [Equiv.Perm.mul_apply]

lemma liftPermutation_swap {n : ℕ} (i j : Fin n) :
    liftPermutation (swap i j) = swap i.succ j.succ := by
  apply Equiv.ext
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [liftPermutation_zero]
    exact (swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm).symm
  · simp only [liftPermutation_succ, swap_apply_def, Fin.succ_inj]
    split_ifs <;> rfl

lemma finRotate_eq_swap_lift (n : ℕ) :
    finRotate (n+1) = swap 0 1 * liftPermutation (finRotate n) := by
  rw [finRotate_succ_eq_decomposeFin, decomposeFin_eq_swap_lift]

lemma swap_zero_one_finRotate (n : ℕ) :
    swap 0 1 * finRotate (n+1) = liftPermutation (finRotate n) := by
  rw [finRotate_eq_swap_lift]
  simp [← mul_assoc]

lemma sameCycle_finRotate (n : ℕ) (i j : Fin (n+1)) :
    (finRotate (n+1)).SameCycle i j := by
  apply sameCycle_of_fixed_vectors
  intro v hv
  exact (cycleFixedSpace_finRotate_constant n ⟨v,hv⟩ i).trans
    (cycleFixedSpace_finRotate_constant n ⟨v,hv⟩ j).symm

lemma swap_finRotate_arc (n : ℕ) (p : Fin (n+1)) (hp : p ≠ 0) :
    swap 0 1 * (swap 0 p.succ * finRotate (n+2)) =
      liftPermutation (swap 0 p * finRotate (n+1)) := by
  have hj0 : p.succ ≠ (0 : Fin (n+2)) := Fin.succ_ne_zero p
  have hj1 : p.succ ≠ (1 : Fin (n+2)) := by
    change p.succ ≠ (0 : Fin (n+1)).succ
    exact fun h => hp (Fin.succ_injective (n+1) h)
  calc
    _ = (swap 0 1 * swap 0 p.succ * swap 0 1) *
        liftPermutation (finRotate (n+1)) := by
      rw [finRotate_eq_swap_lift (n+1)]
      group
    _ = swap 1 p.succ * liftPermutation (finRotate (n+1)) := by
      rw [mul_swap_eq_swap_mul (swap 0 1) 0 p.succ]
      simp only [swap_apply_left, swap_apply_of_ne_of_ne hj0 hj1, mul_assoc,
        swap_mul_self, mul_one]
    _ = liftPermutation (swap 0 p) * liftPermutation (finRotate (n+1)) := by
      rw [liftPermutation_swap]
      simp
    _ = _ := (liftPermutation_mul _ _).symm

/-- A fixed point at zero removes the first point of the full cycle. -/
theorem decomposeFin_absoluteLE_finRotate_zero (n : ℕ) (σ : Perm (Fin n)) :
    PermutationAbsoluteLE (decomposeFin.symm (0,σ)) (finRotate (n+1)) ↔
      PermutationAbsoluteLE σ (finRotate n) := by
  cases n with
  | zero =>
    constructor <;> intro _
    · have he : σ = finRotate 0 := Subsingleton.elim _ _
      rw [he]
    · have he : decomposeFin.symm (0,σ) = finRotate 1 := Subsingleton.elim _ _
      rw [he]
  | succ n =>
    change PermutationAbsoluteLE (liftPermutation σ) (finRotate (n+2)) ↔ _
    rw [permutationAbsoluteLE_fixed_point (liftPermutation σ) (finRotate (n+2)) 0
      (liftPermutation_zero σ) (by simp)]
    rw [finRotate_apply_zero, swap_zero_one_finRotate, absoluteLE_liftPermutation_iff]

/-- Inserting zero into the cycle through `p` yields the smaller arc interval. -/
theorem decomposeFin_absoluteLE_finRotate_succ (n : ℕ)
    (p : Fin (n+1)) (σ : Perm (Fin (n+1))) :
    PermutationAbsoluteLE (decomposeFin.symm (p.succ,σ)) (finRotate (n+2)) ↔
      PermutationAbsoluteLE σ (swap 0 p * finRotate (n+1)) := by
  let τ : Perm (Fin (n+2)) := decomposeFin.symm (p.succ,σ)
  have h0p : (0 : Fin (n+2)) ≠ p.succ := (Fin.succ_ne_zero p).symm
  have hsγ : PermutationAbsoluteLE (swap 0 p.succ) (finRotate (n+2)) :=
    (swap_absoluteLE_iff_sameCycle h0p _).mpr (sameCycle_finRotate (n+1) 0 p.succ)
  have hsτ : PermutationAbsoluteLE (swap 0 p.succ) τ := by
    apply (swap_absoluteLE_iff_sameCycle h0p τ).mpr
    simpa only [τ, decomposeFin_symm_apply_zero] using (SameCycle.refl τ 0).apply_right
  have hpeel := swap_absoluteLE_peel hsγ τ
  have hcancel : swap 0 p.succ * τ = liftPermutation σ := by
    simp [τ, decomposeFin_eq_swap_lift, ← mul_assoc]
  rw [hcancel] at hpeel
  have hred : PermutationAbsoluteLE τ (finRotate (n+2)) ↔
      PermutationAbsoluteLE (liftPermutation σ) (swap 0 p.succ * finRotate (n+2)) := by
    simpa only [hsτ, true_and] using hpeel
  change PermutationAbsoluteLE τ (finRotate (n+2)) ↔ _
  rw [hred]
  by_cases hp : p = 0
  · subst p
    simp only [Fin.succ_zero_eq_one, swap_zero_one_finRotate,
      absoluteLE_liftPermutation_iff, swap_self]
    change _ ↔ PermutationAbsoluteLE σ (1 * finRotate (n+1))
    rw [one_mul]
  · have hδ : (swap 0 p.succ * finRotate (n+2)) 0 = 1 := by
      simp only [Equiv.Perm.mul_apply, finRotate_apply_zero]
      apply swap_apply_of_ne_of_ne
      · simp
      · change (0 : Fin (n+1)).succ ≠ p.succ
        exact fun h => hp (Fin.succ_injective (n+1) h).symm
    rw [permutationAbsoluteLE_fixed_point (liftPermutation σ)
      (swap 0 p.succ * finRotate (n+2)) 0 (liftPermutation_zero σ) (by rw [hδ]; simp)]
    rw [hδ, swap_finRotate_arc n p hp, absoluteLE_liftPermutation_iff]

#print axioms absoluteLE_liftPermutation_iff
#print axioms decomposeFin_absoluteLE_finRotate_zero
#print axioms decomposeFin_absoluteLE_finRotate_succ
end ProjectionChannels.TensorHaar
