import StrongConvergence.StrongConvergenceFreeMarked
import StrongConvergence.StrongConvergenceFreeArc
import StrongConvergence.StrongConvergenceMomentCumulantRecurrence

/-! The marked-cycle decomposition of geodesic permutation sums. -/
open Equiv Equiv.Perm
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.FreeMoments
open ProjectionChannels.TensorHaar
variable {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R]

local instance (priority := 2000) permutationFintype : Fintype (Perm α) :=
  @Equiv.instFintype α α (Classical.decEq α) (Classical.decEq α) inferInstance inferInstance
attribute [local instance 2000] absoluteIntervalFintype orbitClassesDecidableEq
local instance absoluteLEDecidable (σ ρ : Perm α) : Decidable (absoluteLE σ ρ) := Classical.propDecidable _

lemma orbitSize_mk_pos (σ : Perm α) (a : α) : 0 < orbitSize σ (Quotient.mk _ a) := by
  classical
  unfold orbitSize
  exact Fintype.card_pos_iff.mpr ⟨⟨a,rfl⟩⟩

lemma orbitSize_le (σ : Perm α) (q : OrbitClasses σ) : orbitSize σ q ≤ Fintype.card α := by
  classical
  exact Fintype.card_subtype_le _

/-- Weight of a permutation whose marked cycle has the specified size. -/
def markedTerm (f : ℕ → R) (σ : Perm α) (a : α) (r : ℕ) : R :=
  if orbitSize σ (Quotient.mk _ a) = r then markedCycleWeight f σ a else 0

@[simp] lemma markedTerm_zero (f : ℕ → R) (σ : Perm α) (a : α) :
    markedTerm f σ a 0 = 0 := by
  rw [markedTerm, if_neg (Nat.ne_of_gt (orbitSize_mk_pos σ a))]

lemma markedTerm_transport (f : ℕ → R) (e : α ≃ β) (σ : Perm α) (a : α) (r : ℕ) :
    markedTerm f (e.permCongr σ) (e a) r = markedTerm f σ a r := by
  unfold markedTerm
  have hsize : orbitSize (e.permCongr σ) (Quotient.mk _ (e a)) =
      orbitSize σ (Quotient.mk _ a) := orbitSize_transport e σ (Quotient.mk _ a)
  rw [hsize, markedCycleWeight_transport]

lemma markedTerm_sum_right (f : ℕ → R) (σ : Perm α) (τ : Perm β) (b : β) (r : ℕ) :
    markedTerm f (Perm.sumCongr σ τ) (Sum.inr b) r =
      cycleWeight f σ * markedTerm f τ b r := by
  unfold markedTerm
  have hsize : orbitSize (Perm.sumCongr σ τ) (Quotient.mk _ (Sum.inr b)) =
      orbitSize τ (Quotient.mk _ b) := orbitSize_sum_right σ τ (Quotient.mk _ b)
  rw [hsize, markedCycleWeight_sum_right]
  split_ifs <;> simp

lemma markedTerm_insert {n : ℕ} (f : ℕ → R) (σ : Perm (Fin n)) (p : Fin n) (r : ℕ) :
    markedTerm f (insertPermutation σ p) 0 (r+1) = markedTerm f σ p r := by
  simp only [markedTerm, orbitSize_insert_mark, Nat.add_right_cancel_iff,
    markedCycleWeight_insert]

lemma markedTerm_lift {n : ℕ} (f : ℕ → R) (σ : Perm (Fin n)) (r : ℕ) :
    markedTerm f (liftPermutation σ) 0 (r+1) = if r = 0 then cycleWeight f σ else 0 := by
  simp only [markedTerm, orbitSize_lift_zero, markedCycleWeight_lift]
  split_ifs with h₁ h₂ h₂ <;> try rfl
  · omega
  · omega

/-- The marked moment sum on a geodesic interval. -/
def markedInterval (f : ℕ → R) (ρ : Perm α) (a : α) (r : ℕ) : R := by
  classical
  exact ∑ σ : {σ : Perm α // absoluteLE σ ρ}, markedTerm f σ.val a r

lemma markedInterval_eq_sum (f : ℕ → R) (ρ : Perm α) (a : α) (r : ℕ) :
    markedInterval f ρ a r = ∑ σ : Perm α, if absoluteLE σ ρ then markedTerm f σ a r else 0 := by
  classical
  unfold markedInterval
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun σ => absoluteLE σ ρ) {σ | absoluteLE σ ρ}
    (by intro σ; simp) (fun σ => markedTerm f σ a r)).symm

lemma weightedInterval_eq_sum (f : ℕ → R) (ρ : Perm α) :
    weightedInterval f ρ = ∑ σ : Perm α, if absoluteLE σ ρ then cycleWeight f σ else 0 := by
  classical
  unfold weightedInterval
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype {σ | absoluteLE σ ρ} (by intro σ; simp) _).symm

lemma markedInterval_transport (f : ℕ → R) (e : α ≃ β) (ρ : Perm α) (a : α) (r : ℕ) :
    markedInterval f (e.permCongr ρ) (e a) r = markedInterval f ρ a r := by
  classical
  unfold markedInterval
  rw [← Equiv.sum_comp (absoluteIntervalTransport e ρ)]
  apply Finset.sum_congr rfl
  intro σ _
  change markedTerm f (e.permCongr σ.val) (e a) r = markedTerm f σ.val a r
  exact markedTerm_transport f e σ.val a r

lemma markedInterval_sum_right (f : ℕ → R) (ρ₁ : Perm α) (ρ₂ : Perm β) (b : β) (r : ℕ) :
    markedInterval f (Perm.sumCongr ρ₁ ρ₂) (Sum.inr b) r =
      weightedInterval f ρ₁ * markedInterval f ρ₂ b r := by
  classical
  have h := Fintype.sum_equiv (absoluteIntervalSumEquiv ρ₁ ρ₂).symm
    (fun p => cycleWeight f p.1.val * markedTerm f p.2.val b r)
    (fun σ => markedTerm f σ.val (Sum.inr b) r) (by
      intro p
      dsimp only
      rw [absoluteIntervalSumEquiv_symm_val, markedTerm_sum_right])
  rw [Fintype.sum_prod_type] at h
  dsimp only at h
  rw [← Finset.sum_mul_sum] at h
  exact h.symm

/-- Delete zero, separating its fixed-point and insertion contributions. -/
theorem markedInterval_decompose (f : ℕ → R) (n r : ℕ) :
    markedInterval f (finRotate (n+2)) 0 (r+1) =
      (if r = 0 then weightedInterval f (finRotate (n+1)) else 0) +
      ∑ p : Fin (n+1), markedInterval f (swap 0 p * finRotate (n+1)) p r := by
  classical
  rw [markedInterval_eq_sum, ← Equiv.sum_comp decomposeFin.symm, Fintype.sum_prod_type,
    Fin.sum_univ_succ]
  congr 1
  · simp_rw [absoluteLE_fin, decomposeFin_absoluteLE_finRotate_zero]
    change (∑ σ : Perm (Fin (n+1)), if PermutationAbsoluteLE σ (finRotate (n+1)) then
      markedTerm f (liftPermutation σ) 0 (r+1) else 0) = _
    simp_rw [markedTerm_lift]
    split_ifs with hr
    · simpa only [if_pos hr, weightedInterval_eq_sum, absoluteLE_fin]
    · simp [hr]
  · apply Finset.sum_congr rfl
    intro p _
    simp_rw [absoluteLE_fin, decomposeFin_absoluteLE_finRotate_succ]
    change (∑ σ : Perm (Fin (n+1)), if PermutationAbsoluteLE σ (swap 0 p * finRotate (n+1)) then
      markedTerm f (insertPermutation σ p) 0 (r+1) else 0) = _
    simp_rw [markedTerm_insert]
    simp only [markedInterval_eq_sum, absoluteLE_fin]


/-- Moment polynomial defined directly by the full-cycle geodesic interval. -/
def freeMoment (f : ℕ → R) (n : ℕ) : R := weightedInterval f (finRotate n)

/-- Marked cycle sums, including the empty-permutation base value. -/
def freeMarked (f : ℕ → R) : ℕ → ℕ → R
  | 0, r => if r = 0 then 1 else 0
  | n+1, r => markedInterval f (finRotate (n+1)) 0 r

@[simp] lemma freeMarked_zero (f : ℕ → R) (r : ℕ) :
    freeMarked f 0 r = if r = 0 then 1 else 0 := rfl

@[simp] lemma freeMarked_succ_zero (f : ℕ → R) (n : ℕ) : freeMarked f (n+1) 0 = 0 := by
  simp [freeMarked, markedInterval, markedTerm_zero]

lemma cycleWeight_empty (f : ℕ → R) (σ : Perm (Fin 0)) : cycleWeight f σ = 1 := by
  haveI : IsEmpty (OrbitClasses σ) := inferInstance
  exact Fintype.prod_empty _

@[simp] lemma freeMoment_zero (f : ℕ → R) : freeMoment f 0 = 1 := by
  classical
  rw [freeMoment, weightedInterval_eq_sum]
  have hσ (σ : Perm (Fin 0)) : absoluteLE σ (finRotate 0) := by
    rw [Subsingleton.elim σ (finRotate 0), absoluteLE_fin]
  simp only [if_pos (hσ _), cycleWeight_empty]
  simp

lemma cycleWeight_eq_sum_markedTerm (f : ℕ → R) (σ : Perm α) (a : α) :
    cycleWeight f σ = ∑ r ∈ Finset.range (Fintype.card α+1), f r * markedTerm f σ a r := by
  classical
  simp_rw [markedTerm, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le (orbitSize_le σ _)))]
  rw [cycleWeight_eq_marked_mul f σ a, mul_comm]

lemma freeMoment_eq_sum_marked (f : ℕ → R) (n : ℕ) :
    freeMoment f (n+1) = ∑ r ∈ Finset.range (n+2), f r * freeMarked f (n+1) r := by
  classical
  unfold freeMoment weightedInterval
  simp_rw [cycleWeight_eq_sum_markedTerm f _ (0 : Fin (n+1)), Fintype.card_fin]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [freeMarked, markedInterval, Finset.mul_sum]


lemma markedInterval_split_arc (f : ℕ → R) (p q r : ℕ) :
    markedInterval f (swap (0 : Fin (p+q+1)) ⟨p,by omega⟩ * finRotate (p+q+1))
      ⟨p,by omega⟩ r = freeMoment f p * freeMarked f (q+1) r := by
  rw [finRotate_split_arc]
  change markedInterval f _ (finSumFinEquiv (Sum.inr (0 : Fin (q+1)))) r = _
  rw [markedInterval_transport, markedInterval_sum_right]
  rfl

lemma finCongr_arc {n m : ℕ} (h : n+1 = m+1) (p : Fin (n+1)) :
    (finCongr h).permCongr (swap 0 p * finRotate (n+1)) =
      swap 0 ((finCongr h) p) * finRotate (m+1) := by
  have hnm : n = m := by omega
  subst m
  rfl

lemma markedInterval_split_at (f : ℕ → R) (n r : ℕ) (p : Fin (n+1)) :
    markedInterval f (swap 0 p * finRotate (n+1)) p r =
      freeMoment f p.val * freeMarked f (n+1-p.val) r := by
  rcases p with ⟨p,hp⟩
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ hp)
  have hd : p+q+1-p = q+1 := by omega
  simpa only [Fin.val_mk, hd] using markedInterval_split_arc f p q r

lemma freeMarked_one (f : ℕ → R) (r : ℕ) :
    freeMarked f 1 (r+1) = if r=0 then 1 else 0 := by
  classical
  change markedInterval f (finRotate 1) 0 (r+1) = _
  rw [markedInterval_eq_sum]
  have hσ (σ : Perm (Fin 1)) : σ = liftPermutation (1 : Perm (Fin 0)) := Subsingleton.elim _ _
  have hle (σ : Perm (Fin 1)) : absoluteLE σ (finRotate 1) := by
    rw [Subsingleton.elim σ (finRotate 1), absoluteLE_fin]
  simp only [if_pos (hle _)]
  simp_rw [hσ, markedTerm_lift, cycleWeight_empty]
  simp

/-- Peel recursion for the cycle containing zero. -/
theorem freeMarked_recursion (f : ℕ → R) (n r : ℕ) :
    freeMarked f (n+1) (r+1) = (if r=0 then freeMoment f n else 0) +
      ∑ p ∈ Finset.range n, freeMoment f p * freeMarked f (n-p) r := by
  cases n with
  | zero => simp [freeMarked_one]
  | succ n =>
    change markedInterval f (finRotate (n+2)) 0 (r+1) = _
    rw [markedInterval_decompose]
    simp_rw [markedInterval_split_at]
    rw [← Fin.sum_univ_eq_sum_range]
    rfl


/-- The free moment--cumulant identity for the concrete permutation interval sum. -/
theorem freeMoment_formal_identity (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    FreeCumulant.formalSubst (PowerSeries.X * PowerSeries.mk (freeMoment f)) (by simp)
      (PowerSeries.mk f) = PowerSeries.mk (freeMoment f) - 1 :=
  MomentCumulantRecurrence.formalSubst_of_split_recurrence f (freeMoment f) (freeMarked f)
    hf0 (freeMoment_zero f) (freeMarked_zero f) (freeMarked_succ_zero f)
    (freeMarked_recursion f) (freeMoment_eq_sum_marked f)

#print axioms freeMarked_recursion
#print axioms freeMoment_formal_identity
end ProjectionChannels.FreeMoments
