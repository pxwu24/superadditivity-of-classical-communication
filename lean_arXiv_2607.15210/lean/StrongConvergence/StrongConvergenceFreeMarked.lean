import StrongConvergence.StrongConvergenceFreeMoments

/-! Set-level cycle insertion needed by the marked moment recurrence. -/
open Equiv Equiv.Perm
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {n : ℕ}
def insertPermutation (σ : Perm (Fin n)) (p : Fin n) : Perm (Fin (n+1)) :=
  decomposeFin.symm (p.succ,σ)

@[simp] lemma insertPermutation_zero (σ : Perm (Fin n)) (p : Fin n) :
    insertPermutation σ p 0 = p.succ := by simp [insertPermutation]

lemma insertPermutation_succ (σ : Perm (Fin n)) (p i : Fin n) :
    insertPermutation σ p i.succ = if σ i = p then 0 else (σ i).succ := by
  simp only [insertPermutation, decomposeFin_symm_apply_succ]
  by_cases h : σ i = p
  · simp [h]
  · rw [if_neg h, swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by simpa using h)]

lemma insertFixed_restrict (σ : Perm (Fin n)) (p : Fin n)
    (v : cycleFixedSpace (insertPermutation σ p)) :
    (fun i : Fin n => v.val i.succ) ∈ cycleFixedSpace σ := by
  funext i
  have hv := congrFun v.property i.succ
  change v.val i.succ = v.val (insertPermutation σ p i.succ) at hv
  rw [insertPermutation_succ] at hv
  split_ifs at hv with h
  · rw [h]
    have hz := congrFun v.property 0
    simpa using hv.trans hz
  · exact hv

lemma insertFixed_extend (σ : Perm (Fin n)) (p : Fin n)
    (v : cycleFixedSpace σ) :
    Fin.cases (v.val p) v.val ∈ cycleFixedSpace (insertPermutation σ p) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · change v.val i = Fin.cases (v.val p) v.val (insertPermutation σ p i.succ)
    rw [insertPermutation_succ]
    split_ifs with h
    · simpa [h] using congrFun v.property i
    · exact congrFun v.property i

lemma sameCycle_insert_succ (σ : Perm (Fin n)) (p a b : Fin n) :
    (insertPermutation σ p).SameCycle a.succ b.succ ↔ σ.SameCycle a b := by
  constructor
  · intro h
    apply sameCycle_of_fixed_vectors
    intro v hv
    exact cycleFixedSpace_constant_on_cycle (insertPermutation σ p)
      ⟨Fin.cases (v p) v, insertFixed_extend σ p ⟨v,hv⟩⟩
      ((cycleRelation_iff_sameCycle _ _ _).mpr h)
  · intro h
    apply sameCycle_of_fixed_vectors
    intro v hv
    exact cycleFixedSpace_constant_on_cycle σ
      ⟨(fun i => v i.succ),insertFixed_restrict σ p ⟨v,hv⟩⟩
      ((cycleRelation_iff_sameCycle _ _ _).mpr h)

lemma sameCycle_insert_zero (σ : Perm (Fin n)) (p : Fin n) :
    (insertPermutation σ p).SameCycle 0 p.succ := by
  simpa using (SameCycle.refl (insertPermutation σ p) 0).apply_right

end ProjectionChannels.TensorHaar

namespace ProjectionChannels.FreeMoments
open ProjectionChannels.TensorHaar

variable {n : ℕ}
local instance orbitDecidableEq (σ : Perm (Fin n)) : DecidableEq (OrbitClasses σ) := Classical.decEq _
def insertOrbitMap (σ : Perm (Fin n)) (p : Fin n) :
    OrbitClasses σ → OrbitClasses (insertPermutation σ p) :=
  Quotient.map Fin.succ (fun _ _ h => (sameCycle_insert_succ σ p _ _).mpr h)

@[simp] lemma insertOrbitMap_mk (σ : Perm (Fin n)) (p a : Fin n) :
    insertOrbitMap σ p (Quotient.mk _ a) = Quotient.mk _ a.succ := rfl

lemma insertOrbitMap_bijective (σ : Perm (Fin n)) (p : Fin n) :
    Function.Bijective (insertOrbitMap σ p) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        intro h
        exact Quotient.sound ((sameCycle_insert_succ σ p a b).mp (Quotient.exact h))
  · intro q
    induction q using Quotient.inductionOn with | h a =>
      refine Fin.cases ?_ (fun a => ?_) a
      · exact ⟨Quotient.mk _ p, Quotient.sound (sameCycle_insert_zero σ p).symm⟩
      · exact ⟨Quotient.mk _ a,rfl⟩

def insertOrbitEquiv (σ : Perm (Fin n)) (p : Fin n) :
    OrbitClasses σ ≃ OrbitClasses (insertPermutation σ p) :=
  Equiv.ofBijective (insertOrbitMap σ p) (insertOrbitMap_bijective σ p)

@[simp] lemma insertOrbitEquiv_mk (σ : Perm (Fin n)) (p a : Fin n) :
    insertOrbitEquiv σ p (Quotient.mk _ a) = Quotient.mk _ a.succ := rfl

lemma insertOrbitEquiv_at_mark (σ : Perm (Fin n)) (p : Fin n) :
    insertOrbitEquiv σ p (Quotient.mk _ p) = Quotient.mk _ 0 :=
  Quotient.sound (sameCycle_insert_zero σ p).symm

lemma card_subtype_fin_succ (P : Fin (n+1) → Prop) [DecidablePred P] :
    Fintype.card {i // P i} = (if P 0 then 1 else 0) + Fintype.card {i : Fin n // P i.succ} := by
  rw [Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_succ, Fintype.card_subtype,
    Finset.card_filter]

lemma orbitSize_insert (σ : Perm (Fin n)) (p : Fin n) (q : OrbitClasses σ) :
    orbitSize (insertPermutation σ p) (insertOrbitEquiv σ p q) =
      orbitSize σ q + if q = Quotient.mk _ p then 1 else 0 := by
  classical
  have h0 : (Quotient.mk (SameCycle.setoid (insertPermutation σ p)) 0 =
      insertOrbitEquiv σ p q) ↔ q = Quotient.mk _ p := by
    rw [← insertOrbitEquiv_at_mark]
    exact (insertOrbitEquiv σ p).injective.eq_iff.trans eq_comm
  have hs (a : Fin n) : (Quotient.mk (SameCycle.setoid (insertPermutation σ p)) a.succ =
      insertOrbitEquiv σ p q) ↔ Quotient.mk _ a = q := by
    rw [← insertOrbitEquiv_mk]
    exact (insertOrbitEquiv σ p).injective.eq_iff
  unfold orbitSize
  rw [card_subtype_fin_succ]
  rw [if_congr h0 rfl rfl]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hs)]
  exact Nat.add_comm _ _


variable {α β R : Type*} [Fintype α] [Fintype β] [CommMonoid R]

/-- Cycle weight with the cycle containing the marked point omitted. -/
def markedCycleWeight (f : ℕ → R) (σ : Perm α) (a : α) : R := by
  classical
  exact ∏ q : OrbitClasses σ, if q = Quotient.mk _ a then 1 else f (orbitSize σ q)

lemma markedCycleWeight_equiv (f : ℕ → R) (σ : Perm α) (τ : Perm β) (a : α) (b : β)
    (e : OrbitClasses σ ≃ OrbitClasses τ) (he : e (Quotient.mk _ a) = Quotient.mk _ b)
    (hs : ∀ q, q ≠ Quotient.mk _ a → orbitSize τ (e q) = orbitSize σ q) :
    markedCycleWeight f τ b = markedCycleWeight f σ a := by
  classical
  symm
  apply Fintype.prod_equiv e
  intro q
  have hq : e q = Quotient.mk _ b ↔ q = Quotient.mk _ a := by
    rw [← he, e.injective.eq_iff]
  rw [if_congr hq rfl rfl]
  split_ifs with h
  · rfl
  · rw [hs q h]

lemma markedCycleWeight_insert (f : ℕ → R) (σ : Perm (Fin n)) (p : Fin n) :
    markedCycleWeight f (insertPermutation σ p) 0 = markedCycleWeight f σ p := by
  apply markedCycleWeight_equiv f σ _ p 0 (insertOrbitEquiv σ p)
    (insertOrbitEquiv_at_mark σ p)
  intro q hq
  rw [orbitSize_insert, if_neg hq, Nat.add_zero]

lemma cycleWeight_eq_marked_mul (f : ℕ → R) (σ : Perm α) (a : α) :
    cycleWeight f σ = markedCycleWeight f σ a * f (orbitSize σ (Quotient.mk _ a)) := by
  classical
  unfold cycleWeight markedCycleWeight
  rw [← Fintype.prod_ite_eq' (Quotient.mk (SameCycle.setoid σ) a)
    (fun q => f (orbitSize σ q)), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _
  split_ifs <;> simp

lemma orbitSize_insert_mark (σ : Perm (Fin n)) (p : Fin n) :
    orbitSize (insertPermutation σ p) (Quotient.mk _ 0) =
      orbitSize σ (Quotient.mk _ p) + 1 := by
  rw [← insertOrbitEquiv_at_mark, orbitSize_insert, if_pos rfl]


lemma markedCycleWeight_transport (f : ℕ → R) (e : α ≃ β) (σ : Perm α) (a : α) :
    markedCycleWeight f (e.permCongr σ) (e a) = markedCycleWeight f σ a := by
  apply markedCycleWeight_equiv f σ _ a (e a) (orbitClassesTransport e σ) rfl
  intro q _
  exact orbitSize_transport e σ q

lemma markedCycleWeight_sum_right (f : ℕ → R) (σ : Perm α) (τ : Perm β) (b : β) :
    markedCycleWeight f (Perm.sumCongr σ τ) (Sum.inr b) =
      cycleWeight f σ * markedCycleWeight f τ b := by
  classical
  have h := Fintype.prod_equiv (orbitClassesSumEquiv σ τ).symm
    (Sum.elim (fun q => f (orbitSize σ q))
      (fun q => if q = Quotient.mk _ b then 1 else f (orbitSize τ q)))
    (fun q => if q = Quotient.mk _ (Sum.inr b) then 1 else
      f (orbitSize (Perm.sumCongr σ τ) q)) (by
      intro q
      have hm : (Quotient.mk (SameCycle.setoid (Perm.sumCongr σ τ)) (Sum.inr b)) =
          (orbitClassesSumEquiv σ τ).symm (Sum.inr (Quotient.mk _ b)) := rfl
      cases q with
      | inl q =>
        simp only [Sum.elim_inl, hm, (orbitClassesSumEquiv σ τ).symm.injective.eq_iff, Sum.inl_ne_inr,
          if_false, orbitSize_sum_left]
      | inr q =>
        simp only [Sum.elim_inr, hm, (orbitClassesSumEquiv σ τ).symm.injective.eq_iff, Sum.inr.injEq,
          orbitSize_sum_right])
  rw [Fintype.prod_sum_type] at h
  exact h.symm

lemma markedCycleWeight_sum_left (f : ℕ → R) (σ : Perm α) (τ : Perm β) (a : α) :
    markedCycleWeight f (Perm.sumCongr σ τ) (Sum.inl a) =
      markedCycleWeight f σ a * cycleWeight f τ := by
  classical
  have h := Fintype.prod_equiv (orbitClassesSumEquiv σ τ).symm
    (Sum.elim (fun q => if q = Quotient.mk _ a then 1 else f (orbitSize σ q))
      (fun q => f (orbitSize τ q)))
    (fun q => if q = Quotient.mk _ (Sum.inl a) then 1 else
      f (orbitSize (Perm.sumCongr σ τ) q)) (by
      intro q
      have hm : (Quotient.mk (SameCycle.setoid (Perm.sumCongr σ τ)) (Sum.inl a)) =
          (orbitClassesSumEquiv σ τ).symm (Sum.inl (Quotient.mk _ a)) := rfl
      cases q with
      | inl q =>
        simp only [Sum.elim_inl, hm, (orbitClassesSumEquiv σ τ).symm.injective.eq_iff, Sum.inl.injEq,
          orbitSize_sum_left]
      | inr q =>
        simp only [Sum.elim_inr, hm, (orbitClassesSumEquiv σ τ).symm.injective.eq_iff, Sum.inr_ne_inl,
          if_false, orbitSize_sum_right])
  rw [Fintype.prod_sum_type] at h
  exact h.symm

/-- Identify a new first point with a singleton direct-sum block. -/
def zeroSumEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv x := by cases x <;> rfl
  right_inv x := by refine Fin.cases ?_ (fun _ => ?_) x <;> rfl

lemma liftPermutation_eq_transport (σ : Perm (Fin n)) :
    liftPermutation σ = (zeroSumEquiv n).permCongr (Perm.sumCongr 1 σ) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

lemma markedCycleWeight_subsingleton [Subsingleton α] (f : ℕ → R) (σ : Perm α) (a : α) :
    markedCycleWeight f σ a = 1 := by
  classical
  apply Finset.prod_eq_one
  intro q _
  induction q using Quotient.inductionOn with | h b =>
    have h : b = a := Subsingleton.elim _ _
    simp [h]

lemma markedCycleWeight_lift (f : ℕ → R) (σ : Perm (Fin n)) :
    markedCycleWeight f (liftPermutation σ) 0 = cycleWeight f σ := by
  rw [liftPermutation_eq_transport]
  change markedCycleWeight f _ ((zeroSumEquiv n) (Sum.inl ())) = _
  rw [markedCycleWeight_transport, markedCycleWeight_sum_left,
    markedCycleWeight_subsingleton, one_mul]

lemma orbitSize_lift_zero (σ : Perm (Fin n)) :
    orbitSize (liftPermutation σ) (Quotient.mk _ 0) = 1 := by
  classical
  rw [liftPermutation_eq_transport]
  change orbitSize _ ((orbitClassesTransport (zeroSumEquiv n) (Perm.sumCongr 1 σ))
    (Quotient.mk _ (Sum.inl ()))) = _
  rw [orbitSize_transport]
  change orbitSize _ ((orbitClassesSumEquiv (1 : Perm Unit) σ).symm
    (Sum.inl (Quotient.mk _ ()))) = _
  rw [orbitSize_sum_left, orbitSize_mk]
  simp

#print axioms markedCycleWeight_insert
#print axioms markedCycleWeight_lift
#print axioms markedCycleWeight_sum_right
end ProjectionChannels.FreeMoments
