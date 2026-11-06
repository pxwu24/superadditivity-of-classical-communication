import StrongConvergence.StrongConvergenceFreeMoments

/-! Full-cycle moment identities extend to all permutation intervals by the
verified product decomposition over cycles. -/
open Equiv Equiv.Perm Function
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.FreeMoments
open TensorHaar
universe u
variable {α : Type u} [Fintype α]

lemma orbitCount_eq_one_of_sameCycle (σ : Perm α) (a : α)
    (hσ : ∀ x y, σ.SameCycle x y) : orbitCount σ = 1 := by
  letI : Subsingleton (OrbitClasses σ) := ⟨fun q r => by
    induction q using Quotient.inductionOn with | h x =>
      induction r using Quotient.inductionOn with | h y => exact Quotient.sound (hσ x y)⟩
  have hc := Fintype.card_ofSubsingleton (Quotient.mk _ a : OrbitClasses σ)
  simpa only [orbitCount, ← Nat.card_eq_fintype_card] using hc

lemma weightedInterval_fullCycle_fin (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (σ : Perm (Fin n)) (hσ : ∀ x y, σ.SameCycle x y) :
    weightedInterval f σ = weightedInterval f (finRotate n) := by
  classical
  by_cases hn1 : n = 1
  · subst n
    rw [Subsingleton.elim σ (finRotate 1)]
  have hn2 : 2 ≤ n := by omega
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
  have hnf (x : Fin n) : σ x ≠ x := by
    intro hx
    obtain ⟨y, hy⟩ := exists_ne x
    obtain ⟨r, hr⟩ := hσ x y
    exact hy (hr.symm.trans (IsFixedPt.perm_zpow hx r))
  have hc : σ.IsCycle := ⟨⟨0, hn⟩, hnf _, fun y _ => hσ _ _⟩
  have hs : σ.support = Finset.univ := by ext x; simp [Perm.mem_support, hnf x]
  have hconj := hc.isConj (isCycle_finRotate_of_le hn2)
    (by rw [hs, support_finRotate_of_le hn2])
  obtain ⟨e, he⟩ := _root_.isConj_iff.mp hconj
  have heq : e.permCongr σ = finRotate n := by
    convert he using 1
  rw [← heq, weightedInterval_transport]

lemma weightedInterval_fullCycle (f : ℕ → ℝ) (σ : Perm α) (a : α)
    (hσ : ∀ x y, σ.SameCycle x y) :
    weightedInterval f σ = weightedInterval f (finRotate (Fintype.card α)) := by
  let e := Fintype.equivFin α
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  have hσ' : ∀ x y, (e.permCongr σ).SameCycle x y := by
    intro x y
    simpa only [e.apply_symm_apply] using
      (sameCycle_transport e σ (e.symm x) (e.symm y)).mpr (hσ _ _)
  rw [← weightedInterval_transport f e σ]
  exact weightedInterval_fullCycle_fin f hpos _ hσ'

lemma weightedInterval_empty (f : ℕ → ℝ) (σ : Perm α) (hα : Fintype.card α = 0) :
    weightedInterval f σ = 1 := by
  classical
  letI : IsEmpty α := Fintype.card_eq_zero_iff.mp hα
  letI : Unique {τ : Perm α // absoluteLE τ σ} :=
    uniqueOfSubsingleton ⟨σ, by simp [absoluteLE, absoluteLength, orbitCount]⟩
  simp [weightedInterval, cycleWeight]

/-- E4.1: once every nonempty full cycle has moment `s`, independent cycle
blocks give the rank moment `s^(number of cycles)` for every finite permutation. -/
theorem weightedInterval_eq_pow_of_fullCycle (f : ℕ → ℝ) (s : ℝ)
    (hf : ∀ n : ℕ, 0 < n → weightedInterval f (finRotate n) = s)
    (σ : Perm α) : weightedInterval f σ = s ^ orbitCount σ := by
  classical
  induction hcard : Fintype.card α using Nat.strong_induction_on generalizing α with
  | h n ih =>
    by_cases hn : n = 0
    · have hzero : Fintype.card α = 0 := hcard.trans hn
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hzero
      rw [weightedInterval_empty f σ hzero]
      simp [orbitCount]
    have hnonempty : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a⟩ := hnonempty
    by_cases hall : ∀ x y, σ.SameCycle x y
    · rw [weightedInterval_fullCycle f σ a hall, hf _ (by omega), orbitCount_eq_one_of_sameCycle σ a hall,
        pow_one]
    have hex : ∃ b, ¬σ.SameCycle b a := by
      by_contra h
      push_neg at h
      exact hall (fun x y => (h x).trans (h y).symm)
    obtain ⟨b, hb⟩ := hex
    let p : α → Prop := fun x => σ.SameCycle x a
    have hp : ∀ x, p x ↔ p (σ x) := fun x => sameCycle_apply_left.symm
    let σ₁ : Perm {x // p x} := σ.subtypePerm hp
    let σ₂ : Perm {x // ¬p x} := σ.subtypePerm (fun x => not_congr (hp x))
    let e := Equiv.sumCompl p
    have he : e.permCongr (Perm.sumCongr σ₁ σ₂) = σ := by
      ext x
      by_cases hx : p x
      · simp only [Equiv.permCongr_apply, e, Equiv.sumCompl_apply_symm_of_pos p x hx,
          Perm.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl, σ₁, Perm.subtypePerm_apply]
      · simp only [Equiv.permCongr_apply, e, Equiv.sumCompl_apply_symm_of_neg p x hx,
          Perm.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr, σ₂, Perm.subtypePerm_apply]
    have hsmall₁ : Fintype.card {x // p x} < n := by
      rw [← hcard]
      exact Fintype.card_subtype_lt hb
    have hsmall₂ : Fintype.card {x // ¬p x} < n := by
      rw [← hcard]
      exact Fintype.card_subtype_lt (not_not.mpr (SameCycle.rfl : p a))
    have h₁ := ih _ hsmall₁ σ₁ rfl
    have h₂ := ih _ hsmall₂ σ₂ rfl
    have hcount : orbitCount σ = orbitCount σ₁ + orbitCount σ₂ := by
      calc
        _ = orbitCount (e.permCongr (Perm.sumCongr σ₁ σ₂)) := congrArg orbitCount he.symm
        _ = _ := by rw [orbitCount_transport, orbitCount_sumCongr]
    calc
      _ = weightedInterval f (e.permCongr (Perm.sumCongr σ₁ σ₂)) := congrArg (weightedInterval f) he.symm
      _ = weightedInterval f σ₁ * weightedInterval f σ₂ := by
        rw [weightedInterval_transport, weightedInterval_sumCongr]
      _ = s ^ (orbitCount σ₁ + orbitCount σ₂) := by rw [h₁, h₂, pow_add]
      _ = _ := congrArg (fun z => s^z) hcount.symm

#print axioms weightedInterval_eq_pow_of_fullCycle
end ProjectionChannels.FreeMoments
