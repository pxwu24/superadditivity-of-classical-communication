import StrongConvergence.StrongConvergenceGenusLength
import Mathlib.Algebra.Ring.Commute

/-! Relating the project's quotient cycle count to Mathlib's cycle type and sign. -/
noncomputable section
namespace ProjectionChannels.TensorHaar
open Equiv.Perm
variable {m : ℕ}

lemma cycleRelation_iff_sameCycle (σ : Equiv.Perm (Fin m)) (x y : Fin m) :
    Relation.EqvGen (fun i j : Fin m => j = σ i) x y ↔ σ.SameCycle x y := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
      subst b
      exact (SameCycle.refl σ a).apply_right
    | refl a => exact SameCycle.refl σ a
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Relation.EqvGen.refl x
    | succ n ih =>
      apply Relation.EqvGen.trans _ _ _ ih
      apply Relation.EqvGen.rel
      simp [pow_succ', Equiv.Perm.mul_apply]

abbrev PermutationCycleLabel (σ : Equiv.Perm (Fin m)) :=
  Function.fixedPoints σ ⊕ ↥σ.cycleFactorsFinset

/-- Label a cycle by its fixed point or its nontrivial cycle factor. -/
def permutationCycleLabel (σ : Equiv.Perm (Fin m)) (x : Fin m) :
    PermutationCycleLabel σ := by
  classical
  exact if h : σ x = x then Sum.inl ⟨x, h⟩ else
    Sum.inr ⟨σ.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr h)⟩

lemma permutationCycleLabel_eq_iff (σ : Equiv.Perm (Fin m)) (x y : Fin m) :
    permutationCycleLabel σ x = permutationCycleLabel σ y ↔ σ.SameCycle x y := by
  classical
  constructor
  · intro h
    by_cases hx : σ x = x
    · by_cases hy : σ y = y
      · simp only [permutationCycleLabel, dif_pos hx, dif_pos hy, Sum.inl.injEq,
          Subtype.mk.injEq] at h
        exact h.sameCycle σ
      · simp [permutationCycleLabel, hx, hy] at h
    · by_cases hy : σ y = y
      · simp [permutationCycleLabel, hx, hy] at h
      · simp only [permutationCycleLabel, dif_neg hx, dif_neg hy, Sum.inr.injEq,
          Subtype.mk.injEq] at h
        exact (sameCycle_iff_cycleOf_eq_of_mem_support
          (mem_support.mpr hx) (mem_support.mpr hy)).mpr h
  · intro h
    by_cases hx : σ x = x
    · have hxy := h.eq_of_left hx
      subst y
      rfl
    · have hy : σ y ≠ y := fun hy => hx (h.apply_eq_self_iff.mpr hy)
      simp only [permutationCycleLabel, dif_neg hx, dif_neg hy]
      exact congrArg Sum.inr (Subtype.ext h.cycleOf_eq)

lemma permutationCycleLabel_surjective (σ : Equiv.Perm (Fin m)) :
    Function.Surjective (permutationCycleLabel σ) := by
  classical
  rintro (x | c)
  · refine ⟨x.val, ?_⟩
    simp [permutationCycleLabel, show σ x.val = x.val from x.property]
  · obtain ⟨x, hx⟩ := (mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support
    have he : c.val = σ.cycleOf x := cycle_is_cycleOf hx c.property
    have hmove : σ x ≠ x := by
      have hcx : c.val x ≠ x := mem_support.mp hx
      rwa [(mem_cycleFactorsFinset_iff.mp c.property).2 x hx] at hcx
    refine ⟨x, ?_⟩
    simp only [permutationCycleLabel, dif_neg hmove]
    exact congrArg Sum.inr (Subtype.ext he.symm)

/-- The quotient-defined cycles include both fixed points and nontrivial cycles. -/
def cycleClassesLabelEquiv (σ : Equiv.Perm (Fin m)) :
    CycleClasses σ ≃ PermutationCycleLabel σ := by
  classical
  let f : CycleClasses σ → PermutationCycleLabel σ :=
    Quotient.lift (permutationCycleLabel σ) (fun x y h =>
      (permutationCycleLabel_eq_iff σ x y).mpr ((cycleRelation_iff_sameCycle σ x y).mp h))
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        apply Quotient.sound
        exact (cycleRelation_iff_sameCycle σ x y).mpr
          ((permutationCycleLabel_eq_iff σ x y).mp h)
  · intro z
    obtain ⟨x, hx⟩ := permutationCycleLabel_surjective σ z
    exact ⟨Quotient.mk _ x, hx⟩

/-- Compatibility with Mathlib's convention that `cycleType` omits fixed points. -/
theorem cycleCount_eq_card_cycleType_add_fixedPoints (σ : Equiv.Perm (Fin m)) :
    cycleCount σ = σ.cycleType.card + Fintype.card (Function.fixedPoints σ) := by
  classical
  rw [cycleCount, Fintype.card_congr (cycleClassesLabelEquiv σ)]
  simp [PermutationCycleLabel, Equiv.Perm.cycleType_def, Nat.add_comm]

/-- The sign formula expressed using the project's absolute length. -/
theorem sign_eq_neg_one_pow_permutationLength (σ : Equiv.Perm (Fin m)) :
    (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ permutationLength σ := by
  have hcount := cycleCount_eq_card_cycleType_add_fixedPoints σ
  have hsum := Equiv.Perm.sum_cycleType σ
  have hfixed := Equiv.Perm.card_fixedPoints σ
  have hle : σ.cycleType.sum ≤ m := by
    rw [hsum]
    simpa using σ.support.card_le_univ
  have hcycles := cycleCount_le σ
  have hmod : (σ.cycleType.sum + σ.cycleType.card) % 2 = permutationLength σ % 2 := by
    simp only [Fintype.card_fin] at hfixed
    unfold permutationLength
    omega
  rw [Equiv.Perm.sign_of_cycleType]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (permutationLength σ), hmod]

lemma permutationLength_mul_mod_two (σ τ : Equiv.Perm (Fin m)) :
    (permutationLength σ + permutationLength τ) % 2 = permutationLength (σ * τ) % 2 := by
  have hp : (-1 : ℤ) ^ (permutationLength σ + permutationLength τ) =
      (-1 : ℤ) ^ permutationLength (σ * τ) := by
    rw [pow_add, ← sign_eq_neg_one_pow_permutationLength,
      ← sign_eq_neg_one_pow_permutationLength, ← sign_eq_neg_one_pow_permutationLength]
    simp
  rw [neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two (permutationLength (σ * τ))] at hp
  have h₁ := Nat.mod_lt (permutationLength σ + permutationLength τ) (by decide : 0 < 2)
  have h₂ := Nat.mod_lt (permutationLength (σ * τ)) (by decide : 0 < 2)
  by_contra h
  have hc : ((permutationLength σ + permutationLength τ) % 2 = 0 ∧
      permutationLength (σ * τ) % 2 = 1) ∨
      ((permutationLength σ + permutationLength τ) % 2 = 1 ∧
      permutationLength (σ * τ) % 2 = 0) := by omega
  rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [ha, hb] at hp

lemma permutationDistance_parity (σ τ ρ : Equiv.Perm (Fin m)) :
    (permutationLength (τ * σ.symm) + permutationLength (ρ * τ.symm)) % 2 =
      permutationLength (ρ * σ.symm) % 2 := by
  have h := permutationLength_mul_mod_two (ρ * τ.symm) (τ * σ.symm)
  simpa [permutation_symm_eq_inv, mul_assoc, Nat.add_comm] using h

/-- Every exponent in the normalized Haar moment expansion has even genus. -/
theorem permutationLength_genus_even (hm : 0 < m) (σ τ : Equiv.Perm (Fin m)) :
    Even (permutationLength τ + permutationLength (τ * σ.symm) +
      permutationLength (finRotate m * σ) - (m - 1)) := by
  have h₁ := permutationLength_mul_mod_two τ σ.symm
  have h₂ := permutationLength_mul_mod_two (finRotate m) σ
  have h₃ := permutationLength_genus_nonneg hm σ τ
  rw [permutationLength_symm] at h₁
  rw [permutationLength_finRotate hm] at h₂
  rw [Nat.even_iff]
  omega

#print axioms cycleCount_eq_card_cycleType_add_fixedPoints
#print axioms sign_eq_neg_one_pow_permutationLength
#print axioms permutationDistance_parity
#print axioms permutationLength_genus_even
end ProjectionChannels.TensorHaar
