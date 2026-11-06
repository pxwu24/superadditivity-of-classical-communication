import StrongConvergence.StrongConvergenceGenusParity
import Mathlib.Tactic

/-! Geodesic-order refinement, transposition steps, and deletion of a fixed point. -/
open Equiv Equiv.Perm
noncomputable section
namespace ProjectionChannels.TensorHaar
variable {m : ℕ}

/-- Cycle-constant vectors separate distinct permutation cycles. -/
theorem sameCycle_of_fixed_vectors (σ : Perm (Fin m)) (x y : Fin m)
    (h : ∀ v : Fin m → ℝ, v ∈ cycleFixedSpace σ → v x = v y) :
    σ.SameCycle x y := by
  classical
  let f : CycleClasses σ → ℝ := fun q => if q = Quotient.mk _ x then 1 else 0
  let v := (cycleFixedSpaceEquiv σ).symm f
  have hv := h v.val v.property
  have hqx : (Quotient.mk _ y : CycleClasses σ) = Quotient.mk _ x := by
    by_contra hne
    have hx : v.val x = 1 := by
      change (if (Quotient.mk _ x : CycleClasses σ) = Quotient.mk _ x then 1 else 0) = 1
      exact if_pos rfl
    have hy : v.val y = 0 := by
      change (if (Quotient.mk _ y : CycleClasses σ) = Quotient.mk _ x then 1 else 0) = 0
      exact if_neg hne
    rw [hx, hy] at hv
    norm_num at hv
  exact (cycleRelation_iff_sameCycle σ x y).mp (Quotient.exact hqx.symm)

/-- A geodesic factorization gives equality in the fixed-space dimension bound. -/
theorem cycleFixedSpace_eq_inf_of_absoluteLE {τ ρ : Perm (Fin m)}
    (h : PermutationAbsoluteLE τ ρ) :
    cycleFixedSpace ρ = cycleFixedSpace (ρ * τ.symm) ⊓ cycleFixedSpace τ := by
  have hle : cycleFixedSpace (ρ * τ.symm) ⊓ cycleFixedSpace τ ≤ cycleFixedSpace ρ := by
    simpa [permutation_symm_eq_inv, mul_assoc] using
      cycleFixedSpace_inf_le_mul (ρ * τ.symm) τ
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (cycleFixedSpace (ρ * τ.symm)) (cycleFixedSpace τ)
  have hsup : Module.finrank ℝ ↥(cycleFixedSpace (ρ * τ.symm) ⊔ cycleFixedSpace τ) ≤ m := by
    simpa using Submodule.finrank_le (cycleFixedSpace (ρ * τ.symm) ⊔ cycleFixedSpace τ)
  have hinf := Submodule.finrank_mono hle
  have hcount : cycleCount (ρ * τ.symm) + cycleCount τ = m + cycleCount ρ := by
    have hτ := cycleCount_le τ
    have hρ := cycleCount_le ρ
    have hr := cycleCount_le (ρ * τ.symm)
    unfold PermutationAbsoluteLE permutationLength at h
    omega
  have heq : Module.finrank ℝ ↥(cycleFixedSpace (ρ * τ.symm) ⊓ cycleFixedSpace τ) =
      Module.finrank ℝ (cycleFixedSpace ρ) := by
    rw [finrank_cycleFixedSpace, finrank_cycleFixedSpace] at hdim
    rw [finrank_cycleFixedSpace] at hinf ⊢
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle heq).symm

theorem cycleFixedSpace_le_of_absoluteLE {τ ρ : Perm (Fin m)}
    (h : PermutationAbsoluteLE τ ρ) : cycleFixedSpace ρ ≤ cycleFixedSpace τ := by
  rw [cycleFixedSpace_eq_inf_of_absoluteLE h]
  exact inf_le_right

/-- Every cycle of a lower permutation is contained in a cycle of the upper one. -/
theorem sameCycle_apply_of_absoluteLE {τ ρ : Perm (Fin m)}
    (h : PermutationAbsoluteLE τ ρ) (a : Fin m) : ρ.SameCycle a (τ a) := by
  apply sameCycle_of_fixed_vectors
  intro v hv
  exact congrFun (cycleFixedSpace_le_of_absoluteLE h hv) a

/-- Removing a common initial geodesic segment identifies the remaining interval. -/
theorem permutationAbsoluteLE_peel {s γ : Perm (Fin m)}
    (hsγ : PermutationAbsoluteLE s γ) (σ : Perm (Fin m)) :
    (PermutationAbsoluteLE s σ ∧ PermutationAbsoluteLE σ γ) ↔
      PermutationAbsoluteLE (s.symm * σ) (s.symm * γ) := by
  have hres : permutationLength ((s.symm * γ) * (s.symm * σ).symm) =
      permutationLength (γ * σ.symm) := by
    have he : (s.symm * γ) * (s.symm * σ).symm =
        s.symm * (γ * σ.symm) * s.symm.symm := by
      simp [permutation_symm_eq_inv, mul_assoc]
    rw [he, permutationLength_conj]
  have hσ := permutationLength_mul_le s (s.symm * σ)
  have hγ := permutationLength_le_add_distance γ σ
  have hd := permutationLength_mul_symm_comm γ σ
  simp only [permutation_symm_eq_inv, mul_inv_cancel_left] at hσ
  unfold PermutationAbsoluteLE at hsγ ⊢
  rw [hres]
  rw [permutationLength_mul_comm γ s.symm] at hsγ
  rw [permutationLength_mul_comm σ s.symm]
  simp only [permutation_symm_eq_inv] at *
  omega

lemma cycleCount_swap {x y : Fin m} (hxy : x ≠ y) :
    cycleCount (swap x y) = m - 1 := by
  have hm : 2 ≤ m := by
    have h := Finset.card_le_univ ({x,y} : Finset (Fin m))
    simpa [hxy] using h
  have hc : (swap x y).cycleType = {2} := by
    rw [(isCycle_swap hxy).cycleType, card_support_swap hxy]
  rw [cycleCount_eq_card_cycleType_add_fixedPoints, card_fixedPoints, hc]
  simp only [Multiset.card_singleton, Multiset.sum_singleton, Fintype.card_fin]
  omega

lemma permutationLength_swap {x y : Fin m} (hxy : x ≠ y) :
    permutationLength (swap x y) = 1 := by
  have hm : 0 < m := x.pos
  rw [permutationLength, cycleCount_swap hxy]
  omega

lemma mem_cycleFixedSpace_swap_iff (x y : Fin m) (v : Fin m → ℝ) :
    v ∈ cycleFixedSpace (swap x y) ↔ v x = v y := by
  change (v = fun i => v (swap x y i)) ↔ _
  constructor
  · intro h
    simpa using congrFun h x
  · intro h
    funext i
    by_cases hix : i = x
    · subst i; simpa using h
    · by_cases hiy : i = y
      · subst i; simpa using h.symm
      · simp [swap_apply_of_ne_of_ne hix hiy]

/-- Cutting one cycle with a transposition lowers absolute length by one. -/
theorem permutationLength_swap_mul_of_sameCycle {x y : Fin m} (hxy : x ≠ y)
    (σ : Perm (Fin m)) (hcycle : σ.SameCycle x y) :
    permutationLength (swap x y * σ) + 1 = permutationLength σ := by
  have hfix : cycleFixedSpace σ ≤ cycleFixedSpace (swap x y) := by
    intro v hv
    apply (mem_cycleFixedSpace_swap_iff x y v).mpr
    exact cycleFixedSpace_constant_on_cycle σ ⟨v,hv⟩
      ((cycleRelation_iff_sameCycle σ x y).mpr hcycle)
  have hinc : cycleFixedSpace σ ≤ cycleFixedSpace (swap x y * σ) := by
    exact le_trans (le_inf hfix le_rfl) (cycleFixedSpace_inf_le_mul (swap x y) σ)
  have hdim := Submodule.finrank_mono hinc
  rw [finrank_cycleFixedSpace, finrank_cycleFixedSpace] at hdim
  have hlo := permutationLength_mul_le (swap x y) (swap x y * σ)
  have hpar := permutationLength_mul_mod_two (swap x y) σ
  rw [permutationLength_swap hxy] at hlo hpar
  simp only [← mul_assoc, swap_mul_self, one_mul] at hlo
  have hlen : permutationLength (swap x y * σ) ≤ permutationLength σ := by
    unfold permutationLength
    omega
  omega

/-- A transposition is below a permutation exactly when its two points share a cycle. -/
theorem swap_absoluteLE_iff_sameCycle {x y : Fin m} (hxy : x ≠ y)
    (σ : Perm (Fin m)) : PermutationAbsoluteLE (swap x y) σ ↔ σ.SameCycle x y := by
  constructor
  · intro h
    simpa using sameCycle_apply_of_absoluteLE h x
  · intro h
    have hd := permutationLength_swap_mul_of_sameCycle hxy σ h
    unfold PermutationAbsoluteLE
    simpa [permutation_symm_eq_inv, swap_inv, permutationLength_swap hxy,
      permutationLength_mul_comm σ (swap x y), Nat.add_comm] using hd

/-- Joining two different cycles raises absolute length by one. -/
theorem permutationLength_swap_mul_of_not_sameCycle {x y : Fin m} (hxy : x ≠ y)
    (σ : Perm (Fin m)) (hcycle : ¬σ.SameCycle x y) :
    permutationLength (swap x y * σ) = permutationLength σ + 1 := by
  have hlo := permutationLength_mul_le (swap x y) (swap x y * σ)
  have hhi := permutationLength_mul_le (swap x y) σ
  have hpar := permutationLength_mul_mod_two (swap x y) σ
  rw [permutationLength_swap hxy] at hlo hhi hpar
  simp only [← mul_assoc, swap_mul_self, one_mul] at hlo
  have hnot : permutationLength (swap x y * σ) + 1 ≠ permutationLength σ := by
    intro he
    apply hcycle
    apply (swap_absoluteLE_iff_sameCycle hxy σ).mp
    unfold PermutationAbsoluteLE
    simpa [permutation_symm_eq_inv, swap_inv, permutationLength_swap hxy,
      permutationLength_mul_comm σ (swap x y), Nat.add_comm] using he
  omega

/-- The transposition form of geodesic interval deletion used in the peel recursion. -/
theorem swap_absoluteLE_peel {x y : Fin m} {γ : Perm (Fin m)}
    (h : PermutationAbsoluteLE (swap x y) γ) (σ : Perm (Fin m)) :
    (PermutationAbsoluteLE (swap x y) σ ∧ PermutationAbsoluteLE σ γ) ↔
      PermutationAbsoluteLE (swap x y * σ) (swap x y * γ) := by
  simpa [permutation_symm_eq_inv] using permutationAbsoluteLE_peel h σ

/-- If the lower permutation fixes a point, delete that point from the upper cycle. -/
theorem permutationAbsoluteLE_fixed_point (σ γ : Perm (Fin m)) (o : Fin m)
    (hσ : σ o = o) (hγ : γ o ≠ o) :
    PermutationAbsoluteLE σ γ ↔ PermutationAbsoluteLE σ (swap o (γ o) * γ) := by
  have hxy : o ≠ γ o := hγ.symm
  have hσi : σ.symm o = o := by
    apply σ.injective
    simpa using hσ.symm
  have hcycle : γ.SameCycle o (γ o) := (SameCycle.refl γ o).apply_right
  have hrescycle : (γ * σ.symm).SameCycle o (γ o) := by
    have h := (SameCycle.refl (γ * σ.symm) o).apply_right
    simpa [Equiv.Perm.mul_apply, hσi] using h
  have hdrop := permutationLength_swap_mul_of_sameCycle hxy γ hcycle
  have hresdrop := permutationLength_swap_mul_of_sameCycle hxy (γ * σ.symm) hrescycle
  unfold PermutationAbsoluteLE
  rw [mul_assoc]
  omega

lemma not_sameCycle_swap_mul_of_sameCycle {x y : Fin m} (hxy : x ≠ y)
    (σ : Perm (Fin m)) (h : σ.SameCycle x y) : ¬(swap x y * σ).SameCycle x y := by
  intro h'
  have h₁ := permutationLength_swap_mul_of_sameCycle hxy σ h
  have h₂ := permutationLength_swap_mul_of_sameCycle hxy (swap x y * σ) h'
  simp only [← mul_assoc, swap_mul_self, one_mul] at h₂
  omega

lemma sameCycle_swap_mul_of_not_sameCycle {x y : Fin m} (hxy : x ≠ y)
    (σ : Perm (Fin m)) (h : ¬σ.SameCycle x y) : (swap x y * σ).SameCycle x y := by
  by_contra h'
  have h₁ := permutationLength_swap_mul_of_not_sameCycle hxy σ h
  have h₂ := permutationLength_swap_mul_of_not_sameCycle hxy (swap x y * σ) h'
  simp only [← mul_assoc, swap_mul_self, one_mul] at h₂
  omega

lemma cycleCount_swap_mul_of_sameCycle {x y : Fin m} (hxy : x ≠ y)
    (σ : Perm (Fin m)) (h : σ.SameCycle x y) :
    cycleCount (swap x y * σ) = cycleCount σ + 1 := by
  have hd := permutationLength_swap_mul_of_sameCycle hxy σ h
  have h₁ := cycleCount_le σ
  have h₂ := cycleCount_le (swap x y * σ)
  unfold permutationLength at hd
  omega

lemma cycleCount_swap_mul_of_not_sameCycle {x y : Fin m} (hxy : x ≠ y)
    (σ : Perm (Fin m)) (h : ¬σ.SameCycle x y) :
    cycleCount (swap x y * σ) + 1 = cycleCount σ := by
  have hd := permutationLength_swap_mul_of_not_sameCycle hxy σ h
  have h₁ := cycleCount_le σ
  have h₂ := cycleCount_le (swap x y * σ)
  unfold permutationLength at hd
  omega

#print axioms permutationAbsoluteLE_fixed_point
#print axioms cycleCount_swap_mul_of_sameCycle
#print axioms sameCycle_apply_of_absoluteLE
#print axioms permutationAbsoluteLE_peel
#print axioms swap_absoluteLE_iff_sameCycle
end ProjectionChannels.TensorHaar
