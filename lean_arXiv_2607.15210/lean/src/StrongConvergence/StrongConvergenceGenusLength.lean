import StrongConvergence.StrongConvergenceTensorMomentAsymptotics
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.Perm.Fin

/-!
# Permutation length from fixed-coordinate subspaces

Cycle count is the dimension of the subspace fixed by permutation of coordinates.
The Grassmann dimension formula therefore gives the triangle inequality for
`m - cycleCount`. No asymptotic or probabilistic assumptions enter these facts.
-/
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {m : ℕ}

lemma permutation_symm_eq_inv (σ : Equiv.Perm (Fin m)) : σ.symm = σ⁻¹ := rfl

/-- Real coordinate vectors constant on every cycle of `σ`. -/
def cycleFixedSpace (σ : Equiv.Perm (Fin m)) : Submodule ℝ (Fin m → ℝ) where
  carrier := {v | v = fun i => v (σ i)}
  zero_mem' := rfl
  add_mem' := by
    intro v w hv hw
    funext i
    exact congrArg₂ (· + ·) (congrFun hv i) (congrFun hw i)
  smul_mem' := by
    intro c v hv
    funext i
    exact congrArg (fun x : ℝ => c * x) (congrFun hv i)

lemma cycleFixedSpace_constant_on_cycle (σ : Equiv.Perm (Fin m))
    (v : cycleFixedSpace σ) {a b : Fin m}
    (hab : Relation.EqvGen (fun i j : Fin m => j = σ i) a b) : v.val a = v.val b := by
  induction hab with
  | rel a b h => subst b; exact congrFun v.property a
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

/-- Choosing one value on each cycle parametrizes the fixed-coordinate space. -/
def cycleFixedSpaceEquiv (σ : Equiv.Perm (Fin m)) :
    cycleFixedSpace σ ≃ₗ[ℝ] (CycleClasses σ → ℝ) where
  toFun v := Quotient.lift v.val (fun _ _ h => cycleFixedSpace_constant_on_cycle σ v h)
  invFun f := ⟨fun i => f (Quotient.mk _ i), by
    funext i
    apply congrArg f
    exact Quotient.sound (Relation.EqvGen.rel i (σ i) rfl)⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv f := by
    funext q
    induction q using Quotient.inductionOn
    rfl
  map_add' := by
    intro v w
    funext q
    induction q using Quotient.inductionOn
    rfl
  map_smul' := by
    intro c v
    funext q
    induction q using Quotient.inductionOn
    rfl

lemma finrank_cycleFixedSpace (σ : Equiv.Perm (Fin m)) :
    Module.finrank ℝ (cycleFixedSpace σ) = cycleCount σ := by
  rw [(cycleFixedSpaceEquiv σ).finrank_eq]
  simp [cycleCount]

lemma cycleFixedSpace_symm (σ : Equiv.Perm (Fin m)) :
    cycleFixedSpace σ.symm = cycleFixedSpace σ := by
  ext v
  change (v = fun i => v (σ.symm i)) ↔ (v = fun i => v (σ i))
  constructor
  · intro h
    funext i
    simpa using (congrFun h (σ i)).symm
  · intro h
    funext i
    simpa using (congrFun h (σ.symm i)).symm

@[simp] theorem cycleCount_symm (σ : Equiv.Perm (Fin m)) :
    cycleCount σ.symm = cycleCount σ := by
  rw [← finrank_cycleFixedSpace, cycleFixedSpace_symm, finrank_cycleFixedSpace]

/-- Relabelling coordinates preserves the fixed-space dimension. -/
def cycleFixedSpaceConjEquiv (ρ σ : Equiv.Perm (Fin m)) :
    cycleFixedSpace σ ≃ₗ[ℝ] cycleFixedSpace (ρ * σ * ρ.symm) where
  toFun v := ⟨fun i => v.val (ρ.symm i), by
    funext i
    simpa using congrFun v.property (ρ.symm i)⟩
  invFun v := ⟨fun i => v.val (ρ i), by
    funext i
    simpa using congrFun v.property (ρ i)⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    simp
  right_inv v := by
    apply Subtype.ext
    funext i
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cycleCount_conj (ρ σ : Equiv.Perm (Fin m)) :
    cycleCount (ρ * σ * ρ.symm) = cycleCount σ := by
  rw [← finrank_cycleFixedSpace, ← finrank_cycleFixedSpace]
  exact (cycleFixedSpaceConjEquiv ρ σ).finrank_eq.symm

lemma cycleCount_mul_comm (σ τ : Equiv.Perm (Fin m)) :
    cycleCount (σ * τ) = cycleCount (τ * σ) := by
  simpa [mul_assoc] using cycleCount_conj σ (τ * σ)

@[simp] theorem cycleCount_one : cycleCount (1 : Equiv.Perm (Fin m)) = m := by
  have h : cycleFixedSpace (1 : Equiv.Perm (Fin m)) = ⊤ := by
    ext v
    simp [cycleFixedSpace]
  rw [← finrank_cycleFixedSpace, h]
  simp

lemma cycleFixedSpace_finRotate_constant (n : ℕ)
    (v : cycleFixedSpace (finRotate (n+1))) (i : Fin (n+1)) : v.val i = v.val 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have h := congrFun v.property i.castSucc
    have hr : finRotate (n+1) i.castSucc = i.succ := finRotate_of_lt i.is_lt
    rw [hr] at h
    exact h.symm.trans ih

/-- A full cyclic rotation fixes exactly the constant real vectors. -/
def cycleFixedSpaceFinRotateEquiv (n : ℕ) :
    cycleFixedSpace (finRotate (n+1)) ≃ₗ[ℝ] ℝ where
  toFun v := v.val 0
  invFun r := ⟨fun _ => r, rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    exact (cycleFixedSpace_finRotate_constant n v i).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cycleCount_finRotate_succ (n : ℕ) :
    cycleCount (finRotate (n+1)) = 1 := by
  rw [← finrank_cycleFixedSpace, (cycleFixedSpaceFinRotateEquiv n).finrank_eq]
  exact Module.finrank_self ℝ

lemma cycleCount_finRotate (hm : 0 < m) : cycleCount (finRotate m) = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact cycleCount_finRotate_succ n

lemma cycleFixedSpace_inf_le_mul (σ τ : Equiv.Perm (Fin m)) :
    cycleFixedSpace σ ⊓ cycleFixedSpace τ ≤ cycleFixedSpace (σ * τ) := by
  intro v hv
  change v = fun i => v ((σ * τ) i)
  funext i
  exact (congrFun hv.2 i).trans (congrFun hv.1 (τ i))

/-- Grassmann's dimension formula in the fixed-coordinate spaces. -/
theorem cycleCount_add_le_card_add_mul (σ τ : Equiv.Perm (Fin m)) :
    cycleCount σ + cycleCount τ ≤ m + cycleCount (σ * τ) := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (cycleFixedSpace σ) (cycleFixedSpace τ)
  have hsup : Module.finrank ℝ ↥(cycleFixedSpace σ ⊔ cycleFixedSpace τ) ≤ m := by
    simpa using (Submodule.finrank_le (cycleFixedSpace σ ⊔ cycleFixedSpace τ))
  have hinf : Module.finrank ℝ ↥(cycleFixedSpace σ ⊓ cycleFixedSpace τ) ≤
      cycleCount (σ * τ) := by
    rw [← finrank_cycleFixedSpace]
    exact Submodule.finrank_mono (cycleFixedSpace_inf_le_mul σ τ)
  rw [finrank_cycleFixedSpace, finrank_cycleFixedSpace] at hdim
  omega

/-- Absolute permutation length: the number of coordinates minus the number of cycles. -/
def permutationLength (σ : Equiv.Perm (Fin m)) : ℕ := m - cycleCount σ

lemma cycleCount_pos (hm : 0 < m) (σ : Equiv.Perm (Fin m)) :
    0 < cycleCount σ := by
  exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ ⟨0, hm⟩⟩

lemma permutationLength_le_pred (hm : 0 < m) (σ : Equiv.Perm (Fin m)) :
    permutationLength σ ≤ m - 1 := by
  have h := cycleCount_pos hm σ
  unfold permutationLength
  omega

lemma cycleCount_le_pred_of_ne_one (σ : Equiv.Perm (Fin m)) (hσ : σ ≠ 1) :
    cycleCount σ ≤ m - 1 := by
  classical
  have h := fixedTupleCount_le_pow_pred (E := Fin 2) σ hσ
  have hc : fixedTupleCount (E := Fin 2) σ = 2 ^ cycleCount σ := by
    rw [fixedTupleCount, Fintype.card_congr (fixedTupleEquiv (E := Fin 2) σ),
      Fintype.card_fun]
    rfl
  rw [hc] at h
  simp only [Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h

@[simp] lemma permutationLength_eq_zero_iff (σ : Equiv.Perm (Fin m)) :
    permutationLength σ = 0 ↔ σ = 1 := by
  constructor
  · intro h
    by_contra hσ
    have hp := cycleCount_le_pred_of_ne_one σ hσ
    have hm : 0 < m := by
      by_contra h
      have hm : m = 0 := by omega
      subst m
      exact hσ (Subsingleton.elim _ _)
    unfold permutationLength at h
    omega
  · rintro rfl
    simp [permutationLength]

@[simp] lemma permutationLength_conj (ρ σ : Equiv.Perm (Fin m)) :
    permutationLength (ρ * σ * ρ.symm) = permutationLength σ := by
  simp [permutationLength]

lemma permutationLength_mul_comm (σ τ : Equiv.Perm (Fin m)) :
    permutationLength (σ * τ) = permutationLength (τ * σ) := by
  simp only [permutationLength, cycleCount_mul_comm σ τ]

@[simp] lemma permutationLength_one : permutationLength (1 : Equiv.Perm (Fin m)) = 0 := by
  simp [permutationLength]

@[simp] lemma permutationLength_symm (σ : Equiv.Perm (Fin m)) :
    permutationLength σ.symm = permutationLength σ := by
  simp [permutationLength]

/-- The transposition-length triangle inequality, proved without a transposition decomposition. -/
theorem permutationLength_mul_le (σ τ : Equiv.Perm (Fin m)) :
    permutationLength (σ * τ) ≤ permutationLength σ + permutationLength τ := by
  have h := cycleCount_add_le_card_add_mul σ τ
  have hσ := cycleCount_le σ
  have hτ := cycleCount_le τ
  have hστ := cycleCount_le (σ * τ)
  unfold permutationLength
  omega

lemma permutationLength_finRotate (hm : 0 < m) :
    permutationLength (finRotate m) = m - 1 := by
  rw [permutationLength, cycleCount_finRotate hm]

/-- The exponent entering the moment expansion cannot be negative. -/
theorem permutationLength_add_finRotate_mul_ge (hm : 0 < m)
    (σ : Equiv.Perm (Fin m)) :
    m - 1 ≤ permutationLength σ + permutationLength (finRotate m * σ) := by
  have h := permutationLength_mul_le (finRotate m * σ) σ.symm
  simpa [mul_assoc, permutationLength_finRotate hm, Nat.add_comm] using h

lemma permutationLength_mul_symm_comm (σ τ : Equiv.Perm (Fin m)) :
    permutationLength (σ * τ.symm) = permutationLength (τ * σ.symm) := by
  have h := permutationLength_symm (σ * τ.symm)
  simpa only [permutation_symm_eq_inv, mul_inv_rev, inv_inv] using h.symm

lemma permutationLength_le_add_distance (σ τ : Equiv.Perm (Fin m)) :
    permutationLength σ ≤ permutationLength τ + permutationLength (τ * σ.symm) := by
  have h := permutationLength_mul_le (σ * τ.symm) τ
  simpa [mul_assoc, permutationLength_mul_symm_comm σ τ, Nat.add_comm] using h

/-- Nonnegativity of the complete genus exponent in the Haar moment expansion. -/
theorem permutationLength_genus_nonneg (hm : 0 < m) (σ τ : Equiv.Perm (Fin m)) :
    m - 1 ≤ permutationLength τ + permutationLength (τ * σ.symm) +
      permutationLength (finRotate m * σ) := by
  have h₁ := permutationLength_le_add_distance σ τ
  have h₂ := permutationLength_add_finRotate_mul_ge hm σ
  omega

/-- Geodesic (absolute) order on permutations. -/
def PermutationAbsoluteLE (σ τ : Equiv.Perm (Fin m)) : Prop :=
  permutationLength σ + permutationLength (τ * σ.symm) = permutationLength τ

theorem permutationLength_add_finRotate_mul_eq_iff (hm : 0 < m)
    (σ : Equiv.Perm (Fin m)) :
    permutationLength σ + permutationLength (finRotate m * σ) = m - 1 ↔
      PermutationAbsoluteLE σ.symm (finRotate m) := by
  simp [PermutationAbsoluteLE, permutationLength_finRotate hm]

@[refl] theorem permutationAbsoluteLE_refl (σ : Equiv.Perm (Fin m)) :
    PermutationAbsoluteLE σ σ := by
  simp [PermutationAbsoluteLE]

theorem permutationAbsoluteLE_antisymm {σ τ : Equiv.Perm (Fin m)}
    (hστ : PermutationAbsoluteLE σ τ) (hτσ : PermutationAbsoluteLE τ σ) : σ = τ := by
  have hz : permutationLength (τ * σ.symm) = 0 := by
    unfold PermutationAbsoluteLE at hστ hτσ
    omega
  have h := (permutationLength_eq_zero_iff _).mp hz
  have h' := congrArg (fun ρ => ρ * σ) h
  simpa [mul_assoc] using h'.symm

@[trans] theorem permutationAbsoluteLE_trans {σ τ ρ : Equiv.Perm (Fin m)}
    (hστ : PermutationAbsoluteLE σ τ) (hτρ : PermutationAbsoluteLE τ ρ) :
    PermutationAbsoluteLE σ ρ := by
  have hupper : permutationLength (ρ * σ.symm) ≤
      permutationLength (ρ * τ.symm) + permutationLength (τ * σ.symm) := by
    simpa [permutation_symm_eq_inv, mul_assoc] using
      permutationLength_mul_le (ρ * τ.symm) (τ * σ.symm)
  have hlower : permutationLength ρ ≤
      permutationLength (ρ * σ.symm) + permutationLength σ := by
    simpa [mul_assoc] using permutationLength_mul_le (ρ * σ.symm) σ
  unfold PermutationAbsoluteLE at *
  omega

theorem permutationAbsoluteLE_conj_iff (ρ σ τ : Equiv.Perm (Fin m)) :
    PermutationAbsoluteLE (ρ * σ * ρ.symm) (ρ * τ * ρ.symm) ↔
      PermutationAbsoluteLE σ τ := by
  have hres : (ρ * τ * ρ.symm) * (ρ * σ * ρ.symm).symm =
      ρ * (τ * σ.symm) * ρ.symm := by
    simp [permutation_symm_eq_inv, mul_assoc]
  simp only [PermutationAbsoluteLE, hres, permutationLength_conj]

theorem permutationAbsoluteLE_symm_iff (σ τ : Equiv.Perm (Fin m)) :
    PermutationAbsoluteLE σ.symm τ.symm ↔ PermutationAbsoluteLE σ τ := by
  have hres : permutationLength (τ.symm * σ) = permutationLength (τ * σ.symm) := by
    calc
      _ = permutationLength (σ * τ.symm) := permutationLength_mul_comm _ _
      _ = permutationLength (τ * σ.symm).symm := by
        simp only [permutation_symm_eq_inv, mul_inv_rev, inv_inv]
      _ = _ := permutationLength_symm _
  simp [PermutationAbsoluteLE, hres]

theorem permutationLength_lt_of_absoluteLE_ne {σ τ : Equiv.Perm (Fin m)}
    (h : PermutationAbsoluteLE σ τ) (hne : σ ≠ τ) :
    permutationLength σ < permutationLength τ := by
  have hpos : 0 < permutationLength (τ * σ.symm) := by
    by_contra hpos
    have hz : permutationLength (τ * σ.symm) = 0 := by omega
    have he := (permutationLength_eq_zero_iff _).mp hz
    have he' := congrArg (fun ρ => ρ * σ) he
    apply hne
    simpa [mul_assoc] using he'.symm
  unfold PermutationAbsoluteLE at h
  omega

/-- The genus-zero terms are precisely the two-step absolute-order chains. -/
theorem permutationLength_genus_eq_iff (hm : 0 < m) (σ τ : Equiv.Perm (Fin m)) :
    permutationLength τ + permutationLength (τ * σ.symm) +
      permutationLength (finRotate m * σ) = m - 1 ↔
      PermutationAbsoluteLE τ σ ∧ PermutationAbsoluteLE σ.symm (finRotate m) := by
  have h₁ := permutationLength_le_add_distance σ τ
  have h₂ := permutationLength_add_finRotate_mul_ge hm σ
  rw [PermutationAbsoluteLE, permutationLength_mul_symm_comm σ τ,
    ← permutationLength_add_finRotate_mul_eq_iff hm σ]
  omega

#print axioms permutationAbsoluteLE_trans
#print axioms cycleCount_add_le_card_add_mul
#print axioms permutationLength_mul_le
end ProjectionChannels.TensorHaar
