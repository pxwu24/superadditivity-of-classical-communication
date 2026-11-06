import StrongConvergence.StrongConvergenceTensorPermutation
import StrongConvergence.StrongConvergenceTensorGram
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Quotient

/-! Cycle counts and the explicit entries of the Haar permutation Gram matrix.
Fixed points are cycles of length one. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

abbrev CycleClasses (σ : Equiv.Perm (Fin m)) :=
  Quotient (Relation.EqvGen.setoid (fun i j : Fin m => j = σ i))

noncomputable instance cycleClassesFintype (σ : Equiv.Perm (Fin m)) :
    Fintype (CycleClasses σ) := Fintype.ofFinite _

/-- Number of cycles, including singleton cycles. -/
def cycleCount (σ : Equiv.Perm (Fin m)) : ℕ := Fintype.card (CycleClasses σ)

lemma fixedTuple_constant_on_cycle (σ : Equiv.Perm (Fin m))
    (i : Fin m → E) (hi : i = fun l => i (σ l))
    {a b : Fin m} (hab : Relation.EqvGen (fun l r => r = σ l) a b) : i a = i b := by
  induction hab with
  | rel a b h => subst b; exact congrFun hi a
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

def fixedTupleEquiv (σ : Equiv.Perm (Fin m)) :
    {i : Fin m → E // i = fun l => i (σ l)} ≃ (CycleClasses σ → E) where
  toFun i := Quotient.lift i.val (fun _ _ h => fixedTuple_constant_on_cycle σ i.val i.property h)
  invFun f := ⟨fun l => f (Quotient.mk _ l), by
    funext l
    apply congrArg f
    exact Quotient.sound (Relation.EqvGen.rel l (σ l) rfl)⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv f := by
    funext q
    induction q using Quotient.inductionOn
    rfl

theorem fixedTupleCount_eq (σ : Equiv.Perm (Fin m)) :
    (Finset.univ.filter (fun i : Fin m → E => i = fun l => i (σ l))).card =
      Fintype.card E ^ cycleCount σ := by
  classical
  rw [← Fintype.card_subtype (fun i : Fin m → E => i = fun l => i (σ l)),
    Fintype.card_congr (fixedTupleEquiv (E := E) σ), Fintype.card_fun]
  rfl

theorem permutationTensor_trace_cycles (σ : Equiv.Perm (Fin m)) :
    Matrix.trace (permutationTensor (E := E) σ) =
      (Fintype.card E : ℂ) ^ cycleCount σ := by
  rw [permutationTensor_trace, fixedTupleCount_eq]
  exact Nat.cast_pow _ _

/-- The exact Gram matrix underlying unitary Weingarten integration. -/
theorem permutationGram_cycles (σ τ : Equiv.Perm (Fin m)) :
    permutationGram E m σ τ =
      (Fintype.card E : ℂ) ^ cycleCount (τ * σ.symm) := by
  rw [permutationGram_apply, permutationTensor_conjTranspose,
    permutationTensor_mul, permutationTensor_trace_cycles]

def selectedFixedTupleEquiv (S : Finset E) (σ : Equiv.Perm (Fin m)) :
    {i : Fin m → E // i = (fun l => i (σ l)) ∧ ∀ l, i l ∈ S} ≃
      {j : Fin m → ↥S // j = fun l => j (σ l)} where
  toFun i := ⟨fun l => ⟨i.val l, i.property.2 l⟩, by
    funext l
    apply Subtype.ext
    exact congrFun i.property.1 l⟩
  invFun j := ⟨fun l => (j.val l).val, by
    constructor
    · funext l
      exact congrArg Subtype.val (congrFun j.property l)
    · intro l
      exact (j.val l).property⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv j := by apply Subtype.ext; rfl

lemma tensor_indicator_product (S : Finset E) (i : Fin m → E) :
    (∏ l, if i l ∈ S then (1 : ℂ) else 0) =
      if ∀ l, i l ∈ S then 1 else 0 := by
  classical
  by_cases h : ∀ l, i l ∈ S
  · simp [h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨l, hl⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)

/-- A projection of rank d has d choices for the common color on each cycle. -/
theorem permutation_trace_tensor_diagonal_projection (S : Finset E)
    (σ : Equiv.Perm (Fin m)) :
    Matrix.trace (permutationTensor (E := E) σ *
      tensorPower m (Matrix.diagonal (fun e => if e ∈ S then (1 : ℂ) else 0))) =
      (S.card : ℂ) ^ cycleCount σ := by
  classical
  have hc : Fintype.card {i : Fin m → E // i = (fun l => i (σ l)) ∧ ∀ l, i l ∈ S} =
      S.card ^ cycleCount σ := by
    rw [Fintype.card_congr ((selectedFixedTupleEquiv S σ).trans
      (fixedTupleEquiv (E := ↥S) σ)), Fintype.card_fun, Fintype.card_coe]
    rfl
  have ht : Matrix.trace (permutationTensor (E := E) σ *
      tensorPower m (Matrix.diagonal (fun e => if e ∈ S then (1 : ℂ) else 0))) =
      (Fintype.card {i : Fin m → E // i = (fun l => i (σ l)) ∧ ∀ l, i l ∈ S} : ℂ) := by
    rw [tensorPower_diagonal]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, permutationTensor,
      tensor_indicator_product, ite_mul, one_mul, zero_mul, ← ite_and]
    simp [Fintype.card_subtype]
  rw [ht, hc, Nat.cast_pow]

#print axioms permutationGram_cycles
end ProjectionChannels.TensorHaar
