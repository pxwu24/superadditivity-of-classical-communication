import StrongConvergence.StrongConvergenceTensorPermutation
import StrongConvergence.StrongConvergenceTensorGram
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm

open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

/-- Number of tensor coordinates fixed by a permutation of tensor positions. -/
def fixedTupleCount (σ : Equiv.Perm (Fin m)) : ℕ :=
  Fintype.card {i : Fin m → E // i = fun l => i (σ l)}

lemma permutationTensor_trace_eq_fixedTupleCount (σ : Equiv.Perm (Fin m)) :
    Matrix.trace (permutationTensor (E := E) σ) = (fixedTupleCount (E := E) σ : ℂ) := by
  rw [permutationTensor_trace]
  simp [fixedTupleCount, Fintype.card_subtype]

@[simp] lemma fixedTupleCount_one :
    fixedTupleCount (E := E) (1 : Equiv.Perm (Fin m)) = Fintype.card E ^ m := by
  simp [fixedTupleCount]

/-- A nontrivial position permutation identifies two coordinates, hence costs
at least one free coordinate. -/
theorem fixedTupleCount_le_pow_pred (σ : Equiv.Perm (Fin m)) (hσ : σ ≠ 1) :
    fixedTupleCount (E := E) σ ≤ Fintype.card E ^ (m - 1) := by
  have hex : ∃ l, σ l ≠ l := by
    by_contra h
    push_neg at h
    apply hσ
    apply Equiv.ext
    intro l
    simpa using h l
  obtain ⟨l, hl⟩ := hex
  let f : {i : Fin m → E // i = fun r => i (σ r)} → ({r : Fin m // r ≠ l} → E) :=
    fun i r => i.val r.val
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    funext r
    by_cases hr : r = l
    · subst r
      calc
        i.val l = i.val (σ l) := congrFun i.property l
        _ = j.val (σ l) := congrFun h ⟨σ l, hl⟩
        _ = j.val l := (congrFun j.property l).symm
    · exact congrFun h ⟨r, hr⟩
  have hc := Fintype.card_le_of_injective f hf
  simpa [fixedTupleCount, Fintype.card_fun, Fintype.card_subtype_compl] using hc

lemma permutationGram_eq_fixedTupleCount (σ τ : Equiv.Perm (Fin m)) :
    permutationGram E m σ τ = (fixedTupleCount (E := E) (τ * σ.symm) : ℂ) := by
  rw [permutationGram_apply, permutationTensor_conjTranspose, permutationTensor_mul,
    permutationTensor_trace_eq_fixedTupleCount]

@[simp] theorem permutationGram_diag (σ : Equiv.Perm (Fin m)) :
    permutationGram E m σ σ = (Fintype.card E : ℂ) ^ m := by
  rw [permutationGram_eq_fixedTupleCount]
  simp

theorem norm_permutationGram_offdiag_le (σ τ : Equiv.Perm (Fin m)) (hστ : σ ≠ τ) :
    ‖permutationGram E m σ τ‖ ≤ (Fintype.card E : ℝ) ^ (m - 1) := by
  rw [permutationGram_eq_fixedTupleCount]
  have hne : τ * σ.symm ≠ 1 := by
    intro h
    have hh := congrArg (fun g => g * σ) h
    apply hστ
    simpa [mul_assoc] using hh.symm
  simpa using (Nat.cast_le (α := ℝ)).mpr (fixedTupleCount_le_pow_pred (E := E) _ hne)

/-- Entrywise error of the dimension-normalized Haar permutation Gram matrix. -/
theorem norm_normalized_permutationGram_sub_one_apply
    (hE : 0 < Fintype.card E) (hm : 0 < m) (σ τ : Equiv.Perm (Fin m)) :
    ‖(((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m - 1) σ τ‖ ≤
      if σ = τ then 0 else 1 / (Fintype.card E : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr hE
  have hNc : (Fintype.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hE)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hστ : σ = τ
  · subst τ
    simp [permutationGram_diag, hNc]
  · rw [if_neg hστ, Matrix.one_apply_ne hστ, sub_zero, norm_mul, norm_inv,
      norm_pow, Complex.norm_natCast]
    have hpow : (Fintype.card E : ℝ) ^ m =
        (Fintype.card E : ℝ) ^ (m - 1) * Fintype.card E := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      ((Fintype.card E : ℝ) ^ m)⁻¹ * ‖permutationGram E m σ τ‖ ≤
          ((Fintype.card E : ℝ) ^ m)⁻¹ * (Fintype.card E : ℝ) ^ (m - 1) :=
        mul_le_mul_of_nonneg_left (norm_permutationGram_offdiag_le σ τ hστ)
          (inv_nonneg.mpr (le_of_lt (pow_pos hN _)))
      _ = 1 / (Fintype.card E : ℝ) := by
        rw [hpow]
        field_simp

/-- The row-sum estimate is explicit in the tensor degree and dimension. -/
theorem normalized_permutationGram_sub_one_row_bound
    (hE : 0 < Fintype.card E) (hm : 0 < m) (σ : Equiv.Perm (Fin m)) :
    (∑ τ : Equiv.Perm (Fin m),
      ‖(((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m - 1) σ τ‖) ≤
      ((Fintype.card (Equiv.Perm (Fin m)) - 1 : ℕ) : ℝ) /
        (Fintype.card E : ℝ) := by
  calc
    _ ≤ ∑ τ : Equiv.Perm (Fin m), if σ = τ then 0 else
        1 / (Fintype.card E : ℝ) := by
      apply Finset.sum_le_sum
      intro τ _
      exact norm_normalized_permutationGram_sub_one_apply hE hm σ τ
    _ = _ := by
      simp [Finset.sum_ite, Finset.filter_ne, Finset.filter_ne', div_eq_mul_inv]

theorem normalized_permutationGram_sub_one_row_bound_factorial
    (hE : 0 < Fintype.card E) (hm : 0 < m) (σ : Equiv.Perm (Fin m)) :
    (∑ τ : Equiv.Perm (Fin m),
      ‖(((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m - 1) σ τ‖) ≤
      ((m.factorial - 1 : ℕ) : ℝ) / (Fintype.card E : ℝ) := by
  simpa only [Fintype.card_perm, Fintype.card_fin] using
    normalized_permutationGram_sub_one_row_bound hE hm σ

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.fixedTupleCount_le_pow_pred
#print axioms ProjectionChannels.TensorHaar.normalized_permutationGram_sub_one_row_bound_factorial
