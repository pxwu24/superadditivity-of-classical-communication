import StrongConvergence.StrongConvergenceTensorGramRow
import Mathlib.Analysis.Matrix

open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

section General
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
local instance : NormedRing (Matrix I I ℂ) := Matrix.linftyOpNormedRing

lemma linfty_norm_le_of_row_bounds (A : Matrix I I ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ r) : ‖A‖ ≤ r := by
  rw [Matrix.linfty_opNorm_def]
  have hnn : (Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊)) ≤ (⟨r, hr⟩ : NNReal) := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum, coe_nnnorm] using hrow i
  exact_mod_cast hnn

lemma row_sum_le_linfty_norm (A : Matrix I I ℂ) (i : I) :
    (∑ j, ‖A i j‖) ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h := Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)
  have hh := (NNReal.coe_le_coe.mpr h)
  simpa only [NNReal.coe_sum, coe_nnnorm] using hh

/-- A quantitative inverse perturbation bound in the maximum absolute row-sum
norm, proved directly from the inverse identity. -/
theorem inverse_error_row_bound (A B : Matrix I I ℂ) (hBA : B * A = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hrow : ∀ i, ∑ j, ‖(A - 1) i j‖ ≤ ε) (i : I) :
    (∑ j, ‖(B - 1) i j‖) ≤ ε / (1 - ε) := by
  have hnorm : ‖A - 1‖ ≤ ε := linfty_norm_le_of_row_bounds _ hε0 hrow
  have hid : B - 1 = B * (1 - A) := by rw [mul_sub, mul_one, hBA]
  have htri : ‖B‖ ≤ ‖B - 1‖ + 1 := by
    simpa using (norm_add_le (B - 1) (1 : Matrix I I ℂ))
  have hx : ‖B - 1‖ ≤ (‖B - 1‖ + 1) * ε := calc
    ‖B - 1‖ = ‖B * (1 - A)‖ := congrArg norm hid
    _ ≤ ‖B‖ * ‖1 - A‖ := norm_mul_le _ _
    _ ≤ (‖B - 1‖ + 1) * ε := by
      rw [norm_sub_rev 1 A]
      exact mul_le_mul htri hnorm (norm_nonneg _) (by positivity)
  have hb : ‖B - 1‖ ≤ ε / (1 - ε) := by
    apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
    nlinarith
  exact (row_sum_le_linfty_norm (B - 1) i).trans hb

end General

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

/-- The sharp elementary inverse-Gram estimate in stable dimension. Its error
parameter has product form, allowing the tensor degree to grow with dimension. -/
theorem scaled_inverse_permutationGram_row_bound
    (e : Fin m ↪ E) (hE : 0 < Fintype.card E)
    (hsmall : (∏ j ∈ Finset.range m, (1 + (j : ℝ) / Fintype.card E)) - 1 < 1)
    (σ : Equiv.Perm (Fin m)) :
    (∑ τ : Equiv.Perm (Fin m),
      ‖((Fintype.card E : ℂ) ^ m • (permutationGram E m)⁻¹ - 1) σ τ‖) ≤
      ((∏ j ∈ Finset.range m, (1 + (j : ℝ) / Fintype.card E)) - 1) /
        (1 - ((∏ j ∈ Finset.range m, (1 + (j : ℝ) / Fintype.card E)) - 1)) := by
  let A := ((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m
  let B := (Fintype.card E : ℂ) ^ m • (permutationGram E m)⁻¹
  let ε := (∏ j ∈ Finset.range m, (1 + (j : ℝ) / Fintype.card E)) - 1
  have hNc : (Fintype.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hE)
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ (pow_ne_zero _ hNc), one_smul]
    exact Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp (permutationGram_isUnit e))
  have hrow (τ : Equiv.Perm (Fin m)) : ∑ υ, ‖(A - 1) τ υ‖ = ε :=
    normalized_permutationGram_sub_one_row_product hE τ
  have hε0 : 0 ≤ ε := by
    rw [← hrow σ]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact inverse_error_row_bound A B hBA hε0 hsmall (fun τ => (hrow τ).le) σ

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.scaled_inverse_permutationGram_row_bound
