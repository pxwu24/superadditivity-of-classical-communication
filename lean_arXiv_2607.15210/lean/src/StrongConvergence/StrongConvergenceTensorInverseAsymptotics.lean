import StrongConvergence.StrongConvergenceTensorInverseBound
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Arbitrary-order inverse-Gram expansions

The first inverse-Gram estimate controls only the difference from the identity.
Here the inverse is compared with every finite Neumann polynomial, with an
explicit remainder.  This is a finite-dimensional estimate; it does not assert
strong convergence or identify the limiting free law.
-/

open Matrix Filter
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.TensorHaar

section General
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
local instance : NormedRing (Matrix I I ℂ) := Matrix.linftyOpNormedRing

/-- The exact finite Neumann expansion, requiring only a left inverse. -/
theorem inverse_neumann_remainder (A B : Matrix I I ℂ) (hBA : B * A = 1)
    (q : ℕ) :
    B - ∑ j ∈ Finset.range q, (1 - A) ^ j = B * (1 - A) ^ q := by
  have hid : B - 1 = B * (1 - A) := by rw [mul_sub, mul_one, hBA]
  induction q with
  | zero => simp
  | succ q ih =>
    calc
      B - ∑ j ∈ Finset.range (q+1), (1 - A) ^ j =
          (B - ∑ j ∈ Finset.range q, (1 - A) ^ j) - (1 - A) ^ q := by
            rw [Finset.sum_range_succ, sub_sub]
      _ = B * (1 - A) ^ q - 1 * (1 - A) ^ q := by rw [ih, one_mul]
      _ = (B - 1) * (1 - A) ^ q := (sub_mul _ _ _).symm
      _ = B * (1 - A) ^ (q+1) := by rw [hid, mul_assoc, pow_succ']

/-- A bound on the inverse itself, in the maximum absolute row-sum norm. -/
theorem inverse_norm_le_of_row_error (A B : Matrix I I ℂ) (hBA : B * A = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hrow : ∀ i, ∑ j, ‖(A - 1) i j‖ ≤ ε) :
    ‖B‖ ≤ 1 / (1 - ε) := by
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  have hb : ‖B - 1‖ ≤ ε / (1 - ε) :=
    linfty_norm_le_of_row_bounds _ (div_nonneg hε0 hden.le)
      (inverse_error_row_bound A B hBA hε0 hε1 hrow)
  calc
    ‖B‖ ≤ ‖B - 1‖ + 1 := by
      simpa using norm_add_le (B - 1) (1 : Matrix I I ℂ)
    _ ≤ ε / (1 - ε) + 1 := add_le_add_right hb 1
    _ = 1 / (1 - ε) := by field_simp

/-- Arbitrary-order error control for the finite Neumann expansion. -/
theorem inverse_neumann_row_bound (A B : Matrix I I ℂ) (hBA : B * A = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hrow : ∀ i, ∑ j, ‖(A - 1) i j‖ ≤ ε) (q : ℕ) (i : I) :
    (∑ j, ‖(B - ∑ l ∈ Finset.range q, (1 - A) ^ l) i j‖) ≤
      ε ^ q / (1 - ε) := by
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  have hnorm : ‖1 - A‖ ≤ ε := by
    rw [norm_sub_rev]
    exact linfty_norm_le_of_row_bounds _ hε0 hrow
  have hpower : ‖(1 - A) ^ q‖ ≤ ε ^ q :=
    (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hnorm _)
  calc
    _ ≤ ‖B - ∑ l ∈ Finset.range q, (1 - A) ^ l‖ :=
      row_sum_le_linfty_norm _ i
    _ = ‖B * (1 - A) ^ q‖ := by rw [inverse_neumann_remainder A B hBA]
    _ ≤ ‖B‖ * ‖(1 - A) ^ q‖ := norm_mul_le _ _
    _ ≤ (1 / (1 - ε)) * ε ^ q :=
      mul_le_mul (inverse_norm_le_of_row_error A B hBA hε0 hε1 hrow)
        hpower (norm_nonneg _) (div_nonneg zero_le_one hden.le)
    _ = ε ^ q / (1 - ε) := by ring

end General

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

/-- The normalized finite Haar Gram matrix admits Neumann approximations of
every order.  Retaining more terms yields the additional inverse-dimension
orders needed before the compression trace factors are applied. -/
theorem scaled_inverse_permutationGram_neumann_row_bound
    (e : Fin m ↪ E) (hE : 0 < Fintype.card E)
    (hsmall : (∏ j ∈ Finset.range m, (1 + (j : ℝ) / Fintype.card E)) - 1 < 1)
    (q : ℕ) (σ : Equiv.Perm (Fin m)) :
    (∑ τ : Equiv.Perm (Fin m),
      ‖((Fintype.card E : ℂ) ^ m • (permutationGram E m)⁻¹ -
        ∑ l ∈ Finset.range q,
          (1 - ((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m) ^ l) σ τ‖) ≤
      ((∏ j ∈ Finset.range m, (1 + (j : ℝ) / Fintype.card E)) - 1) ^ q /
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
  exact inverse_neumann_row_bound A B hBA hε0 hsmall (fun τ => (hrow τ).le) q σ

/-- A factorial version makes the inverse-dimension order of the remainder
explicit at every fixed tensor degree. -/
theorem scaled_inverse_permutationGram_neumann_row_bound_factorial
    (e : Fin m ↪ E) (hE : 0 < Fintype.card E) (hm : 0 < m)
    (hsmall : ((m.factorial - 1 : ℕ) : ℝ) / Fintype.card E < 1)
    (q : ℕ) (σ : Equiv.Perm (Fin m)) :
    (∑ τ : Equiv.Perm (Fin m),
      ‖((Fintype.card E : ℂ) ^ m • (permutationGram E m)⁻¹ -
        ∑ l ∈ Finset.range q,
          (1 - ((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m) ^ l) σ τ‖) ≤
      (((m.factorial - 1 : ℕ) : ℝ) / Fintype.card E) ^ q /
        (1 - ((m.factorial - 1 : ℕ) : ℝ) / Fintype.card E) := by
  let A := ((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m
  let B := (Fintype.card E : ℂ) ^ m • (permutationGram E m)⁻¹
  let ε := ((m.factorial - 1 : ℕ) : ℝ) / Fintype.card E
  have hNc : (Fintype.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hE)
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ (pow_ne_zero _ hNc), one_smul]
    exact Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp (permutationGram_isUnit e))
  exact inverse_neumann_row_bound A B hBA (by positivity) hsmall
    (normalized_permutationGram_sub_one_row_bound_factorial hE hm) q σ

private lemma scaled_error_identity (N C : ℝ) (hN : N ≠ 0) (hNC : N - C ≠ 0)
    (r : ℕ) :
    N ^ r * ((C / N) ^ (r+1) / (1 - C / N)) = C ^ (r+1) / (N - C) := by
  have hd : 1 - C / N ≠ 0 := by
    rw [sub_div' hN, one_mul]
    exact div_ne_zero hNC hN
  simp only [div_pow, pow_succ]
  field_simp [hN, hNC, hd] <;> ring

/-- After retaining `r+1` Neumann terms, the error is still small after
amplification by the dimension to the power `r`.  This is the scaling needed
when dimension factors from compression traces multiply inverse-Gram entries. -/
theorem scaled_inverse_permutationGram_neumann_dimension_bound
    (e : Fin m ↪ E) (hE : 0 < Fintype.card E) (hm : 0 < m)
    (hsmall : m.factorial - 1 < Fintype.card E)
    (r : ℕ) (σ : Equiv.Perm (Fin m)) :
    (Fintype.card E : ℝ) ^ r *
      (∑ τ : Equiv.Perm (Fin m),
        ‖((Fintype.card E : ℂ) ^ m • (permutationGram E m)⁻¹ -
          ∑ l ∈ Finset.range (r+1),
            (1 - ((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m) ^ l) σ τ‖) ≤
      ((m.factorial - 1 : ℕ) : ℝ) ^ (r+1) /
        ((Fintype.card E : ℝ) - ((m.factorial - 1 : ℕ) : ℝ)) := by
  have hN : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr hE
  have hC : (((m.factorial - 1 : ℕ) : ℝ)) < Fintype.card E := by
    exact_mod_cast hsmall
  have he : ((m.factorial - 1 : ℕ) : ℝ) / Fintype.card E < 1 :=
    (div_lt_one hN).mpr hC
  have hb := mul_le_mul_of_nonneg_left
    (scaled_inverse_permutationGram_neumann_row_bound_factorial e hE hm he (r+1) σ)
    (pow_nonneg hN.le r)
  simpa only [scaled_error_identity _ _ hN.ne' (sub_pos.mpr hC).ne' r] using hb

/-- Difference between the normalized inverse Gram matrix and its first `q`
Neumann terms. -/
def inverseGramNeumannRemainder (E : Type*) [Fintype E] [DecidableEq E]
    (m q : ℕ) : Matrix (Equiv.Perm (Fin m)) (Equiv.Perm (Fin m)) ℂ :=
  (Fintype.card E : ℂ) ^ m • (permutationGram E m)⁻¹ -
    ∑ l ∈ Finset.range q,
      (1 - ((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m) ^ l

/-- A finite Neumann expansion resolves the inverse Gram matrix to every
prescribed inverse-dimension order, along an arbitrary diverging dimension
sequence. No random-matrix limit is an assumption of this theorem. -/
theorem inverseGramNeumannRemainder_scaled_tendsto
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hm : 0 < m)
    (r : ℕ) (σ : Equiv.Perm (Fin m)) :
    Tendsto (fun n => (N n : ℝ) ^ r *
      ∑ τ, ‖inverseGramNeumannRemainder (Fin (N n)) m (r+1) σ τ‖)
      atTop (𝓝 0) := by
  let C : ℝ := ((m.factorial - 1 : ℕ) : ℝ)
  have hNR : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hden : Tendsto (fun n => (N n : ℝ) - C) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-C) hNR
  have hlim : Tendsto (fun n => C ^ (r+1) / ((N n : ℝ) - C))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  have hbound : ∀ᶠ n in atTop,
      (N n : ℝ) ^ r *
        (∑ τ, ‖inverseGramNeumannRemainder (Fin (N n)) m (r+1) σ τ‖) ≤
          C ^ (r+1) / ((N n : ℝ) - C) := by
    filter_upwards [hN.eventually (eventually_ge_atTop (max m (m.factorial+1)))] with n hn
    have hmN : m ≤ N n := (le_max_left _ _).trans hn
    have hN0 : 0 < N n := hm.trans_le hmN
    have hfact : m.factorial - 1 < N n := by
      have hh := (le_max_right m (m.factorial+1)).trans hn
      omega
    let e : Fin m ↪ Fin (N n) :=
      { toFun := fun i => ⟨i.val, i.isLt.trans_le hmN⟩
        inj' := by
          intro i j h
          exact Fin.ext (congrArg (fun z : Fin (N n) => z.val) h) }
    simpa only [inverseGramNeumannRemainder, Fintype.card_fin, C] using
      scaled_inverse_permutationGram_neumann_dimension_bound e
        (by simpa using hN0) hm (by simpa using hfact) r σ
  exact squeeze_zero' (Eventually.of_forall (fun n => by positivity)) hbound hlim

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.inverse_neumann_remainder
#print axioms ProjectionChannels.TensorHaar.inverse_neumann_row_bound
#print axioms ProjectionChannels.TensorHaar.scaled_inverse_permutationGram_neumann_row_bound
#print axioms ProjectionChannels.TensorHaar.scaled_inverse_permutationGram_neumann_dimension_bound
#print axioms ProjectionChannels.TensorHaar.inverseGramNeumannRemainder_scaled_tendsto
