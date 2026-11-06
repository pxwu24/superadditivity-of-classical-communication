import StrongConvergence.StrongConvergenceGenusCoefficients
import StrongConvergence.StrongConvergenceFreeMoments
import Mathlib.Algebra.GeomSum

/-! Incidence inversion identifies the leading inverse-Gram coefficients from
an arbitrary cycle-weight family satisfying the Bernoulli interval identities. -/
open Polynomial Matrix Equiv
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar
variable {m : ℕ}
local instance (σ τ : Perm (Fin m)) : Decidable (PermutationAbsoluteLE σ τ) := Classical.propDecidable _

/-- The stable first possible coefficient of the normalized inverse-Gram solution. -/
def projectionLeadingCoefficient (s : ℝ) (σ : Perm (Fin m)) : ℝ :=
  (polynomialProjectionCoefficients m s (permutationLength σ) σ).coeff (permutationLength σ)

lemma projectionLeadingCoefficient_eq (s : ℝ) (σ : Perm (Fin m)) (L : ℕ)
    (hL : permutationLength σ ≤ L) :
    projectionLeadingCoefficient s σ =
      (polynomialProjectionCoefficients m s L σ).coeff (permutationLength σ) :=
  (polynomialProjectionCoefficients_coeff_stable s _ L hL σ).symm

lemma polynomialGramSystem_entry (σ τ : Perm (Fin m)) :
    ((1 + polynomialGramError m) σ τ) = X ^ permutationDistance σ τ := by
  classical
  by_cases h : σ = τ
  · subst τ
    simp [polynomialGramError, NeumannPolynomial.monomialMatrix]
  · simp [polynomialGramError, NeumannPolynomial.monomialMatrix, h]

lemma polynomialGramSystem_residual (s : ℝ) (L : ℕ) :
    (1 + polynomialGramError m) *ᵥ polynomialProjectionCoefficients m s L =
      rankContractionPolynomial s -
        ((-polynomialGramError m) ^ (L+1)) *ᵥ rankContractionPolynomial s := by
  rw [polynomialProjectionCoefficients, Matrix.mulVec_mulVec]
  have h := mul_neg_geom_sum (-polynomialGramError m) (L+1)
  simp only [sub_neg_eq_add] at h
  change (1 + polynomialGramError m) * NeumannPolynomial.partialInverse (polynomialGramError m) L = _ at h
  rw [h, Matrix.sub_mulVec, Matrix.one_mulVec]

lemma polynomialGramSystem_coeff (s : ℝ) (L : ℕ) (σ : Perm (Fin m)) (n : ℕ)
    (hn : n ≤ L) :
    (((1 + polynomialGramError m) *ᵥ polynomialProjectionCoefficients m s L) σ).coeff n =
      (rankContractionPolynomial s σ).coeff n := by
  have hA : ∀ i j, ((-polynomialGramError m) i j).coeff 0 = 0 := by
    intro i j
    simp only [Matrix.neg_apply, Polynomial.coeff_neg, polynomialGramError]
    rw [NeumannPolynomial.monomialMatrix_coeff_zero permutationDistance
      (fun _ _ h => permutationDistance_pos h)]
    simp
  have hz : ((((-polynomialGramError m) ^ (L+1)) *ᵥ rankContractionPolynomial s) σ).coeff n = 0 := by
    simp only [Matrix.mulVec, dotProduct, Polynomial.finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro τ _
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro uv huv
    have huv' := Finset.mem_antidiagonal.mp huv
    rw [NeumannPolynomial.pow_coeff_eq_zero_of_lt_steps _ hA (L+1) σ τ uv.1 (by omega), zero_mul]
  rw [polynomialGramSystem_residual]
  simpa only [Pi.sub_apply, Polynomial.coeff_sub, hz, sub_zero]

/-- E1.3: the leading solution is the incidence inverse of the rank moments. -/
theorem projectionLeadingCoefficient_interval_sum (s : ℝ) (σ : Perm (Fin m)) :
    (∑ τ : Perm (Fin m), if PermutationAbsoluteLE τ σ then projectionLeadingCoefficient s τ else 0) =
      s ^ cycleCount σ := by
  classical
  have h := polynomialGramSystem_coeff s m σ (permutationLength σ)
    (by unfold permutationLength; omega)
  rw [rankContractionPolynomial_coeff, if_pos rfl] at h
  simp only [Matrix.mulVec, dotProduct, Polynomial.finset_sum_coeff,
    polynomialGramSystem_entry, Polynomial.coeff_X_pow_mul'] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro τ _
  have htri := permutationLength_le_add_distance σ τ
  have hdist : permutationDistance σ τ = permutationLength (σ * τ.symm) :=
    permutationLength_mul_symm_comm τ σ
  rw [hdist]
  by_cases hle : PermutationAbsoluteLE τ σ
  · have heq : permutationLength τ + permutationLength (σ * τ.symm) = permutationLength σ := hle
    rw [if_pos hle, if_pos (by omega), show permutationLength σ - permutationLength (σ * τ.symm) =
      permutationLength τ by omega]
    exact projectionLeadingCoefficient_eq s τ m (by unfold permutationLength; omega)
  · rw [if_neg hle]
    split_ifs with hd
    · symm
      apply polynomialProjectionCoefficients_coeff_eq_zero
      rw [permutationLength_mul_symm_comm σ τ] at hd ⊢
      unfold PermutationAbsoluteLE at hle
      rw [permutationLength_mul_symm_comm σ τ] at hle
      omega
    · rfl

/-- E1.4: interval sums determine a function, by induction on absolute length. -/
theorem projection_interval_sum_injective (f g : Perm (Fin m) → ℝ)
    (h : ∀ σ, (∑ τ : Perm (Fin m), if PermutationAbsoluteLE τ σ then f τ else 0) =
      ∑ τ : Perm (Fin m), if PermutationAbsoluteLE τ σ then g τ else 0) : f = g := by
  classical
  funext σ
  induction hlen : permutationLength σ using Nat.strong_induction_on generalizing σ with
  | h n ih =>
    have hzero : (∑ τ : Perm (Fin m), if PermutationAbsoluteLE τ σ then f τ - g τ else 0) = 0 := by
      have hh := sub_eq_zero.mpr (h σ)
      rw [← Finset.sum_sub_distrib] at hh
      convert hh using 1
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs <;> simp
    have hsingle : (∑ τ : Perm (Fin m), if PermutationAbsoluteLE τ σ then f τ - g τ else 0) =
        f σ - g σ := by
      calc
        _ = if PermutationAbsoluteLE σ σ then f σ - g σ else 0 := by
          apply Finset.sum_eq_single σ
          · intro τ _ hne
            split_ifs with hle
            · have hlt := permutationLength_lt_of_absoluteLE_ne hle hne
              rw [ih (permutationLength τ) (by omega) τ rfl, sub_self]
            · rfl
          · simp
        _ = _ := by simp [permutationAbsoluteLE_refl]
    rw [hsingle] at hzero
    exact sub_eq_zero.mp hzero

/-- E4.2 conditional on the combinatorial cycle-weight interval identity. -/
theorem projectionLeadingCoefficient_eq_cycleWeight (s : ℝ) (κ : ℕ → ℝ)
    (hκ : ∀ σ : Perm (Fin m), FreeMoments.weightedInterval κ σ = s ^ cycleCount σ) :
    projectionLeadingCoefficient (m := m) s = FreeMoments.cycleWeight κ := by
  apply projection_interval_sum_injective
  intro σ
  rw [projectionLeadingCoefficient_interval_sum]
  rw [← hκ σ]
  unfold FreeMoments.weightedInterval
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp [FreeMoments.absoluteLE_fin]) _).symm

#print axioms projectionLeadingCoefficient_interval_sum
#print axioms projection_interval_sum_injective
#print axioms projectionLeadingCoefficient_eq_cycleWeight
end ProjectionChannels.TensorHaar
