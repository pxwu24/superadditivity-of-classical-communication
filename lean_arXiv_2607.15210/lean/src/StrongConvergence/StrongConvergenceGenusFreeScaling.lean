import StrongConvergence.StrongConvergenceGenusLeading
import StrongConvergence.StrongConvergenceTensorWeightedCycles

/-! The exact genus-zero normalization agrees with cycle weights of the scaled
free-sum cumulants. -/
open Equiv Equiv.Perm Polynomial
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.FreeMoments
open TensorHaar
variable {α : Type*} [Fintype α]
attribute [local instance] orbitClassesDecidableEq TensorHaar.cycleClassesDecidableEq

lemma sum_orbitSize (σ : Perm α) : (∑ q : OrbitClasses σ, orbitSize σ q) = Fintype.card α := by
  classical
  unfold orbitSize
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun x : α => (Quotient.mk _ x : OrbitClasses σ)))

lemma orbitSize_fin {m : ℕ} (σ : Perm (Fin m)) (q : OrbitClasses σ) :
    orbitSize σ q = cycleLength σ (orbitClassesFinEquiv σ q) := by
  classical
  unfold orbitSize cycleLength
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun x : Fin m =>
    (orbitClassesFinEquiv σ).injective.eq_iff.symm)

lemma cycleWeight_symm (f : ℕ → ℝ) (σ : Perm α) : cycleWeight f σ.symm = cycleWeight f σ := by
  classical
  let e : OrbitClasses σ.symm ≃ OrbitClasses σ :=
    Quotient.congrRight (fun _ _ => sameCycle_inv)
  have hsize (q : OrbitClasses σ.symm) : orbitSize σ.symm q = orbitSize σ (e q) := by
    unfold orbitSize
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x : α => e.injective.eq_iff.symm)
  exact Fintype.prod_equiv e _ _ (fun q => congrArg f (hsize q))

lemma realWeightedCycleMoment_eq_cycleWeight {k m : ℕ} (a : Fin k → ℝ) (σ : Perm (Fin m)) :
    realWeightedCycleMoment a σ = cycleWeight (fun r => ∑ i, a i ^ r) σ := by
  apply Complex.ofReal_injective
  rw [weightedCycleMoment_real, weightedCycleMoment_eq_product_powerSums]
  simp only [cycleWeight, Complex.ofReal_prod, Complex.ofReal_sum, Complex.ofReal_pow]
  exact (Fintype.prod_equiv (orbitClassesFinEquiv σ) _ _ (fun q => by rw [orbitSize_fin])).symm

/-- Cumulants with exactly the block-compression scaling used in the inverse germ. -/
def compressionCumulant {k : ℕ} (a : Fin k → ℝ) (κ : ℕ → ℝ) (r : ℕ) : ℝ :=
  (k : ℝ) * ∑ i, (a i / k)^r * κ r

lemma compressionCumulant_factor {k : ℕ} (a : Fin k → ℝ) (κ : ℕ → ℝ) (r : ℕ) :
    compressionCumulant a κ r =
      (k : ℝ) * (k : ℝ)⁻¹^r * (∑ i, a i ^ r) * κ r := by
  simp only [compressionCumulant, div_eq_mul_inv, mul_pow]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

lemma cycleWeight_compressionCumulant {k m : ℕ} (hk : 0 < k) (a : Fin k → ℝ)
    (κ : ℕ → ℝ) (σ : Perm (Fin m)) :
    cycleWeight (compressionCumulant a κ) σ =
      (k : ℝ)⁻¹ ^ permutationLength σ * realWeightedCycleMoment a σ * cycleWeight κ σ := by
  classical
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hscale : (k : ℝ)^cycleCount σ * (k : ℝ)⁻¹^m = (k : ℝ)⁻¹^permutationLength σ := by
    rw [permutationLength, inv_pow, inv_pow]
    have hp : (k : ℝ)^(m-cycleCount σ) * (k : ℝ)^cycleCount σ = (k : ℝ)^m := by
      rw [← pow_add, Nat.sub_add_cancel (cycleCount_le σ)]
    field_simp
    simpa only [mul_comm] using hp
  rw [realWeightedCycleMoment_eq_cycleWeight]
  simp only [cycleWeight, compressionCumulant_factor, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Finset.prod_pow_eq_pow_sum, sum_orbitSize,
    Fintype.card_fin]
  rw [show Fintype.card (OrbitClasses σ) = cycleCount σ from orbitCount_fin σ]
  change (k : ℝ)^cycleCount σ * (k : ℝ)⁻¹^m * _ * _ = _
  rw [hscale]

end ProjectionChannels.FreeMoments
namespace ProjectionChannels.TensorHaar
open FreeMoments
variable {k m : ℕ}
local instance (σ τ : Perm (Fin m)) : Decidable (PermutationAbsoluteLE σ τ) := Classical.propDecidable _

lemma genusWeight_geodesic (a : Fin k → ℝ) {σ : Perm (Fin m)}
    (hσ : permutationLength σ + permutationLength (finRotate m * σ) = m-1) :
    genusWeight a σ = (k : ℝ)⁻¹ ^ permutationLength σ * realWeightedCycleMoment a σ := by
  unfold genusWeight
  congr 1
  congr 1
  unfold permutationLength at hσ ⊢
  have hcycle := cycleCount_le (finRotate m * σ)
  omega

/-- E4.3: the leading rank polynomial is the moment-cumulant sum with the exact
`k * ∑ᵢ (aᵢ/k)^r` scaling of the target Bernoulli free sum. -/
theorem genusRankCoefficient_zero_eq_weightedInterval
    (hk : 0 < k) (hm : 0 < m) (a : Fin k → ℝ) (s : ℝ) (κ : ℕ → ℝ)
    (hκ : ∀ σ : Perm (Fin m), weightedInterval κ σ = s ^ cycleCount σ) :
    (genusRankCoefficient k m a 0).eval s =
      weightedInterval (compressionCumulant a κ) (finRotate m) := by
  classical
  rw [genusRankCoefficient_eval_base hm, genusMomentPolynomial_constantTerm hm]
  simp only [zero_add]
  have hlead := projectionLeadingCoefficient_eq_cycleWeight s κ hκ
  have heq : (∑ σ : Perm (Fin m),
        if permutationLength σ + permutationLength (finRotate m * σ) = m-1 then
          genusWeight a σ * (polynomialProjectionCoefficients m s (m-1) σ).coeff
            (permutationLength σ) else 0) =
      ∑ σ : Perm (Fin m), if PermutationAbsoluteLE σ.symm (finRotate m) then
        cycleWeight (compressionCumulant a κ) σ else 0 := by
    apply Finset.sum_congr rfl
    intro σ _
    simp only [← permutationLength_add_finRotate_mul_eq_iff hm]
    split_ifs with hgeo
    · rw [← projectionLeadingCoefficient_eq s σ (m-1) (permutationLength_le_pred hm σ),
        congrFun hlead σ, genusWeight_geodesic a hgeo, ← cycleWeight_compressionCumulant hk]
    · rfl
  rw [heq]
  have hinv := Equiv.sum_comp (Equiv.inv (Perm (Fin m)))
    (fun σ : Perm (Fin m) => if PermutationAbsoluteLE σ (finRotate m) then
      cycleWeight (compressionCumulant a κ) σ else 0)
  simp only [Equiv.inv_apply, ← permutation_symm_eq_inv, cycleWeight_symm] at hinv
  rw [hinv]
  unfold weightedInterval
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp [absoluteLE_fin]) _

#print axioms cycleWeight_compressionCumulant
#print axioms genusRankCoefficient_zero_eq_weightedInterval
end ProjectionChannels.TensorHaar
