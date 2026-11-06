import StrongConvergence.StrongConvergenceTensorCompressionCycles

/-! Exact factorization of the weighted permutation contractions in all-order
Haar compression moments into one power sum for each cycle. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {K : Type*} [Fintype K] [DecidableEq K] {m : ℕ}

local instance cycleClassesDecidableEq (σ : Equiv.Perm (Fin m)) :
    DecidableEq (CycleClasses σ) := Classical.decEq _

/-- The number of tensor positions in a given permutation cycle. -/
def cycleLength (σ : Equiv.Perm (Fin m)) (C : CycleClasses σ) : ℕ :=
  Fintype.card {l : Fin m // (Quotient.mk _ l : CycleClasses σ) = C}

lemma weightedCycleMoment_eq_fixedTupleSum (a : K → ℝ) (σ : Equiv.Perm (Fin m)) :
    weightedCycleMoment a σ =
      ∑ b : {b : Fin m → K // b = fun l => b (σ l)}, ∏ l, (a (b.val l) : ℂ) := by
  classical
  simp only [weightedCycleMoment,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

lemma weightedCycleMoment_eq_cycleAssignmentSum (a : K → ℝ) (σ : Equiv.Perm (Fin m)) :
    weightedCycleMoment a σ = ∑ f : CycleClasses σ → K,
      ∏ l, (a (f (Quotient.mk _ l)) : ℂ) := by
  rw [weightedCycleMoment_eq_fixedTupleSum]
  exact (Equiv.sum_comp (fixedTupleEquiv (E := K) σ).symm
    (fun b => ∏ l, (a (b.val l) : ℂ))).symm

lemma cycleAssignment_product (a : K → ℝ) (σ : Equiv.Perm (Fin m))
    (f : CycleClasses σ → K) :
    (∏ l, (a (f (Quotient.mk _ l)) : ℂ)) =
      ∏ C : CycleClasses σ, (a (f C) : ℂ)^cycleLength σ C := by
  classical
  symm
  simpa only [Finset.prod_const,Finset.card_univ,cycleLength] using
    (Fintype.prod_fiberwise' (fun l : Fin m => (Quotient.mk _ l : CycleClasses σ))
      (fun C => (a (f C) : ℂ)))

/-- Each cycle has an independent color; its contribution is the power sum of
degree equal to its length. This is the explicit scalar input in the Haar
compression moment formula. -/
theorem weightedCycleMoment_eq_product_powerSums (a : K → ℝ)
    (σ : Equiv.Perm (Fin m)) :
    weightedCycleMoment a σ =
      ∏ C : CycleClasses σ, ∑ i : K, (a i : ℂ)^cycleLength σ C := by
  classical
  rw [weightedCycleMoment_eq_cycleAssignmentSum]
  simp_rw [cycleAssignment_product]
  exact (Fintype.prod_sum (fun C (i : K) => (a i : ℂ)^cycleLength σ C)).symm

#print axioms weightedCycleMoment_eq_product_powerSums

end ProjectionChannels.TensorHaar
