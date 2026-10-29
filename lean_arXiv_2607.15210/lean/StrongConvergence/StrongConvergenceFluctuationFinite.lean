import StrongConvergence.StrongConvergenceFluctuationWeights
import StrongConvergence.StrongConvergenceFourthFinite

/-! Reduction of fourth-order weighted Haar contractions to five power sums. -/

open Matrix MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {K : Type*} [Fintype K] [DecidableEq K]

def fourthRepresentative : Fin 5 → Equiv.Perm (Fin 4) :=
  ![1, Equiv.swap 0 1, twoTwoCycle,
    Equiv.swap 0 1 * Equiv.swap 1 2, finRotate 4]

def fourthWeight (a : K → ℝ) : Fin 5 → ℂ :=
  ![coefficientPowerSum a 1 ^ 4,
    coefficientPowerSum a 1 ^ 2 * coefficientPowerSum a 2,
    coefficientPowerSum a 2 ^ 2,
    coefficientPowerSum a 1 * coefficientPowerSum a 3,
    coefficientPowerSum a 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fourthRepresentative_certificate :
    ∀ σ : Equiv.Perm (Fin 4), ∃ τ : Equiv.Perm (Fin 4),
      τ.symm * σ * τ = fourthRepresentative (fourthClass σ) := by
  decide

lemma weightedCycleMoment_fourthRepresentative (a : K → ℝ) (j : Fin 5) :
    weightedCycleMoment a (fourthRepresentative j) = fourthWeight a j := by
  fin_cases j
  · exact weightedCycleMoment_identity a 4
  · exact weightedCycleMoment_swap01 a
  · exact weightedCycleMoment_twoTwoCycle a
  · exact weightedCycleMoment_threeCycle a
  · exact weightedCycleMoment_fourCycle a

theorem weightedCycleMoment_fourth (a : K → ℝ) (σ : Equiv.Perm (Fin 4)) :
    weightedCycleMoment a σ = fourthWeight a (fourthClass σ) := by
  obtain ⟨τ,hτ⟩ := fourthRepresentative_certificate σ
  rw [← weightedCycleMoment_conjugate a σ τ, hτ,
    weightedCycleMoment_fourthRepresentative]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma twoTwoCycle_fourthCycleNumber :
    ∀ σ : Equiv.Perm (Fin 4),
      fourthCycleNumber (twoTwoCycle * σ) =
        fourthCycleNumber (σ * twoTwoCycle.symm) := by decide

lemma twoTwoCycle_fourthClass : fourthClass twoTwoCycle = 2 := by decide

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.weightedCycleMoment_fourth
