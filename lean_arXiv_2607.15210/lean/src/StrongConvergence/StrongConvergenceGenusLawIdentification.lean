import StrongConvergence.StrongConvergenceGenusFreeScaling
import StrongConvergence.StrongConvergenceFreeIntervalLaw
import StrongConvergence.StrongConvergenceFreeRecurrence
import StrongConvergence.StrongConvergenceInverseGerm

/-! Identification of the actual genus-zero moments with the compact Bernoulli
free-sum law. All permutation-interval and formal-series inputs are proved. -/

open Equiv Equiv.Perm PowerSeries MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.FreeMoments
open FreeCumulant TensorHaar

/-- The concrete noncrossing permutation sum for Bernoulli cumulants has the
Bernoulli moments, by uniqueness of the verified formal cumulant equation. -/
theorem freeMoment_bernoulli (t : ℝ) (n : ℕ) :
    freeMoment (bernoulliCumulant t) n = if n = 0 then 1 else t := by
  have hformal := freeMoment_formal_identity (bernoulliCumulant t) (by simp)
  rw [← bernoulliCumulantSeries_eq_mk] at hformal
  have hseries := bernoulliMomentSeries_unique t (PowerSeries.mk (freeMoment (bernoulliCumulant t)))
    (by simp [freeMoment_zero]) hformal
  have h := congrArg (PowerSeries.coeff ℝ n) hseries
  simpa only [PowerSeries.coeff_mk, bernoulliMomentSeries] using h

/-- The full Bernoulli interval identity, on any finite type. -/
theorem weightedInterval_bernoulli {α : Type*} [Fintype α] (t : ℝ) (σ : Perm α) :
    weightedInterval (bernoulliCumulant t) σ = t ^ orbitCount σ := by
  apply weightedInterval_eq_pow_of_fullCycle
  intro n hn
  exact (freeMoment_bernoulli t n).trans (if_neg hn.ne')

end ProjectionChannels.FreeMoments
namespace ProjectionChannels.TensorHaar
open FreeCumulant FreeMoments

/-- Every genus-zero normalized moment, including order zero, is the free
moment of the precisely scaled Bernoulli cumulants. -/
theorem normalizedMomentCoefficient_zero_eq_freeMoment
    {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ) (t : ℝ) (m : ℕ) :
    (normalizedMomentCoefficient k m a 0).eval t =
      freeMoment (compressionCumulant a (bernoulliCumulant t)) m := by
  cases m with
  | zero => simp [normalizedMomentCoefficient, freeMoment_zero]
  | succ m =>
    simp only [normalizedMomentCoefficient, Nat.succ_ne_zero, if_false]
    exact genusRankCoefficient_zero_eq_weightedInterval hk (Nat.succ_pos m) a t
      (bernoulliCumulant t) (fun σ => by simpa using weightedInterval_bernoulli t σ)

lemma mk_compressionCumulant_eq_freeSum {k : ℕ} (a : Fin k → ℝ) (t : ℝ) :
    PowerSeries.mk (compressionCumulant a (bernoulliCumulant t)) = freeSumCumulantSeries k t a := by
  ext r
  simp only [PowerSeries.coeff_mk, coeff_freeSumCumulantSeries, compressionCumulant]

end ProjectionChannels.TensorHaar
namespace ProjectionChannels
open TensorHaar FreeMoments FreeCumulant

/-- A compact probability measure with the actual genus-zero moment sequence
is the Bernoulli free-sum law required by block-modified strong convergence. -/
theorem isBernoulliFreeSumLaw_of_genus_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {k : ℕ} {t K : ℝ} {a : Fin k → ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (hs : ∀ᵐ y ∂ν, |y| ≤ K)
    (hmom : ∀ m : ℕ, (∫ y, y^m ∂ν) = (normalizedMomentCoefficient k m a 0).eval t) :
    IsBernoulliFreeSumLaw k t a ν := by
  have hM : lawMomentSeries ν = PowerSeries.mk
      (freeMoment (compressionCumulant a (bernoulliCumulant t))) := by
    ext m
    rw [coeff_lawMomentSeries, PowerSeries.coeff_mk, hmom,
      normalizedMomentCoefficient_zero_eq_freeMoment hk]
  have hzero : compressionCumulant a (bernoulliCumulant t) 0 = 0 := by
    simp [compressionCumulant]
  have hformal := freeMoment_formal_identity (compressionCumulant a (bernoulliCumulant t)) hzero
  apply isBernoulliFreeSumLaw_of_formal_identity ν ht0 ht1 hK hs
  simpa only [hM, mk_compressionCumulant_eq_freeSum] using hformal

#print axioms isBernoulliFreeSumLaw_of_genus_moments
end ProjectionChannels
