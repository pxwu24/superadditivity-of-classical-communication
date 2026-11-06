import StrongConvergence.StrongConvergenceProbability
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

namespace StrongConvergenceProbability

/-- Exponentially decaying real tail bounds are summable as outer measures. -/
theorem tsum_tail_ne_top_of_exponential_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : ℕ → Set Ω) {a : ℝ} (ha : 0 < a)
    (hbound : ∀ n, μ.real (E n) ≤
      2 * Real.exp (-(n : ℝ)) + 2 * Real.exp (-a*(n : ℝ))) :
    (∑' n, μ (E n)) ≠ ∞ := by
  have hs : Summable (fun n : ℕ =>
      2 * Real.exp (-(n : ℝ)) + 2 * Real.exp (-a*(n : ℝ))) := by
    apply (Real.summable_exp_neg_nat.mul_left 2).add
    have h := (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha)).mul_left 2
    simpa only [mul_comm (-a)] using h
  have hle : ∀ n, μ (E n) ≤ ENNReal.ofReal
      (2 * Real.exp (-(n : ℝ)) + 2 * Real.exp (-a*(n : ℝ))) := by
    intro n
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hle)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs]
  exact ENNReal.ofReal_ne_top

/-- Exponential concentration around deterministic centers and an
exponentially small error in those centers imply almost-sure fluctuations
about the actual means tend to zero. No independence is used. -/
theorem ae_tendsto_sub_mean_of_exponential_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℕ → ℝ) (center mean : ℕ → ℝ)
    {C α : ℝ} (hα : 0 < α)
    (hcenter : ∀ n, |center n-mean n| ≤ C*Real.exp (-(n : ℝ)))
    (htail : ∀ r : ℝ, 0 < r → ∀ n,
      μ.real {ω | r ≤ |X ω n-center n|} ≤
        2 * Real.exp (-(n : ℝ)) + 2 * Real.exp (-α*r^2*(n : ℝ))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X ω n-mean n) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => center n-mean n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => by simpa only [Real.norm_eq_abs] using hcenter n)
    simpa only [mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul C
  have hx := ae_countable_tendsto_of_summable_deviations μ
    (fun ω n (_ : Unit) => X ω n-center n) (fun _ => (0 : ℝ)) (by
      intro i m
      apply tsum_tail_ne_top_of_exponential_bound μ _ (show 0 < α*(1/((m:ℝ)+1))^2 by positivity)
      intro n
      simpa only [Real.dist_eq, sub_zero, neg_mul] using htail (1/((m:ℝ)+1)) (by positivity) n)
  filter_upwards [hx] with ω hω
  have h := (hω ()).add hc
  simpa only [sub_add_sub_cancel, add_zero] using h

end StrongConvergenceProbability

#print axioms StrongConvergenceProbability.tsum_tail_ne_top_of_exponential_bound
#print axioms StrongConvergenceProbability.ae_tendsto_sub_mean_of_exponential_tails
