import BellOutput.RevisionBellLogPotential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Logarithmic trace convergence from the permitted spectral convergence

A bounded continuous clamp extension of the logarithm agrees with log on
an eventual common positive spectral interval. Thus the logarithmic test is
derived from weak spectral convergence; it is not a separate black-box input.
-/
open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace RevisionBell

/-- The logarithm extended to a bounded continuous function on the real line. -/
def clippedLog (m M x : ℝ) : ℝ := Real.log (max m (min M x))

lemma continuous_clippedLog {m M : ℝ} (hm : 0 < m) :
    Continuous (clippedLog m M) := by
  apply Continuous.log
  · fun_prop
  · intro x
    exact ne_of_gt (hm.trans_le (le_max_left _ _))

lemma clippedLog_eq_log {m M x : ℝ} (hx : x ∈ Icc m M) :
    clippedLog m M x = Real.log x := by
  simp only [clippedLog, min_eq_right hx.2, max_eq_right hx.1]

lemma clippedLog_bounded {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    ∃ C : ℝ, ∀ x : ℝ, |clippedLog m M x| ≤ C := by
  refine ⟨|Real.log m|+|Real.log M|, fun x => ?_⟩
  have hlo : m ≤ max m (min M x) := le_max_left _ _
  have hhi : max m (min M x) ≤ M := max_le hmM (min_le_left _ _)
  have hpos : 0 < max m (min M x) := hm.trans_le hlo
  have hloglo := Real.log_le_log hm hlo
  have hloghi := Real.log_le_log hpos hhi
  unfold clippedLog
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)]
  · linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]

/-- The actual empirical log average converges to the actual logarithmic
integral, whenever weak spectral convergence and a common positive spectral
interval hold. Index sets may grow arbitrarily with n. -/
theorem spectral_log_mean_tendsto_of_clipped
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (lam : ∀ n, ι n → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m M : ℝ) (hm : 0 < m)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc m M)
    (hlam : ∀ᶠ n in atTop, ∀ i, lam n i ∈ Icc m M)
    (hclip : Tendsto
      (fun n => (Fintype.card (ι n) : ℝ)⁻¹ * ∑ i, clippedLog m M (lam n i))
      atTop (𝓝 (∫ x, clippedLog m M x ∂μ))) :
    Tendsto (fun n => (Fintype.card (ι n) : ℝ)⁻¹ * ∑ i, Real.log (lam n i))
      atTop (𝓝 (∫ x, Real.log x ∂μ)) := by
  have hc := hclip
  have hi : (∫ x, clippedLog m M x ∂μ) = ∫ x, Real.log x ∂μ := by
    apply integral_congr_ae
    exact hμ.mono fun x hx => clippedLog_eq_log hx
  rw [hi] at hc
  apply hc.congr'
  filter_upwards [hlam] with n hn
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact clippedLog_eq_log (hn i)

/-- Weak spectral convergence implies the clipped-test hypothesis. -/
theorem spectral_log_mean_tendsto
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (lam : ∀ n, ι n → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m M : ℝ) (hm : 0 < m)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc m M)
    (hlam : ∀ᶠ n in atTop, ∀ i, lam n i ∈ Icc m M)
    (hweak : ∀ f : ℝ → ℝ, Continuous f →
      (∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) →
      Tendsto (fun n => (Fintype.card (ι n) : ℝ)⁻¹ * ∑ i, f (lam n i))
        atTop (𝓝 (∫ x, f x ∂μ))) :
    Tendsto (fun n => (Fintype.card (ι n) : ℝ)⁻¹ * ∑ i, Real.log (lam n i))
      atTop (𝓝 (∫ x, Real.log x ∂μ)) := by
  obtain ⟨x,hx⟩ := hμ.exists
  exact spectral_log_mean_tendsto_of_clipped lam μ m M hm hμ hlam
    (hweak (clippedLog m M) (continuous_clippedLog hm)
      (clippedLog_bounded hm (hx.1.trans hx.2)))

end RevisionBell
