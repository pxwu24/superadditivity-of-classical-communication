import StrongConvergence.StrongConvergenceProbability
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Upgrading vanishing outlier probability using concentration

A vanishing upper-tail probability alone is not summable. If deviations from
some deterministic centers are summable, the centers themselves have the same
limiting upper bound, and Borel--Cantelli gives an almost-sure upper bound.
Neither independence nor measurability of the events is required.
The estimates must still be established for the Haar ensemble.
-/
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace StrongConvergenceProbability

/-- Two small exceptional events force the deterministic center below the edge. -/
theorem center_lt_of_small_upper_and_centered_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (center L ε : ℝ)
    (hu : μ {ω | L + ε / 2 ≤ F ω} < 1 / 2)
    (hc : μ {ω | ε / 2 ≤ |F ω - center|} < 1 / 2) :
    center < L + ε := by
  by_contra h
  have hcenter : L + ε ≤ center := le_of_not_gt h
  have hcover : (Set.univ : Set Ω) ⊆
      {ω | L + ε / 2 ≤ F ω} ∪ {ω | ε / 2 ≤ |F ω - center|} := by
    intro ω _
    by_cases hω : L + ε / 2 ≤ F ω
    · exact Or.inl hω
    · right
      have habs := neg_le_abs (F ω - center)
      have hf : F ω < L + ε / 2 := lt_of_not_ge hω
      dsimp only [Set.mem_setOf_eq]
      linarith
  have hbound := (measure_mono (μ := μ) hcover).trans (measure_union_le _ _)
  rw [measure_univ] at hbound
  have hsmall : μ {ω | L + ε / 2 ≤ F ω} +
      μ {ω | ε / 2 ≤ |F ω - center|} < (1 : ℝ≥0∞) := by
    calc
      _ < (1 : ℝ≥0∞) / 2 + 1 / 2 := ENNReal.add_lt_add hu hc
      _ = 1 := by simp only [one_div, ENNReal.inv_two_add_inv_two]
  exact (not_lt_of_ge hbound) hsmall

/-- Convergence in probability of the upper tail, together with centered
concentration in probability, bounds the centers. -/
theorem eventually_center_lt_of_vanishing_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℕ → ℝ) (center : ℕ → ℝ) (L : ℝ)
    (hu : ∀ ε > 0, Tendsto (fun n => μ {ω | L + ε ≤ F ω n}) atTop (𝓝 0))
    (hc : ∀ ε > 0, Tendsto (fun n => μ {ω | ε ≤ |F ω n - center n|})
      atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, center n < L + ε := by
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < 1 / 2 := by norm_num
  filter_upwards [(hu (ε / 2) (by linarith)).eventually (gt_mem_nhds hhalf),
    (hc (ε / 2) (by linarith)).eventually (gt_mem_nhds hhalf)] with n hun hcn
  exact center_lt_of_small_upper_and_centered_tails μ (fun ω => F ω n)
    (center n) L ε hun hcn

/-- The polynomial method may provide only vanishing outlier probabilities;
summable centered concentration upgrades these to almost-sure upper bounds. -/
theorem ae_upper_of_vanishing_upper_and_summable_centered_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℕ → ℝ) (center : ℕ → ℝ) (L : ℝ)
    (hu : ∀ ε > 0, Tendsto (fun n => μ {ω | L + ε ≤ F ω n}) atTop (𝓝 0))
    (hc : ∀ ε > 0, (∑' n, μ {ω | ε ≤ |F ω n - center n|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, F ω n < L + ε := by
  have hcenter := eventually_center_lt_of_vanishing_tails μ F center L hu
    (fun ε hε => ENNReal.tendsto_atTop_zero_of_tsum_ne_top (hc ε hε))
  have hdev := ae_countable_tendsto_of_summable_deviations
    (ι := Unit) μ (fun ω n _ => F ω n - center n) (fun _ => (0 : ℝ)) (by
      intro _ m
      simpa only [Real.dist_eq, sub_zero] using hc (1 / ((m : ℝ) + 1)) (by positivity))
  filter_upwards [hdev] with ω hω
  intro ε hε
  have hsmall := (Metric.tendsto_atTop.mp (hω ())) (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := hsmall
  filter_upwards [hcenter (ε / 2) (by linarith), eventually_ge_atTop N] with n hcn hn
  have hd := hN n hn
  rw [Real.dist_eq, sub_zero] at hd
  have habs := le_abs_self (F ω n - center n)
  linarith

#print axioms center_lt_of_small_upper_and_centered_tails
#print axioms eventually_center_lt_of_vanishing_tails
#print axioms ae_upper_of_vanishing_upper_and_summable_centered_tails
end StrongConvergenceProbability
