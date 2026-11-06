import StrongConvergence.StrongConvergenceProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Quantitative front ends for almost-sure strong-convergence tests

Markov's inequality converts summable squared deviations into summable failure
probabilities. A second front end accepts explicit geometric concentration
bounds. These estimates are inputs to a probabilistic intermediate theorem;
this file does not claim to establish them for Haar projection polynomials.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace StrongConvergenceProbability

/-- A summable second-moment bound gives the needed Borel--Cantelli tails.
The moment is the actual nonnegative Lebesgue integral, not a surrogate. -/
theorem summable_deviations_of_second_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (center : ℕ → ℝ)
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hmoment : (∑' n, ∫⁻ ω, ENNReal.ofReal ((F n ω-center n)^2) ∂μ) ≠ ∞)
    (ε : ℝ) (hε : 0<ε) :
    (∑' n, μ {ω | ε ≤ |F n ω-center n|}) ≠ ∞ := by
  have heps : ENNReal.ofReal (ε^2)≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε))
  have hprob (n : ℕ) : μ {ω | ε ≤ |F n ω-center n|} ≤
      (∫⁻ ω, ENNReal.ofReal ((F n ω-center n)^2) ∂μ)/ENNReal.ofReal (ε^2) := by
    have hsub : {ω | ε ≤ |F n ω-center n|} ⊆
        {ω | ENNReal.ofReal (ε^2) ≤ ENNReal.ofReal ((F n ω-center n)^2)} := by
      intro ω hω
      apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mpr
      have hh := mul_self_le_mul_self hε.le hω
      simpa only [← pow_two,sq_abs] using hh
    exact (measure_mono hsub).trans (meas_ge_le_lintegral_div
      (((hF n).sub_const (center n)).pow_const 2).ennreal_ofReal heps ENNReal.ofReal_ne_top)
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hprob)
  simp only [div_eq_mul_inv,ENNReal.tsum_mul_right]
  exact ENNReal.mul_ne_top hmoment (by simpa using heps)

/-- Deterministic center convergence plus summable actual second moments
implies simultaneous almost-sure convergence for countably many tests. -/
theorem ae_countable_tendsto_of_summable_second_moments
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (F : Ω → ℕ → ι → ℝ) (center : ℕ → ι → ℝ) (L : ι → ℝ)
    (hF : ∀ n i, AEMeasurable (fun ω=>F ω n i) μ)
    (hcenter : ∀ i, Tendsto (fun n=>center n i) atTop (𝓝 (L i)))
    (hmoment : ∀ i, (∑' n, ∫⁻ ω, ENNReal.ofReal ((F ω n i-center n i)^2) ∂μ) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n=>F ω n i) atTop (𝓝 (L i)) := by
  apply ae_countable_tendsto_of_centered_tails μ F center L hcenter
  intro i m
  exact summable_deviations_of_second_moments μ (fun n ω=>F ω n i) (fun n=>center n i)
    (fun n=>hF n i) (hmoment i) _ (by positivity)

/-- Explicit summable upper bounds on second moments suffice; the bounds
may depend on the chosen polynomial or scalar trace test. -/
theorem ae_countable_tendsto_of_second_moment_majorants
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (F : Ω → ℕ → ι → ℝ) (center : ℕ → ι → ℝ) (L : ι → ℝ)
    (hF : ∀ n i, AEMeasurable (fun ω=>F ω n i) μ)
    (hcenter : ∀ i, Tendsto (fun n=>center n i) atTop (𝓝 (L i)))
    (v : ι → ℕ → ℝ≥0∞)
    (hv : ∀ i n, (∫⁻ ω, ENNReal.ofReal ((F ω n i-center n i)^2) ∂μ) ≤ v i n)
    (hsum : ∀ i, (∑' n, v i n) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n=>F ω n i) atTop (𝓝 (L i)) := by
  apply ae_countable_tendsto_of_summable_second_moments μ F center L hF hcenter
  intro i
  exact ne_top_of_le_ne_top (hsum i) (ENNReal.tsum_le_tsum (hv i))

/-- A fully explicit geometric concentration rate is summable and hence
gives simultaneous almost-sure convergence. The rate may vary with the test
and accuracy level; no uniformity across that countable family is required. -/
theorem ae_countable_tendsto_of_geometric_tails
    {Ω ι Y : Type*} [MeasurableSpace Ω] [Countable ι] [PseudoMetricSpace Y]
    (μ : Measure Ω) (F : Ω → ℕ → ι → Y) (L : ι → Y)
    (C r : ι → ℕ → ℝ)
    (hC : ∀ i m, 0≤C i m) (hr0 : ∀ i m, 0≤r i m) (hr1 : ∀ i m, r i m<1)
    (hbound : ∀ i (m n : ℕ), μ {ω | 1/((m:ℝ)+1) ≤ dist (F ω n i) (L i)} ≤
      ENNReal.ofReal (C i m*(r i m)^n)) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n=>F ω n i) atTop (𝓝 (L i)) := by
  apply ae_countable_tendsto_of_tail_majorants μ F L
    (fun i m n=>ENNReal.ofReal (C i m*(r i m)^n)) hbound
  intro i m
  have hs : Summable (fun n : ℕ => C i m*(r i m)^n) :=
    (summable_geometric_of_lt_one (hr0 i m) (hr1 i m)).mul_left (C i m)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n=>mul_nonneg (hC i m) (pow_nonneg (hr0 i m) n)) hs]
  exact ENNReal.ofReal_ne_top

#print axioms ae_countable_tendsto_of_summable_second_moments
#print axioms ae_countable_tendsto_of_geometric_tails
end StrongConvergenceProbability
