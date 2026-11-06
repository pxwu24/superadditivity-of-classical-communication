import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# From summable failure probabilities to a common strong-convergence event

These are probabilistic intermediate results, not a proof of Haar strong
asymptotic freeness or of the block-modification theorem. The new input is a
summable quantitative failure bound; almost-sure convergence is derived by
Borel--Cantelli. No almost-sure convergence hypothesis is assumed. Independence
is unnecessary, and countably many norm and trace tests share one event.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace StrongConvergenceProbability

/-- Summable deviations at the countable thresholds `1/(m+1)` imply
almost-sure convergence simultaneously for a countable family of metric tests.
The events need not be separately assumed measurable: the first
Borel--Cantelli lemma applies to their outer measures. -/
theorem ae_countable_tendsto_of_summable_deviations
    {Ω ι Y : Type*} [MeasurableSpace Ω] [Countable ι] [PseudoMetricSpace Y]
    (μ : Measure Ω) (F : Ω → ℕ → ι → Y) (L : ι → Y)
    (hprob : ∀ i : ι, ∀ m : ℕ,
      (∑' n, μ {ω | 1/((m:ℝ)+1) ≤ dist (F ω n i) (L i)}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto (fun n => F ω n i) atTop (𝓝 (L i)) := by
  have hevent : ∀ᵐ ω ∂μ, ∀ i : ι, ∀ m : ℕ,
      ∀ᶠ n in atTop, dist (F ω n i) (L i) < 1/((m:ℝ)+1) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro m
    have h := ae_eventually_not_mem (hprob i m)
    simpa only [mem_setOf_eq,not_le] using h
  filter_upwards [hevent] with ω hω
  intro i
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hω i m)
  exact ⟨N,fun n hn => (hN n hn).trans hm⟩

/-- It suffices to prove explicit summable majorants for the failure
probabilities. This is the interface for concentration or high-moment bounds. -/
theorem ae_countable_tendsto_of_tail_majorants
    {Ω ι Y : Type*} [MeasurableSpace Ω] [Countable ι] [PseudoMetricSpace Y]
    (μ : Measure Ω) (F : Ω → ℕ → ι → Y) (L : ι → Y)
    (bound : ι → ℕ → ℕ → ℝ≥0∞)
    (hbound : ∀ i (m n : ℕ),
      μ {ω | 1/((m:ℝ)+1) ≤ dist (F ω n i) (L i)} ≤ bound i m n)
    (hsum : ∀ i m, (∑' n, bound i m n) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto (fun n => F ω n i) atTop (𝓝 (L i)) := by
  apply ae_countable_tendsto_of_summable_deviations μ F L
  intro i m
  exact ne_top_of_le_ne_top (hsum i m) (ENNReal.tsum_le_tsum (hbound i m))

/-- Concentration around a deterministic approximation and convergence of
that approximation are enough. In applications the centers can be expected
normalized traces or deterministic norm estimates; they are not random
almost-sure convergence assumptions. -/
theorem ae_countable_tendsto_of_centered_tails
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (F : Ω → ℕ → ι → ℝ) (center : ℕ → ι → ℝ) (L : ι → ℝ)
    (hcenter : ∀ i, Tendsto (fun n => center n i) atTop (𝓝 (L i)))
    (hprob : ∀ i : ι, ∀ m : ℕ,
      (∑' n, μ {ω | 1/((m:ℝ)+1) ≤ |F ω n i-center n i|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto (fun n => F ω n i) atTop (𝓝 (L i)) := by
  have h := ae_countable_tendsto_of_summable_deviations μ
    (fun ω n i => F ω n i-center n i) (fun _=>0) (by
      intro i m
      simpa only [Real.dist_eq,sub_zero] using hprob i m)
  filter_upwards [h] with ω hω
  intro i
  have hlim := (hω i).add (hcenter i)
  simpa only [sub_add_cancel,zero_add] using hlim

/-- Norm tests and normalized trace tests may have different quantitative
bounds; both converge on the same probability-one event. This theorem does
not assert those bounds for Haar matrices. -/
theorem ae_countable_norm_trace_of_centered_tails
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [Countable κ]
    (μ : Measure Ω)
    (normTest : Ω → ℕ → ι → ℝ) (normCenter : ℕ → ι → ℝ) (normLimit : ι → ℝ)
    (traceTest : Ω → ℕ → κ → ℝ) (traceCenter : ℕ → κ → ℝ) (traceLimit : κ → ℝ)
    (hnCenter : ∀ i, Tendsto (fun n => normCenter n i) atTop (𝓝 (normLimit i)))
    (htCenter : ∀ j, Tendsto (fun n => traceCenter n j) atTop (𝓝 (traceLimit j)))
    (hnProb : ∀ i (m : ℕ), (∑' n, μ {ω | 1/((m:ℝ)+1) ≤ |normTest ω n i-normCenter n i|}) ≠ ∞)
    (htProb : ∀ j (m : ℕ), (∑' n, μ {ω | 1/((m:ℝ)+1) ≤ |traceTest ω n j-traceCenter n j|}) ≠ ∞) :
    ∀ᵐ ω ∂μ,
      (∀ i, Tendsto (fun n => normTest ω n i) atTop (𝓝 (normLimit i))) ∧
      (∀ j, Tendsto (fun n => traceTest ω n j) atTop (𝓝 (traceLimit j))) :=
  (ae_countable_tendsto_of_centered_tails μ normTest normCenter normLimit hnCenter hnProb).and
    (ae_countable_tendsto_of_centered_tails μ traceTest traceCenter traceLimit htCenter htProb)

#print axioms ae_countable_tendsto_of_summable_deviations
#print axioms ae_countable_norm_trace_of_centered_tails
end StrongConvergenceProbability
