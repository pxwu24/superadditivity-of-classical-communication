import StrongConvergence.StrongConvergenceProbability
import Preliminaries.PreliminariesAnalysis
import Entropy.OutputSpace

/-!
# Dense-test and compact-uniform consequences of quantitative probability bounds

The deterministic Lipschitz and finite-net arguments already available in
`Preliminaries.PreliminariesAnalysis` and `Entropy.OutputSpace` are reused. What is new is
the Borel--Cantelli input: the hypotheses are summable failure probabilities,
not pre-assumed almost-sure convergence of the random matrix tests.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace StrongConvergenceProbability

/-- Quantitative failure bounds on a countable dense set give one event
of simultaneous convergence for every real parameter. -/
theorem ae_all_tests_of_summable_dense_deviations
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (μ : Measure Ω) (s : Set X) (hcount : s.Countable) (hdense : Dense s)
    (F : Ω → ℕ → X → ℝ) (L : X → ℝ)
    (hF : ∀ ω n x y, dist (F ω n x) (F ω n y) ≤ dist x y)
    (hL : ∀ x y, dist (L x) (L y) ≤ dist x y)
    (hprob : ∀ q ∈ s, ∀ m : ℕ,
      (∑' n, μ {ω | 1/((m:ℝ)+1) ≤ |F ω n q-L q|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ x, Tendsto (fun n => F ω n x) atTop (𝓝 (L x)) := by
  letI : Countable s := hcount.to_subtype
  have hsim := ae_countable_tendsto_of_summable_deviations μ
    (fun ω n (q : s) => F ω n q) (fun q : s => L q) (by
      intro q m
      simpa only [Real.dist_eq] using hprob q q.property m)
  filter_upwards [hsim] with ω hω
  exact ProjectionChannels.convergence_of_dense_lipschitz s (F ω) L hdense (hF ω) hL
    (fun q hq => hω ⟨q,hq⟩)

/-- The same probability-one event gives uniform convergence on every
compact parameter set. No uncountable intersection over compact sets is
performed: compact uniformity is a deterministic consequence on that event. -/
theorem ae_compact_uniform_of_summable_dense_deviations
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (μ : Measure Ω) (s : Set X) (hcount : s.Countable) (hdense : Dense s)
    (F : Ω → ℕ → X → ℝ) (L : X → ℝ)
    (hF : ∀ ω n x y, dist (F ω n x) (F ω n y) ≤ dist x y)
    (hL : ∀ x y, dist (L x) (L y) ≤ dist x y)
    (hprob : ∀ q ∈ s, ∀ m : ℕ,
      (∑' n, μ {ω | 1/((m:ℝ)+1) ≤ |F ω n q-L q|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ K : Set X, IsCompact K →
      ∀ ε>0, ∃ N, ∀ n≥N, ∀ x∈K, |F ω n x-L x|<ε := by
  filter_upwards [ae_all_tests_of_summable_dense_deviations μ s hcount hdense F L hF hL hprob]
    with ω hω
  intro K hK
  exact OutputSpaceVerification.uniform_tendsto_on_compact K hK (F ω) L
    (fun n x _ y _=>hF ω n x y) (fun x _ y _=>hL x y) (fun x _=>hω x)

/-- Dense-test version with explicit concentration bounds, separating the
analytic estimate from the probabilistic conversion. -/
theorem ae_compact_uniform_of_dense_tail_majorants
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (μ : Measure Ω) (s : Set X) (hcount : s.Countable) (hdense : Dense s)
    (F : Ω → ℕ → X → ℝ) (L : X → ℝ)
    (hF : ∀ ω n x y, dist (F ω n x) (F ω n y) ≤ dist x y)
    (hL : ∀ x y, dist (L x) (L y) ≤ dist x y)
    (bound : X → ℕ → ℕ → ℝ≥0∞)
    (hbound : ∀ q∈s, ∀ (m n : ℕ),
      μ {ω | 1/((m:ℝ)+1) ≤ |F ω n q-L q|} ≤ bound q m n)
    (hsum : ∀ q∈s, ∀ m, (∑' n, bound q m n) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ K : Set X, IsCompact K →
      ∀ ε>0, ∃ N, ∀ n≥N, ∀ x∈K, |F ω n x-L x|<ε := by
  apply ae_compact_uniform_of_summable_dense_deviations μ s hcount hdense F L hF hL
  intro q hq m
  exact ne_top_of_le_ne_top (hsum q hq m) (ENNReal.tsum_le_tsum (hbound q hq m))

#print axioms ae_all_tests_of_summable_dense_deviations
#print axioms ae_compact_uniform_of_dense_tail_majorants
end StrongConvergenceProbability
