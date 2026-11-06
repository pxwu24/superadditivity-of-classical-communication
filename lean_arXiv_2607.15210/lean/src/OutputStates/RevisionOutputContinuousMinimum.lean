import OutputStates.RevisionOutputMetricComparison
import OutputStates.RevisionEntropyHausdorff

/-! Continuous objectives on the actual channel output sets. Eventual
normalization is obtained from the single permitted strong-convergence input. -/

open MeasureTheory Filter Set Matrix Metric PreliminariesMatrix ProjectionChannels
open scoped Topology BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Canonical strong convergence gives genuine density outputs eventually. -/
theorem ae_eventually_output_density
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hStrong : FullBlockModifiedStrongInput μ k t P hH) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop,
      normalizedOutput (P ω N)
        (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))) ''
          densityMatrices (Fin (N+1)) ⊆ densityMatrices (Fin k) := by
  have hbase : AmplifiedBlockModifiedStrongInput μ k t P := by
    simpa only [Matrix.UnitaryGroup.one_val,localConjugate_one] using hStrong.to_amplified 1
  filter_upwards [ae_eventually_marginal_posDef μ hk ht ht1 hkt P hH hId hbase] with ω hω
  filter_upwards [hω] with N hN
  rintro _ ⟨ρ,hρ,rfl⟩
  exact normalizedOutput_mem_densityMatrices _
    (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N)) hN hρ

/-- Actual minimum values converge for every continuous function on density
matrices; matrix Rényi entropy is an application of this theorem. -/
theorem output_continuous_minimum_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hStrong : FullBlockModifiedStrongInput μ k t P hH)
    (F : Matrix (Fin k) (Fin k) ℂ → ℝ)
    (hF : ContinuousOn F (densityMatrices (Fin k))) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => sInf (F ''
      (normalizedOutput (P ω N)
        (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))) ''
          densityMatrices (Fin (N+1))))) atTop (𝓝 (sInf (F '' spectralBody k t))) := by
  have hhaus := output_space_metric_limit μ hk ht ht1 hkt P hH hId hStrong
  have hdomain := ae_eventually_output_density μ hk ht ht1 hkt P hH hId hStrong
  filter_upwards [hhaus,hdomain] with ω hω hD
  exact OutputSpaceVerification.minimum_value_tendsto_of_hausdorff_eventually
    (densityMatrices (Fin k)) (spectralBody k t) _ F
    (isCompact_spectralBody hk ht.le hkt) (spectralBody_nonempty hk ht.le ht1.le)
    (fun N => (output_image_nonempty_compact _ _).2)
    (fun N => (output_image_nonempty_compact _ _).1)
    (spectralBody_subset_densityMatrices hk ht.le hkt) hD
    (isCompact_densityMatrices.uniformContinuousOn_of_continuous hF) hω

#print axioms output_continuous_minimum_limit
end
end RevisionOutput
