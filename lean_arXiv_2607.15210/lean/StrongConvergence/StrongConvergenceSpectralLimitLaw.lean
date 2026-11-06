import StrongConvergence.StrongConvergenceMomentLaw
import StrongConvergence.StrongConvergenceMomentMatrices

/-! Construction of a deterministic compact spectral law from almost-sure
matrix moments, with a single full-measure event for all continuous tests. -/
open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergenceMoments

/-- A countable intersection over moments supplies one sample from which the
Riesz representation theorem constructs the deterministic limit measure.
Every sample with the same moment limits then has the same weak limit. -/
theorem exists_spectral_limit_of_ae_trace_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (M : Ω → (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hM : ∀ ω n, (M ω n).IsHermitian)
    {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ᵐ ω ∂μ, ∀ n, ‖M ω n‖ ≤ R)
    (mom : ℕ → ℝ)
    (hmom : ∀ j : ℕ, ∀ᵐ ω ∂μ, Tendsto
      (fun n => (1/(d n:ℝ))*(Matrix.trace ((M ω n)^j)).re)
      atTop (𝓝 (mom j))) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ᵐ x ∂ν, x ∈ Icc (-R) R) ∧
      (∀ j : ℕ, ∫ x, x^j ∂ν = mom j) ∧
      (∀ᵐ ω ∂μ, ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-R) R) →
        Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM ω n).eigenvalues i))
          atTop (𝓝 (∫ x, f x ∂ν))) := by
  letI (n : ℕ) : NeZero (d n) := ⟨(hd n).ne'⟩
  have hcommon : ∀ᵐ ω ∂μ, ∀ j : ℕ, Tendsto
      (fun n => (1/(d n:ℝ))*(Matrix.trace ((M ω n)^j)).re)
      atTop (𝓝 (mom j)) := ae_all_iff.mpr hmom
  obtain ⟨ω₀, hωbound, hωmom⟩ := (hbound.and hcommon).exists
  let σ : ℕ → Measure ℝ := fun n => empiricalSpectralMeasure (M ω₀ n) (hM ω₀ n)
  have hσ : ∀ n, ∀ᵐ x ∂σ n, x ∈ Icc (-R) R := fun n =>
    empiricalSpectralMeasure_ae_mem_of_norm_le _ _ (hωbound n)
  have hσmom : ∀ j, Tendsto (fun n => ∫ x, x^j ∂σ n) atTop (𝓝 (mom j)) := by
    intro j
    simpa only [σ, empiricalSpectralMeasure_moment, Fintype.card_fin] using hωmom j
  obtain ⟨ν, hνprob, hν, hνmom⟩ := exists_compact_probability_of_moments σ hσ mom hσmom
    (by linarith : -R ≤ R)
  letI := hνprob
  refine ⟨ν, hνprob, hν, hνmom, ?_⟩
  apply ae_matrix_spectral_tests_of_ae_trace_moments μ d hd M hM ν hbound hν
  intro j
  rw [hνmom j]
  exact hmom j

end StrongConvergenceMoments

#print axioms StrongConvergenceMoments.exists_spectral_limit_of_ae_trace_moments
