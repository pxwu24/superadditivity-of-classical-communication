import StrongConvergence.StrongConvergenceGenusCoefficients
import StrongConvergence.StrongConvergenceCanonicalConcentration
import StrongConvergence.StrongConvergenceSpectralLimitLaw
import StrongConvergence.StrongConvergenceSmoothSpectralTests

/-! The deterministic limit law and almost-sure weak convergence of the
actual canonical compression ensemble, constructed from its proved moments. -/
open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar StrongConvergenceMoments

/-- The actual almost-sure moment limit, including the zeroth moment. -/
theorem ae_normalizedTrace_tendsto_genus {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ) :
    ∀ᵐ ω ∂probability k, ∀ j : ℕ, Tendsto
      (fun n => (1/((n+1:ℕ):ℝ)) *
        (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^j)).re)
      atTop (𝓝 ((normalizedMomentCoefficient k j a 0).eval t)) := by
  filter_upwards [ae_compressionMoment_tendsto_genus hk ht0 ht1 a] with ω hω
  intro j
  cases j with
  | zero =>
    have hz (n : ℕ) : (1/((n+1:ℕ):ℝ)) *
        (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^0)).re = 1 := by
      rw [← spectralTest_power]
      simp [spectralTest]
    simpa only [hz, normalizedMomentCoefficient, if_true, Polynomial.eval_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  | succ j =>
    simpa only [normalizedMomentCoefficient, Nat.succ_ne_zero, if_false,
      Nat.cast_add, Nat.cast_one, one_div, div_eq_mul_inv, mul_comm, one_mul] using hω j

/-- The genus-zero moments determine an actual compact probability measure,
and the canonical empirical spectra converge to it on one full-measure event
valid simultaneously for all continuous functions on the spectral interval. -/
theorem exists_canonical_spectral_limit {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ᵐ x ∂ν, x ∈ Icc (-(∑ i, |a i|)) (∑ i, |a i|)) ∧
      (∀ j : ℕ, ∫ x, x^j ∂ν = (normalizedMomentCoefficient k j a 0).eval t) ∧
      (∀ᵐ ω ∂probability k, ∀ f : ℝ → ℝ,
        ContinuousOn f (Icc (-(∑ i, |a i|)) (∑ i, |a i|)) →
        Tendsto (fun n => (1/((n+1:ℕ):ℝ))*∑ i,
          f ((compressionHermitian k t a ω n).eigenvalues i))
          atTop (𝓝 (∫ x, f x ∂ν))) := by
  apply exists_spectral_limit_of_ae_trace_moments (probability k)
    (fun n => n+1) (fun n => Nat.succ_pos n)
    (fun ω n => blockCompression (diagonalBlock (projection k t ω n)) a)
    (compressionHermitian k t a)
    (Finset.sum_nonneg (fun i _ => abs_nonneg (a i)))
  · exact Eventually.of_forall fun ω n => StrongConvergence.projection_compression_norm_le _
      (projection_isHermitian k t ω n) (projection_idempotent k t ω n) a
  · exact ae_all_iff.mp (ae_normalizedTrace_tendsto_genus hk ht0 ht1 a)

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.ae_normalizedTrace_tendsto_genus
#print axioms ProjectionChannels.Canonical.exists_canonical_spectral_limit
