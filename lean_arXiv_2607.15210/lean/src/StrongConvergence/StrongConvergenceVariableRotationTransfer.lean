import StrongConvergence.StrongConvergenceRotationTransfer

/-! Haar output rotation for arbitrary deterministic sequences of densities. -/
open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels.Canonical

/-- It is enough to prove the norm and weak spectral limits in the original
output basis. The same deterministic law then works for every fixed output
unitary, with the probability-one event allowed to depend on the test. -/
theorem fullBlockModifiedStrongInput_of_variable_unrotated (k : ℕ) (t : ℝ) (u : ℕ → ℝ)
    (h : ∀ a : Fin k → ℝ, ∃ ν : Measure ℝ,
      IsBernoulliFreeSumLaw k t a ν ∧
      (∀ c : ℝ, ∀ᵐ ω ∂probability k,
        Tendsto (fun n => ‖(c : ℂ) • (1 : Matrix (Index k n) (Index k n) ℂ) +
          ProjectionChannelsCP.amplify (diagonalTraceLinearMap a) (projection k (u n) ω n)‖)
          atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν)))) ∧
      (∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        ∀ᵐ ω ∂probability k, Tendsto
          (fun n => (1/((n+1 : ℕ) : ℝ)) * ∑ i,
            f ((compressionHermitian k (u n) a ω n).eigenvalues i))
          atTop (𝓝 (∫ x, f x ∂ν)))) :
    FullBlockModifiedStrongInput (probability k) k t
      (fun ω n => projection k (u n) ω n) (fun ω n => projection_isHermitian k (u n) ω n) := by
  intro U a
  obtain ⟨ν, hν, hnorm, hweak⟩ := h a
  refine ⟨ν, hν, ?_, ?_⟩
  · intro c
    have h := (outputRotation_measurePreserving k U).quasiMeasurePreserving.ae (hnorm c)
    filter_upwards [h] with ω hω
    simpa only [projection_outputRotation] using hω
  · intro f hf hb
    have h := (outputRotation_measurePreserving k U).quasiMeasurePreserving.ae
      (hweak f hf hb)
    filter_upwards [h] with ω hω
    apply hω.congr'
    filter_upwards [] with n
    exact congrArg
      (fun g : Fin (n+1) → ℝ => (1/((n+1 : ℕ) : ℝ)) * ∑ i, f (g i))
      (rotatedCompression_eigenvalues k (u n) U a ω n).symm

/-- The final assembly may work entirely with the smaller block compression:
tensoring with the output identity and changing output basis cost no further
probabilistic estimates. -/
theorem fullBlockModifiedStrongInput_of_variable_compression {k : ℕ} (hk : 0 < k) (t : ℝ) (u : ℕ → ℝ)
    (h : ∀ a : Fin k → ℝ, ∃ ν : Measure ℝ,
      IsBernoulliFreeSumLaw k t a ν ∧
      (∀ c : ℝ, ∀ᵐ ω ∂probability k,
        Tendsto (fun n => ‖(c : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
          blockCompression (diagonalBlock (projection k (u n) ω n)) a‖)
          atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν)))) ∧
      (∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        ∀ᵐ ω ∂probability k, Tendsto
          (fun n => (1/((n+1 : ℕ) : ℝ)) * ∑ i,
            f ((compressionHermitian k (u n) a ω n).eigenvalues i))
          atTop (𝓝 (∫ x, f x ∂ν)))) :
    FullBlockModifiedStrongInput (probability k) k t
      (fun ω n => projection k (u n) ω n) (fun ω n => projection_isHermitian k (u n) ω n) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  apply fullBlockModifiedStrongInput_of_variable_unrotated k t u
  intro a
  obtain ⟨ν, hν, hnorm, hweak⟩ := h a
  refine ⟨ν, hν, ?_, hweak⟩
  intro c
  filter_upwards [hnorm c] with ω hω
  simpa only [norm_shift_amplified_diagonalTrace] using hω

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.fullBlockModifiedStrongInput_of_variable_compression
