import StrongConvergence.StrongConvergenceVariableConcentration
import StrongConvergence.StrongConvergenceVariableMomentLimit
import StrongConvergence.StrongConvergenceCanonicalLimitLaw

/-! Almost-sure moments and weak spectral convergence for converging density
sequences, with the same deterministic law as the fixed limiting density. -/
open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar StrongConvergenceMoments

theorem ae_variable_compressionMoment_tendsto_genus {k : ℕ} {t : ℝ} {u : ℕ → ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1) (hut : Tendsto u atTop (𝓝 t))
    (a : Fin k → ℝ) :
    ∀ᵐ ω ∂probability k, ∀ m : ℕ, Tendsto
      (fun n => (Matrix.trace ((blockCompression (diagonalBlock (projection k (u n) ω n)) a)^(m+1))).re /
        ((n:ℝ)+1)) atTop (𝓝 ((genusRankCoefficient k (m+1) a 0).eval t)) := by
  apply ae_all_iff.mpr
  intro m
  have hmean := (Complex.continuous_re.tendsto _).comp
    (expectedNormalizedMoment_variable_tendsto_genus hk hu0 hu1 hut m a)
  simp only [Complex.ofReal_re] at hmean
  filter_upwards [ae_variable_compressionMoment_sub_mean_tendsto_zero hk ht0 ht1 u hut a m]
    with ω hω
  simp_rw [integral_normalized_compressionMoment_eq_re_expected] at hω
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hω.add hmean

theorem ae_variable_normalizedTrace_tendsto_genus {k : ℕ} {t : ℝ} {u : ℕ → ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1) (hut : Tendsto u atTop (𝓝 t))
    (a : Fin k → ℝ) :
    ∀ᵐ ω ∂probability k, ∀ j : ℕ, Tendsto
      (fun n => (1/((n+1:ℕ):ℝ)) *
        (Matrix.trace ((blockCompression (diagonalBlock (projection k (u n) ω n)) a)^j)).re)
      atTop (𝓝 ((normalizedMomentCoefficient k j a 0).eval t)) := by
  filter_upwards [ae_variable_compressionMoment_tendsto_genus hk ht0 ht1 hu0 hu1 hut a] with ω hω
  intro j
  cases j with
  | zero =>
    have hz (n : ℕ) : (1/((n+1:ℕ):ℝ)) *
        (Matrix.trace ((blockCompression (diagonalBlock (projection k (u n) ω n)) a)^0)).re = 1 := by
      rw [← spectralTest_power]
      simp [spectralTest]
    simpa only [hz, normalizedMomentCoefficient, if_true, Polynomial.eval_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  | succ j =>
    simpa only [normalizedMomentCoefficient, Nat.succ_ne_zero, if_false,
      Nat.cast_add, Nat.cast_one, one_div, div_eq_mul_inv, mul_comm, one_mul] using hω j

/-- The limiting law depends only on the limiting density, not on how the
ranks approach it. The full-measure event works for all continuous tests. -/
theorem ae_variable_spectral_tests_tendsto {k : ℕ} {t : ℝ} {u : ℕ → ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1) (hut : Tendsto u atTop (𝓝 t))
    (a : Fin k → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (-(∑ i, |a i|)) (∑ i, |a i|))
    (hνmom : ∀ j : ℕ, ∫ x, x^j ∂ν = (normalizedMomentCoefficient k j a 0).eval t) :
    ∀ᵐ ω ∂probability k, ∀ f : ℝ → ℝ,
      ContinuousOn f (Icc (-(∑ i, |a i|)) (∑ i, |a i|)) →
      Tendsto (fun n => (1/((n+1:ℕ):ℝ))*∑ i,
        f ((compressionHermitian k (u n) a ω n).eigenvalues i))
        atTop (𝓝 (∫ x, f x ∂ν)) := by
  apply ae_matrix_spectral_tests_of_ae_trace_moments (probability k)
    (fun n => n+1) (fun n => Nat.succ_pos n)
    (fun ω n => blockCompression (diagonalBlock (projection k (u n) ω n)) a)
    (fun ω n => compressionHermitian k (u n) a ω n) ν
  · exact Eventually.of_forall fun ω n => StrongConvergence.projection_compression_norm_le _
      (projection_isHermitian k (u n) ω n) (projection_idempotent k (u n) ω n) a
  · exact hν
  · intro j
    rw [hνmom j]
    exact ae_all_iff.mp (ae_variable_normalizedTrace_tendsto_genus hk ht0 ht1 hu0 hu1 hut a) j

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.ae_variable_normalizedTrace_tendsto_genus
#print axioms ProjectionChannels.Canonical.ae_variable_spectral_tests_tendsto
