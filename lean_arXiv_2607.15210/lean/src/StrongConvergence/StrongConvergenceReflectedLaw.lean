import StrongConvergence.StrongConvergenceCanonicalLimitLaw
import StrongConvergence.StrongConvergenceEdgeSandwich
import StrongConvergence.StrongConvergenceEdgeSupport

/-! Reflection of the actual genus-zero law under negation of all block
weights. This lets both spectral edges use one deterministic limit law. -/
open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar StrongConvergenceMoments

lemma normalizedTrace_neg_weights (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (ω : Sample k) (n j : ℕ) :
    (1/((n+1:ℕ):ℝ)) *
      (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) (-a))^j)).re =
    (-1:ℝ)^j * ((1/((n+1:ℕ):ℝ)) *
      (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^j)).re) := by
  have hneg : blockCompression (diagonalBlock (projection k t ω n)) (-a) =
      -blockCompression (diagonalBlock (projection k t ω n)) a :=
    StrongConvergence.blockCompression_neg _ a
  rw [hneg]
  rw [show -(blockCompression (diagonalBlock (projection k t ω n)) a) =
      (-1:ℂ) • blockCompression (diagonalBlock (projection k t ω n)) a by simp]
  rw [smul_pow, Matrix.trace_smul]
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_one, ← Complex.ofReal_pow,
    smul_eq_mul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Negating all weights reflects every limiting moment. The proof uses
uniqueness of the actual almost-sure trace limits, so it also covers degree
zero without separate combinatorial conventions. -/
theorem normalizedMomentCoefficient_neg_eval {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ) (j : ℕ) :
    (normalizedMomentCoefficient k j (-a) 0).eval t =
      (-1:ℝ)^j * (normalizedMomentCoefficient k j a 0).eval t := by
  obtain ⟨ω, hpos, hneg⟩ :=
    ((ae_normalizedTrace_tendsto_genus hk ht0 ht1 a).and
      (ae_normalizedTrace_tendsto_genus hk ht0 ht1 (-a))).exists
  apply tendsto_nhds_unique (hneg j)
  convert (hpos j).const_mul ((-1:ℝ)^j) using 1
  ext n
  exact normalizedTrace_neg_weights k t a ω n j

lemma reflectedLaw_ae_mem (ν : Measure ℝ) {K : ℝ}
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (-K) K) :
    ∀ᵐ x ∂ν.map (fun y : ℝ => -y), x ∈ Icc (-K) K := by
  apply (ae_map_iff measurable_neg.aemeasurable measurableSet_Icc).mpr
  filter_upwards [hν] with x hx
  exact ⟨neg_le_neg hx.2, by linarith [hx.1]⟩

lemma reflectedLaw_moment (ν : Measure ℝ) (j : ℕ) :
    (∫ x, x^j ∂ν.map (fun y : ℝ => -y)) = (-1:ℝ)^j * ∫ x, x^j ∂ν := by
  rw [integral_map measurable_neg.aemeasurable
    (by fun_prop : Continuous (fun x : ℝ => x^j)).aestronglyMeasurable]
  have he (x : ℝ) : (-x)^j = (-1:ℝ)^j * x^j := by
    rw [neg_eq_neg_one_mul, mul_pow]
  calc
    _ = ∫ x, (-1:ℝ)^j * x^j ∂ν := integral_congr_ae (Eventually.of_forall he)
    _ = _ := integral_const_mul _ _

/-- The reflected measure has exactly the genus-zero moments for negative
weights, so all support-localization theorems may be applied to this same law. -/
theorem reflectedLaw_canonical_moments {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ)
    (ν : Measure ℝ)
    (hνmom : ∀ j : ℕ, ∫ x, x^j ∂ν = (normalizedMomentCoefficient k j a 0).eval t) :
    ∀ j : ℕ, ∫ x, x^j ∂ν.map (fun y : ℝ => -y) =
      (normalizedMomentCoefficient k j (-a) 0).eval t := by
  intro j
  rw [reflectedLaw_moment, hνmom, normalizedMomentCoefficient_neg_eval hk ht0 ht1 a j]

/-- Negative-weight empirical spectra converge to the reflection of the
positive-weight law on a single full-measure event for all continuous tests. -/
theorem ae_spectral_tests_reflectedLaw {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (-(∑ i, |a i|)) (∑ i, |a i|))
    (hνmom : ∀ j : ℕ, ∫ x, x^j ∂ν = (normalizedMomentCoefficient k j a 0).eval t) :
    ∀ᵐ ω ∂probability k, ∀ f : ℝ → ℝ,
      ContinuousOn f (Icc (-(∑ i, |a i|)) (∑ i, |a i|)) →
      Tendsto (fun n => (1/((n+1:ℕ):ℝ))*∑ i,
        f ((compressionHermitian k t (-a) ω n).eigenvalues i))
        atTop (𝓝 (∫ x, f x ∂ν.map (fun y : ℝ => -y))) := by
  letI : IsProbabilityMeasure (ν.map (fun y : ℝ => -y)) :=
    isProbabilityMeasure_map measurable_neg.aemeasurable
  apply ae_matrix_spectral_tests_of_ae_trace_moments (probability k)
    (fun n => n+1) (fun n => Nat.succ_pos n)
    (fun ω n => blockCompression (diagonalBlock (projection k t ω n)) (-a))
    (compressionHermitian k t (-a)) (ν.map (fun y : ℝ => -y))
  · exact Eventually.of_forall fun ω n => by
      simpa only [Pi.neg_apply, abs_neg] using StrongConvergence.projection_compression_norm_le _
        (projection_isHermitian k t ω n) (projection_idempotent k t ω n) (-a)
  · exact reflectedLaw_ae_mem ν hν
  · intro j
    rw [reflectedLaw_canonical_moments hk ht0 ht1 a ν hνmom j]
    exact ae_all_iff.mp (ae_normalizedTrace_tendsto_genus hk ht0 ht1 (-a)) j

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.normalizedMomentCoefficient_neg_eval
#print axioms ProjectionChannels.Canonical.reflectedLaw_canonical_moments
#print axioms ProjectionChannels.Canonical.ae_spectral_tests_reflectedLaw
