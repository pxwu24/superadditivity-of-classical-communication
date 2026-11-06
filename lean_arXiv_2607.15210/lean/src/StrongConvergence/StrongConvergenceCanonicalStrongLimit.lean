import StrongConvergence.StrongConvergenceCanonicalLimitLaw
import StrongConvergence.StrongConvergenceReflectedLaw
import StrongConvergence.StrongConvergenceSmoothEdge
import StrongConvergence.StrongConvergenceCanonicalEdgeConcentration
import StrongConvergence.StrongConvergenceEdgeSupport
import StrongConvergence.StrongConvergenceRotationTransfer

/-! Strong spectral convergence of the actual canonical Haar compression.
The same compact law controls weak convergence and both spectral edges. -/
open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar

private lemma largestEigenvalue_congr_matrix {d : ℕ} [NeZero d]
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A=B) : largestEigenvalue hA=largestEigenvalue hB := by
  subst B
  rfl

/-- The compact law determined by the genus moments controls every affine
compression norm on one probability-one event. -/
theorem ae_norm_shift_tendsto_of_genus_moments {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (a : Fin k → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x∈Icc (-(∑ i, |a i|)) (∑ i, |a i|))
    (hmom : ∀ j : ℕ, ∫ x, x^j ∂ν=(normalizedMomentCoefficient k j a 0).eval t)
    (hweak : ∀ᵐ ω ∂probability k, ∀ f : ℝ → ℝ,
      ContinuousOn f (Icc (-(∑ i, |a i|)) (∑ i, |a i|)) →
      Tendsto (fun n => (1/((n+1:ℕ):ℝ))*∑ i,
        f ((compressionHermitian k t a ω n).eigenvalues i)) atTop (𝓝 (∫ x, f x ∂ν))) :
    ∀ᵐ ω ∂probability k, ∀ c : ℝ,
      Tendsto (fun n => ‖(c:ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
        blockCompression (diagonalBlock (projection k t ω n)) a‖)
        atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν))) := by
  let K : ℝ := (∑ i, |a i|)+1
  have hK : 0<K := by dsimp [K]; positivity
  have hKa : (∑ i, |a i|)≤K := by dsimp [K]; linarith
  have hsν : ∀ᵐ x ∂ν, x∈Icc (-K) K := hν.mono fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hupper := ae_largestCompression_upper_of_vanishing_probability hk ht0.le ht1 a
    (sSup (realMeasureSupport ν)) (fun ε hε =>
      upper_support_edge_measure_tendsto_zero hk ht0 ht1 a ν hK hKa hsν hmom hε)
  let νneg := ν.map (fun x : ℝ => -x)
  letI : IsProbabilityMeasure νneg := isProbabilityMeasure_map measurable_neg.aemeasurable
  have hKaneg : (∑ i, |(-a) i|)≤K := by simpa only [Pi.neg_apply, abs_neg] using hKa
  have hnegmom := reflectedLaw_canonical_moments hk ht0.le ht1 a ν hmom
  have hlower := ae_largestCompression_upper_of_vanishing_probability hk ht0.le ht1 (-a)
    (sSup (realMeasureSupport νneg)) (fun ε hε =>
      upper_support_edge_measure_tendsto_zero hk ht0 ht1 (-a) νneg hK hKaneg
        (reflectedLaw_ae_mem ν hsν) hnegmom hε)
  filter_upwards [hweak,hupper,hlower] with ω hω hu hl
  intro c
  apply StrongConvergence.tendsto_norm_shift_of_weak_and_edges
    (fun n => n+1) (fun n => Nat.succ_pos n)
    (fun n => blockCompression (diagonalBlock (projection k t ω n)) a)
    (compressionHermitian k t a ω) ν
    ⟨K,hsν.mono fun x hx => abs_le.mpr hx⟩
  · intro f hf hb
    exact hω f hf.continuousOn
  · intro ε hε
    exact (hu ε hε).mono fun n hn => hn.le
  · intro ε hε
    filter_upwards [hl ε hε] with n hn
    have heq : largestEigenvalue (compressionHermitian k t (-a) ω n) =
        largestEigenvalue (compressionHermitian k t a ω n).neg :=
      largestEigenvalue_congr_matrix _ _ (StrongConvergence.blockCompression_neg _ a)
    rw [← heq]
    exact hn.le

/-- An actual compact probability law satisfies almost-sure weak convergence
and every shifted operator-norm limit for the canonical ensemble. -/
theorem exists_canonical_strong_spectral_limit {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (a : Fin k → ℝ) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ᵐ x ∂ν, x∈Icc (-(∑ i, |a i|)) (∑ i, |a i|)) ∧
      (∀ j : ℕ, ∫ x, x^j ∂ν=(normalizedMomentCoefficient k j a 0).eval t) ∧
      (∀ᵐ ω ∂probability k, ∀ c : ℝ,
        Tendsto (fun n => ‖(c:ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
          blockCompression (diagonalBlock (projection k t ω n)) a‖)
          atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν)))) ∧
      (∀ᵐ ω ∂probability k, ∀ f : ℝ → ℝ,
        ContinuousOn f (Icc (-(∑ i, |a i|)) (∑ i, |a i|)) →
        Tendsto (fun n => (1/((n+1:ℕ):ℝ))*∑ i,
          f ((compressionHermitian k t a ω n).eigenvalues i)) atTop (𝓝 (∫ x, f x ∂ν))) := by
  obtain ⟨ν,hprob,hν,hmom,hweak⟩ := exists_canonical_spectral_limit hk ht0.le ht1 a
  letI := hprob
  exact ⟨ν,hprob,hν,hmom,ae_norm_shift_tendsto_of_genus_moments hk ht0 ht1 a ν hν hmom hweak,hweak⟩

#print axioms exists_canonical_strong_spectral_limit
end ProjectionChannels.Canonical
