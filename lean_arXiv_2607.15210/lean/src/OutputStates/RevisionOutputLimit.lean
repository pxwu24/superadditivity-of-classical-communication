import OutputStates.RevisionOutputStates
import OutputStates.RevisionOutputBody

/-!
# Assembly of the deterministic output-space limit

The actual channel image and actual limiting matrix body are used throughout.
All their geometric and support properties are proved in the dependency chain.
The only asymptotic input of `actual_output_hausdorff_from_compression` is the
unnormalized random-compression spectral limit for shifted observables.
This file uses the elementwise matrix supremum norm; conversion to the paper's
trace-norm Hausdorff distance is handled separately.
-/

open Filter Set Matrix PreliminariesMatrix ProjectionChannels OutputSpaceVerification
open scoped Topology BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- All matrix-body geometry and dual representation are included, so
only pointwise observable support convergence is required at this step. -/
theorem actual_output_hausdorff_from_support
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hP : ∀ N, (P N).PosSemidef) (hA : ∀ N, (traceB (P N)).PosDef)
    (hconv : ∀ (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.IsHermitian),
      Tendsto (fun N => outputSupport (P N) (hA N).posSemidef.sqrt⁻¹ H)
        atTop (𝓝 (normalizedBodySupport k t hH.eigenvalues))) :
    Tendsto (fun N => Metric.hausdorffDist
      (normalizedOutput (P N) (hA N).posSemidef.sqrt⁻¹ '' densityMatrices (Fin (N+1)))
      (spectralBody k t)) atTop (𝓝 0) := by
  letI : NeZero k := ⟨hk.ne'⟩
  let C : ℕ → Set (Matrix (Fin k) (Fin k) ℂ) := fun N =>
    normalizedOutput (P N) (hA N).posSemidef.sqrt⁻¹ '' densityMatrices (Fin (N+1))
  have hC : ∀ N, IsCompact (C N) := fun N => (output_image_nonempty_compact _ _).2
  have hnC : ∀ N, (C N).Nonempty := fun N => (output_image_nonempty_compact _ _).1
  have hCc : ∀ N, Convex ℝ (C N) := fun N => output_image_convex _ _
  have hCstate : ∀ N, C N ⊆ densityMatrices (Fin k) := by
    intro N X hX
    obtain ⟨ρ, hρ, rfl⟩ := hX
    exact normalizedOutput_mem_densityMatrices (P N) (hP N) (hA N) hρ
  have hKstate := spectralBody_subset_densityMatrices hk ht.le hkt
  apply hausdorffDist_tendsto_of_support_tendsto C (spectralBody k t)
    hC (isCompact_spectralBody hk ht.le hkt) hnC (spectralBody_nonempty hk ht.le ht1.le)
    hCc (convex_spectralBody hk ht ht1 hkt)
    (fun N X hX => density_norm_le_one (hCstate N hX))
    (fun X hX => density_norm_le_one (hKstate hX))
  intro f _
  let H := hermitianFunctionalMatrix f
  have hH : H.IsHermitian := hermitianFunctionalMatrix_isHermitian f
  have heqC : ∀ N, support (C N) f = outputSupport (P N) (hA N).posSemidef.sqrt⁻¹ H := by
    intro N
    unfold support outputSupport
    congr 1
    apply Set.image_congr
    intro X hX
    exact (hermitian_trace_representation f (hCstate N hX).1.isHermitian).symm
  have heqK : support (spectralBody k t) f = normalizedBodySupport k t hH.eigenvalues := by
    rw [← spectralBody_support hk ht ht1 hkt H hH]
    unfold support
    congr 1
    apply Set.image_congr
    intro X hX
    exact (hermitian_trace_representation f (hKstate hX).1.isHermitian).symm
  simpa only [heqC, heqK] using hconv H hH

/-- Deterministic sample-path form of Theorem III.1, with the sole limiting
input being unnormalized compression. The threshold, actual output support,
body support, compactness, convexity, duality, and uniformity are all proved. -/
theorem actual_output_hausdorff_from_compression
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hP : ∀ N, (P N).PosSemidef) (hA : ∀ N, (traceB (P N)).PosDef)
    (hconv : ∀ (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.IsHermitian) (z : ℝ),
      Tendsto (fun N => largestEigenvalue
        (contraction_isHermitian (hP N).isHermitian
          (real_scalar_shift_hermitian hH Matrix.isHermitian_one z)))
        atTop (𝓝 (bodySupport k t (fun i => hH.eigenvalues i - z)))) :
    Tendsto (fun N => Metric.hausdorffDist
      (normalizedOutput (P N) (hA N).posSemidef.sqrt⁻¹ '' densityMatrices (Fin (N+1)))
      (spectralBody k t)) atTop (𝓝 0) := by
  apply actual_output_hausdorff_from_support hk ht ht1 hkt P hP hA
  intro H hH
  apply concrete_normalized_support_tendsto hk ht.le ht1.le hkt hH.eigenvalues
    (fun N z => largestEigenvalue
      (contraction_isHermitian (hP N).isHermitian
        (real_scalar_shift_hermitian hH Matrix.isHermitian_one z)))
  · intro N z
    rw [normalized_output_support (P N) (hP N).isHermitian _
      (hA N).posSemidef.posSemidef_sqrt.isHermitian.inv H hH]
    have hc := inverse_sqrt_threshold (traceB (P N)) (contraction (P N) H)
      (hA N) (contraction_isHermitian (hP N).isHermitian hH) z
    simpa only [contraction_sub_scalar] using hc
  · exact hconv H hH

end
end RevisionOutput
