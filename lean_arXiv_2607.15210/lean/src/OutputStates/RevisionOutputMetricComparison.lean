import OutputStates.RevisionOutputTheorem
import OutputStates.RevisionOutputTraceGeometry

/-! The trace-norm limit also gives the ordinary finite-dimensional metric
Hausdorff limit, used by the entropy-continuity corollary. -/

open MeasureTheory Filter Set Matrix Metric PreliminariesMatrix ProjectionChannels
open scoped Topology BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

lemma trace_cost_directed_bddAbove (C K : Set (Matrix A A ℂ))
    (hC : IsCompact C) (hK : IsCompact K) (hneC : C.Nonempty) (hneK : K.Nonempty) :
    BddAbove ((fun X => sInf ((fun Y => hermitianTraceNorm (X-Y)) '' K)) '' C) ∧
    BddAbove ((fun Y => sInf ((fun X => hermitianTraceNorm (X-Y)) '' C)) '' K) := by
  let R := (Fintype.card A : ℝ)^3 * diam (C ∪ K)
  have hbound : ∀ X ∈ C, ∀ Y ∈ K, hermitianTraceNorm (X-Y) ≤ R := by
    intro X hX Y hY
    apply (hermitianTraceNorm_le (X-Y)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← dist_eq_norm]
    exact dist_le_diam_of_mem (hC.union hK).isBounded (Or.inl hX) (Or.inr hY)
  have hlower (X : Matrix A A ℂ) : BddBelow ((fun Y => hermitianTraceNorm (X-Y)) '' K) :=
    ⟨0, by rintro _ ⟨Y, _, rfl⟩; exact hermitianTraceNorm_nonneg _⟩
  have hlower' (Y : Matrix A A ℂ) : BddBelow ((fun X => hermitianTraceNorm (X-Y)) '' C) :=
    ⟨0, by rintro _ ⟨X, _, rfl⟩; exact hermitianTraceNorm_nonneg _⟩
  constructor
  · refine ⟨R, ?_⟩
    rintro _ ⟨X, hX, rfl⟩
    obtain ⟨Y, hY⟩ := hneK
    exact (csInf_le (hlower X) ⟨Y, hY, rfl⟩).trans (hbound X hX Y hY)
  · refine ⟨R, ?_⟩
    rintro _ ⟨Y, hY, rfl⟩
    obtain ⟨X, hX⟩ := hneC
    exact (csInf_le (hlower' Y) ⟨X, hX, rfl⟩).trans (hbound X hX Y hY)

lemma hausdorffDist_le_traceHausdorff (C K : Set (Matrix A A ℂ))
    (hC : IsCompact C) (hK : IsCompact K) (hneC : C.Nonempty) (hneK : K.Nonempty)
    (hHC : ∀ X ∈ C, X.IsHermitian) (hHK : ∀ Y ∈ K, Y.IsHermitian) :
    hausdorffDist C K ≤ traceHausdorff C K := by
  have hb := trace_cost_directed_bddAbove C K hC hK hneC hneK
  apply hausdorffDist_le_of_infDist (traceHausdorff_comparison C K hC hK hneC hneK).1
  · intro X hX
    have hl : infDist X K ≤ sInf ((fun Y => hermitianTraceNorm (X-Y)) '' K) := by
      apply le_csInf (hneK.image _)
      rintro _ ⟨Y, hY, rfl⟩
      exact (infDist_le_dist_of_mem hY).trans (by
        simpa only [dist_eq_norm] using norm_le_hermitianTraceNorm (X-Y) ((hHC X hX).sub (hHK Y hY)))
    exact hl.trans ((le_csSup hb.1 ⟨X, hX, rfl⟩).trans (le_max_left _ _))
  · intro Y hY
    have hl : infDist Y C ≤ sInf ((fun X => hermitianTraceNorm (X-Y)) '' C) := by
      apply le_csInf (hneC.image _)
      rintro _ ⟨X, hX, rfl⟩
      exact (infDist_le_dist_of_mem hX).trans (by
        rw [dist_comm, dist_eq_norm]
        exact norm_le_hermitianTraceNorm (X-Y) ((hHC X hX).sub (hHK Y hY)))
    exact hl.trans ((le_csSup hb.2 ⟨Y, hY, rfl⟩).trans (le_max_right _ _))

/-- Canonical input, ordinary matrix metric version of Theorem III.1.
This is the interface for continuous matrix entropy minimization. -/
theorem output_space_metric_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hStrong : FullBlockModifiedStrongInput μ k t P hH) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => hausdorffDist
      (normalizedOutput (P ω N)
        (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))) ''
          densityMatrices (Fin (N+1))) (spectralBody k t)) atTop (𝓝 0) := by
  have hh := output_space_limit μ hk ht ht1 hkt P hH hId hStrong
  filter_upwards [hh] with ω hω
  have hb : ∀ N, hausdorffDist
      (normalizedOutput (P ω N)
        (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))) ''
          densityMatrices (Fin (N+1))) (spectralBody k t) ≤ traceHausdorff
      (normalizedOutput (P ω N)
        (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))) ''
          densityMatrices (Fin (N+1))) (spectralBody k t) := by
    intro N
    apply hausdorffDist_le_traceHausdorff _ _
      (output_image_nonempty_compact _ _).2 (isCompact_spectralBody hk ht.le hkt)
      (output_image_nonempty_compact _ _).1 (spectralBody_nonempty hk ht.le ht1.le)
    · rintro X ⟨ρ, hρ, rfl⟩
      exact (raw_normalizedOutput_posSemidef _ _ hρ).isHermitian
    · exact fun X hX => isHermitian_of_spectralBody hX
  exact squeeze_zero (fun _ => hausdorffDist_nonneg) hb hω

end
end RevisionOutput
