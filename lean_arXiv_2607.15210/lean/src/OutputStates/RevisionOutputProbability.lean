import OutputStates.RevisionOutputTraceDistance
import RandomCompression.RevisionBernoulliCompression

/-!
# Almost-sure output-space convergence

The countable-intersection argument is performed in the continuous real dual.
Only fixed-observable probability-one statements are used; no uncountable
intersection of events is taken. The final theorem invokes only the permitted
block-modified strong-convergence input for the deterministically rotated
projection ensembles.
-/

open MeasureTheory Filter Set Matrix Metric
open PreliminariesMatrix ProjectionChannels OutputSpaceVerification
open scoped Topology BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section GenericProbability
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [ProperSpace (E →L[ℝ] ℝ)] [TopologicalSpace.SeparableSpace (E →L[ℝ] ℝ)]

/-- The complete common-event/finite-net/separation argument for random
compact convex sets. -/
theorem ae_hausdorff_of_pointwise_support
    (μ : Measure Ω) (C : Ω → ℕ → Set E) (K : Set E)
    (hC : ∀ ω n, IsCompact (C ω n)) (hK : IsCompact K)
    (hnC : ∀ ω n, (C ω n).Nonempty) (hnK : K.Nonempty)
    (hcC : ∀ ω n, Convex ℝ (C ω n)) (hcK : Convex ℝ K)
    (hbC : ∀ ω n x, x ∈ C ω n → ‖x‖ ≤ 1) (hbK : ∀ x ∈ K, ‖x‖ ≤ 1)
    (hconv : ∀ f : E →L[ℝ] ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun n => support (C ω n) f) atTop (𝓝 (support K f))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => hausdorffDist (C ω n) K) atTop (𝓝 0) := by
  obtain ⟨s, hs, hsd⟩ := TopologicalSpace.exists_countable_dense (E →L[ℝ] ℝ)
  have hu := ae_uniform_tendsto_on_compact_of_dense μ s (closedBall (0 : E →L[ℝ] ℝ) 1)
    hs hsd (isCompact_closedBall _ _)
    (fun ω n f => support (C ω n) f) (support K)
    (fun ω n f g => support_lipschitz (hC ω n) (hnC ω n) (hbC ω n) f g)
    (support_lipschitz hK hnK hbK) (fun f _ => hconv f)
  filter_upwards [hu] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hω (ε/2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound : hausdorffDist (C ω n) K ≤ ε/2 := by
    apply hausdorffDist_le_of_support_le (hC ω n) hK (hnC ω n) hnK (hcC ω n) hcK (by positivity)
    intro f hf
    exact (hN n hn f (mem_closedBall_zero_iff.mpr hf)).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hausdorffDist_nonneg]
  linarith

end GenericProbability

/-- Almost-sure actual trace-norm Hausdorff convergence from the
fixed-observable unnormalized compression limit. -/
theorem ae_actual_output_traceHausdorff_from_compression
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hP : ∀ ω N, (P ω N).PosSemidef) (hA : ∀ ω N, (traceB (P ω N)).PosDef)
    (hconv : ∀ (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.IsHermitian),
      ∀ᵐ ω ∂μ, ∀ z : ℝ,
      Tendsto (fun N => largestEigenvalue
        (contraction_isHermitian (hP ω N).isHermitian
          (real_scalar_shift_hermitian hH Matrix.isHermitian_one z)))
        atTop (𝓝 (bodySupport k t (fun i => hH.eigenvalues i - z)))) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => traceHausdorff
      (normalizedOutput (P ω N) (hA ω N).posSemidef.sqrt⁻¹ '' densityMatrices (Fin (N+1)))
      (spectralBody k t)) atTop (𝓝 0) := by
  let C : Ω → ℕ → Set (Matrix (Fin k) (Fin k) ℂ) := fun ω N =>
    normalizedOutput (P ω N) (hA ω N).posSemidef.sqrt⁻¹ '' densityMatrices (Fin (N+1))
  have hC : ∀ ω N, IsCompact (C ω N) := fun ω N => (output_image_nonempty_compact _ _).2
  have hnC : ∀ ω N, (C ω N).Nonempty := fun ω N => (output_image_nonempty_compact _ _).1
  have hcC : ∀ ω N, Convex ℝ (C ω N) := fun ω N => output_image_convex _ _
  have hCstate : ∀ ω N, C ω N ⊆ densityMatrices (Fin k) := by
    intro ω N X hX
    obtain ⟨ρ, hρ, rfl⟩ := hX
    exact normalizedOutput_mem_densityMatrices _ (hP ω N) (hA ω N) hρ
  have hKstate := spectralBody_subset_densityMatrices hk ht.le hkt
  have hpoint : ∀ f : Matrix (Fin k) (Fin k) ℂ →L[ℝ] ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun N => support (C ω N) f) atTop (𝓝 (support (spectralBody k t) f)) := by
    intro f
    let H := hermitianFunctionalMatrix f
    have hH : H.IsHermitian := hermitianFunctionalMatrix_isHermitian f
    filter_upwards [hconv H hH] with ω hω
    have hc : Tendsto (fun N => outputSupport (P ω N) (hA ω N).posSemidef.sqrt⁻¹ H)
        atTop (𝓝 (normalizedBodySupport k t hH.eigenvalues)) := by
      apply concrete_normalized_support_tendsto hk ht.le ht1.le hkt hH.eigenvalues
        (fun N z => largestEigenvalue
          (contraction_isHermitian (hP ω N).isHermitian
            (real_scalar_shift_hermitian hH Matrix.isHermitian_one z)))
      · intro N z
        rw [normalized_output_support _ (hP ω N).isHermitian _
          (hA ω N).posSemidef.posSemidef_sqrt.isHermitian.inv _ hH]
        have heq := inverse_sqrt_threshold (traceB (P ω N)) (contraction (P ω N) H)
          (hA ω N) (contraction_isHermitian (hP ω N).isHermitian hH) z
        simpa only [contraction_sub_scalar] using heq
      · exact hω
    have heqC : ∀ N, support (C ω N) f = outputSupport (P ω N) (hA ω N).posSemidef.sqrt⁻¹ H := by
      intro N
      unfold support outputSupport
      congr 1
      apply Set.image_congr
      intro X hX
      exact (hermitian_trace_representation f (hCstate ω N hX).1.isHermitian).symm
    have heqK : support (spectralBody k t) f = normalizedBodySupport k t hH.eigenvalues := by
      rw [← spectralBody_support hk ht ht1 hkt H hH]
      unfold support
      congr 1
      apply Set.image_congr
      intro X hX
      exact (hermitian_trace_representation f (hKstate hX).1.isHermitian).symm
    simpa only [heqC, heqK] using hc
  have ha := ae_hausdorff_of_pointwise_support μ C (spectralBody k t)
    hC (isCompact_spectralBody hk ht.le hkt) hnC (spectralBody_nonempty hk ht.le ht1.le)
    hcC (convex_spectralBody hk ht ht1 hkt)
    (fun ω N X hX => density_norm_le_one (hCstate ω N hX))
    (fun X hX => density_norm_le_one (hKstate hX)) hpoint
  filter_upwards [ha] with ω hω
  have hb := fun N => traceHausdorff_comparison (C ω N) (spectralBody k t)
    (hC ω N) (isCompact_spectralBody hk ht.le hkt) (hnC ω N) (spectralBody_nonempty hk ht.le ht1.le)
  apply squeeze_zero (fun N => (hb N).1) (fun N => (hb N).2)
  simpa only [mul_zero] using hω.const_mul ((Fintype.card (Fin k) : ℝ)^3)

lemma bernoulliSupport_eq_bodySupport (k : ℕ) (t : ℝ) (a : Fin k → ℝ) :
    bernoulliSupport t (k : ℝ) a = bodySupport k t a := by
  have hs : (bernoulliFeasible t (k : ℝ) : Set (Fin k → ℝ)) = AppendixB.Dset k t := by
    ext u
    simp only [bernoulliFeasible, AppendixB.Dset, AppendixB.ct, bernoulliCost,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1, hc⟩
      exact ⟨fun i => ⟨h0 i, h1 i⟩, hc⟩
    · rintro ⟨hu, hc⟩
      exact ⟨fun i => (hu i).1, fun i => (hu i).2, hc⟩
  unfold bernoulliSupport bernoulliObjectiveValues bodySupport
  rw [hs]

lemma localConjugate_idempotent {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A]
    (P : Matrix (A × B) (A × B) ℂ) (hP : P * P = P)
    (V : Matrix.unitaryGroup B ℂ) :
    localConjugate P (V : Matrix B B ℂ) * localConjugate P (V : Matrix B B ℂ) =
      localConjugate P (V : Matrix B B ℂ) := by
  let L := Matrix.kronecker (1 : Matrix A A ℂ) (V : Matrix B B ℂ).conjTranspose
  let R := Matrix.kronecker (1 : Matrix A A ℂ) (V : Matrix B B ℂ)
  have hRL : R * L = 1 := by
    change Matrix.kronecker (1 : Matrix A A ℂ) (V : Matrix B B ℂ) *
      Matrix.kronecker (1 : Matrix A A ℂ) (V : Matrix B B ℂ).conjTranspose = 1
    have hV : (V : Matrix B B ℂ) * (V : Matrix B B ℂ).conjTranspose = 1 :=
      Matrix.mem_unitaryGroup_iff.mp V.2
    rw [local_kronecker_mul, hV]
    exact Matrix.one_kronecker_one
  change (L * P * R) * (L * P * R) = L * P * R
  calc
    _ = L * (P * (R * L) * P) * R := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hRL, Matrix.mul_one, hP]

lemma conjugate_shifted_eigenvalues {k : ℕ} (H : Matrix (Fin k) (Fin k) ℂ)
    (hH : H.IsHermitian) (z : ℝ) :
    (hH.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) *
      Matrix.diagonal (fun i => ((hH.eigenvalues i-z : ℝ) : ℂ)) *
      (hH.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ).conjTranspose =
      H - (z : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) := by
  have hd : Matrix.diagonal (fun i => ((hH.eigenvalues i-z : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) -
        (z : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hV : (hH.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) *
      (hH.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hV]
  congr 1
  exact hH.spectral_theorem.symm

/-- Theorem III.1 for the normalized part of the sequence. The only analytic
black box is the block-modified strong-convergence statement, applied to each
fixed unitary rotation of the same projection ensemble. The right-edge law,
random compression, unitary transport, normalization, state-body geometry,
countable common event, and trace-norm Hausdorff convergence are all proved.

`hA` records that this statement is applied after discarding terms whose
input marginal is singular, as in the manuscript. -/
theorem output_space_limit_from_block_strong
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hA : ∀ ω N, (traceB (P ω N)).PosDef)
    (hBM : ∀ V : Matrix.unitaryGroup (Fin k) ℂ,
      AmplifiedBlockModifiedStrongInput μ k t
        (fun ω N => localConjugate (P ω N) (V : Matrix (Fin k) (Fin k) ℂ))) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => traceHausdorff
      (normalizedOutput (P ω N) (hA ω N).posSemidef.sqrt⁻¹ '' densityMatrices (Fin (N+1)))
      (spectralBody k t)) atTop (𝓝 0) := by
  have hP : ∀ ω N, (P ω N).PosSemidef := fun ω N =>
    HaarProjection.projection_posSemidef (P ω N) (hH ω N) (hId ω N)
  apply ae_actual_output_traceHausdorff_from_compression μ hk ht ht1 hkt P hP hA
  intro H hHerm
  let V := hHerm.eigenvectorUnitary
  let Q := fun ω N => localConjugate (P ω N) (V : Matrix (Fin k) (Fin k) ℂ)
  have hQH : ∀ ω N, (Q ω N).IsHermitian := fun ω N => localConjugate_isHermitian (hH ω N) V
  have hQI : ∀ ω N, Q ω N * Q ω N = Q ω N := fun ω N =>
    localConjugate_idempotent (P ω N) (hId ω N) V
  have hc := random_compression_from_amplified_block_strong μ k hk t ht ht1 Q hQH hQI (hBM V)
  filter_upwards [hc] with ω hω
  intro z
  have heqN (N : ℕ) : blockCompression (diagonalBlock (Q ω N)) (fun i => hHerm.eigenvalues i-z) =
      contraction (P ω N) (H-(z : ℂ) • 1) := by
    rw [show diagonalBlock (Q ω N) = diagonalBlocks (Q ω N) from rfl,
      ← contraction_diagonal]
    change contraction (localConjugate (P ω N) V)
      (Matrix.diagonal (fun i => ((hHerm.eigenvalues i-z : ℝ) : ℂ))) = _
    rw [contraction_localConjugate]
    simp only [V, conjugate_shifted_eigenvalues]
  simpa only [heqN, bernoulliSupport_eq_bodySupport] using hω (fun i => hHerm.eigenvalues i-z)

end
end RevisionOutput
