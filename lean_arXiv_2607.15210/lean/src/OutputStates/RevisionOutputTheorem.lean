import OutputStates.RevisionOutputEventual
import RandomCompression.RevisionFullBlockInput

/-!
# Theorem III.1 from the single permitted strong-convergence input

All downstream ingredients are proved: Bernoulli edge evaluation, random
compression, eventual invertibility, Choi support identities, actual state
body geometry, fixed-unitary transport, the countable common event, and
trace-norm Hausdorff convergence. The one external theorem parameter is the
full block-modified strong-convergence theorem described in
`RevisionFullBlockInput.lean`.
-/

open MeasureTheory Filter Matrix PreliminariesMatrix ProjectionChannels
open scoped Topology ComplexOrder
namespace RevisionOutput
noncomputable section

/-- **Theorem III.1.** The actual output image converges almost surely in
the trace-norm Hausdorff distance to the actual unitarily invariant body.
There is no invertibility hypothesis: it is derived eventually within the
proof from the compression limit. -/
theorem output_space_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hStrong : FullBlockModifiedStrongInput μ k t P hH) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => traceHausdorff
      (normalizedOutput (P ω N)
        (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))) ''
          densityMatrices (Fin (N+1))) (spectralBody k t)) atTop (𝓝 0) :=
  output_space_limit_eventual_from_block_strong μ hk ht ht1 hkt P hH hId
    hStrong.to_amplified

/-- On density matrices, the cost used in the Hausdorff distance is
exactly the sum of absolute eigenvalues of their Hermitian difference. -/
lemma trace_distance_density_formula {k : ℕ} [NeZero k]
    {X Y : Matrix (Fin k) (Fin k) ℂ}
    (hX : X ∈ densityMatrices (Fin k)) (hY : Y ∈ densityMatrices (Fin k)) :
    hermitianTraceNorm (X-Y) =
      ∑ i, |(hX.1.isHermitian.sub hY.1.isHermitian).eigenvalues i| :=
  hermitianTraceNorm_eq _ _

/-- Even before the eventually valid trace normalization, the finite
outputs remain Hermitian positive semidefinite; the zero fallback in the
cost definition on non-Hermitian matrices is never used by the theorem. -/
lemma raw_normalizedOutput_posSemidef {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (P : Matrix (A × B) (A × B) ℂ) (hP : P.PosSemidef)
    {ρ : Matrix A A ℂ} (hρ : ρ ∈ densityMatrices A) :
    (normalizedOutput P (marginalNormalizer P hP) ρ).PosSemidef :=
  normalizedOutput_posSemidef hP _
    (HaarProjection.traceB_posSemidef P hP).posSemidef_sqrt.isHermitian.inv hρ.1

end
end RevisionOutput
