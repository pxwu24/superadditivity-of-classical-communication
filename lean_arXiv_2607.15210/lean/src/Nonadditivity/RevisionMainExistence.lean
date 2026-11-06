import Antisymmetric.RevisionPostprocessedBellLimit
import HaarProjections.RevisionCanonicalEnsemble

/-! From a strict limiting postprocessed-body gap to actual finite-dimensional
channels, using a concrete independent Haar-projection ensemble. The only
external input is its block-modified strong-convergence theorem. -/
open MeasureTheory Filter Set Matrix
open PreliminariesMatrix ProjectionChannels ProjectionChannelsCP RevisionOutput RevisionBell
open AntisymmetricVerification RevisionMatrixEntropy
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
noncomputable section
namespace RevisionMain

theorem exists_nonadditive_channel_of_postprocessed_body_gap
    (hStrong : ProjectionChannels.Canonical.CanonicalStrongInput)
    {B : Type} [Fintype B] [DecidableEq B] [Nonempty B]
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (E : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hE : CompletelyPositive E ∧ TracePreserving E) (p : ℝ) (hp : 0<p)
    (hgap : matrixRenyiEntropy p (tensorMap E (conjugateMap E)
        (isotropic (Fin k) (BellLimitVerification.mixing k t))) <
      2*sInf ((fun X => matrixRenyiEntropy p (E X)) '' spectralBody k t)) :
    ∃ N : ℕ, ∃ Φ : Matrix (Fin (N+1)) (Fin (N+1)) ℂ →ₗ[ℂ] Matrix B B ℂ,
      (CompletelyPositive Φ ∧ TracePreserving Φ) ∧
      (CompletelyPositive (conjugateLinearMap Φ) ∧ TracePreserving (conjugateLinearMap Φ)) ∧
      minimumOutputEntropy p (tensorMap Φ (conjugateMap Φ)) <
        minimumOutputEntropy p Φ+minimumOutputEntropy p (conjugateMap Φ) := by
  let P := ProjectionChannels.Canonical.projection k t
  have hH := ProjectionChannels.Canonical.projection_isHermitian k t
  have hId := ProjectionChannels.Canonical.projection_idempotent k t
  have hFull := hStrong k hk t ht0 ht1
  obtain ⟨ω,hω⟩ := (postprocessed_eventual_nonadditivity
    (ProjectionChannels.Canonical.probability k) hk ht0 ht1 hkt P hH hId hFull E hE p hp hgap).exists
  obtain ⟨N,hN⟩ := hω.exists
  exact ⟨N,_,hN⟩

end RevisionMain
