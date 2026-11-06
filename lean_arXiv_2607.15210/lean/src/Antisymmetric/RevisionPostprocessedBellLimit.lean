import Antisymmetric.RevisionPostprocessTensor
import Nonadditivity.RevisionMainNonadditivity

/-! The actual Bell entropy limit after any fixed finite CP/TP postprocessing,
and its finite-channel nonadditivity consequence. -/
open MeasureTheory Filter Set Matrix
open PreliminariesMatrix ProjectionChannels ProjectionChannelsCP RevisionOutput RevisionBell
open AntisymmetricVerification RevisionMatrixEntropy
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
noncomputable section
namespace RevisionMain
variable {B : Type} [Fintype B] [DecidableEq B] [Nonempty B]

theorem postprocessed_bell_output_entropy_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH)
    (E : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hE : CompletelyPositive E ∧ TracePreserving E) (p : ℝ) (hp : 0<p) :
    let D := fun ω n => marginalNormalizer (P ω n)
      (HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    let Θ := fun ω n => E.comp (normalizedChannel (P ω n) (D ω n))
    ∀ᵐ ω ∂μ, Tendsto (fun n => matrixRenyiEntropy p
      (tensorMap (Θ ω n) (conjugateMap (Θ ω n)) (bellState (Fin (n+1)))))
      atTop (nhds (matrixRenyiEntropy p (tensorMap E (conjugateMap E)
        (isotropic (Fin k) (BellLimitVerification.mixing k t))))) := by
  dsimp only
  simp_rw [tensor_conjugate_normalizedChannel_comp]
  let hP := fun ω n => HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n)
  let D := fun ω n => marginalNormalizer (P ω n) (hP ω n)
  have hD : ∀ ω n, (D ω n).IsHermitian := fun ω n =>
    (HaarProjection.traceB_posSemidef (P ω n) (hP ω n)).posSemidef_sqrt.isHermitian.inv
  have hL := (tensorLinearMap E (conjugateLinearMap E)).continuous_of_finiteDimensional
  filter_upwards [bell_output_limit μ hk ht0 ht1 hkt P hH hId hFull,
    ae_marginalNormalizer_normalizes μ hk ht0 ht1 hkt P hH hId hFull] with ω hω hnω
  apply matrixRenyiEntropy_tendsto_of_eventually_density p hp
  · filter_upwards [hnω] with n hn
    exact tensor_channel_mem_density E (conjugateLinearMap E) hE (quantumChannel_conjugate E hE)
      (normalizedOutput_bell_mem_densityMatrices (hP ω n) (D ω n) (hD ω n) hn)
  · exact hL.continuousAt.tendsto.comp ((tendsto_iff_norm_sub_tendsto_zero).mpr hω)

/-- A strict gap for the actual limiting postprocessed body and Bell state
produces nonadditivity of actual CP/TP channels at all sufficiently large
input dimensions, almost surely. -/
theorem postprocessed_eventual_nonadditivity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH)
    (E : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hE : CompletelyPositive E ∧ TracePreserving E) (p : ℝ) (hp : 0<p)
    (hgap : matrixRenyiEntropy p (tensorMap E (conjugateMap E)
        (isotropic (Fin k) (BellLimitVerification.mixing k t))) <
      2*sInf ((fun X => matrixRenyiEntropy p (E X)) '' spectralBody k t)) :
    let D := fun ω n => marginalNormalizer (P ω n)
      (HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    let Θ := fun ω n => E.comp (normalizedChannel (P ω n) (D ω n))
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      (CompletelyPositive (Θ ω n) ∧ TracePreserving (Θ ω n)) ∧
      (CompletelyPositive (conjugateLinearMap (Θ ω n)) ∧ TracePreserving (conjugateLinearMap (Θ ω n))) ∧
      minimumOutputEntropy p (tensorMap (Θ ω n) (conjugateMap (Θ ω n))) <
        minimumOutputEntropy p (Θ ω n)+minimumOutputEntropy p (conjugateMap (Θ ω n)) := by
  dsimp only
  let hP := fun ω n => HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n)
  let D := fun ω n => marginalNormalizer (P ω n) (hP ω n)
  have hD : ∀ ω n, (D ω n).IsHermitian := fun ω n =>
    (HaarProjection.traceB_posSemidef (P ω n) (hP ω n)).posSemidef_sqrt.isHermitian.inv
  filter_upwards [postprocessed_minimum_output_entropy_limit μ hk ht0 ht1 hkt P hH hId hFull E hE p hp,
    postprocessed_bell_output_entropy_limit μ hk ht0 ht1 hkt P hH hId hFull E hE p hp,
    ae_marginalNormalizer_normalizes μ hk ht0 ht1 hkt P hH hId hFull] with ω hS hB hn
  apply quantum_channel_eventual_nonadditivity (fun n => Fin (n+1))
    (fun n => E.comp (normalizedChannel (P ω n) (D ω n))) p hp _ _ _ hS hB hgap
  filter_upwards [hn] with n hn
  have hΦ := normalizedChannel_quantumChannel (hP ω n) (D ω n) (hD ω n) hn
  exact ⟨completelyPositive_comp E _ hE.1 hΦ.1,tracePreserving_comp E _ hE.2 hΦ.2⟩

end RevisionMain
