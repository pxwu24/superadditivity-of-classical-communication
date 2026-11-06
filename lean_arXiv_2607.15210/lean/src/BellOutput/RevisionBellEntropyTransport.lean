import BellOutput.RevisionBellTheorem
import Preliminaries.RevisionTensorChannels
import Entropy.RevisionMatrixEntropyConjugate

/-! Matrix entropy convergence for the actual Bell outputs. Positivity,
trace one, and continuity are proved; the only probabilistic input is the
permitted full block-modified strong-convergence theorem. -/

open MeasureTheory Filter Set Matrix PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
namespace RevisionMatrixEntropy
noncomputable section

lemma matrixRenyiEntropy_tendsto_of_eventually_density
    {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (p : ℝ) (hp : 0<p) (X : ℕ → Matrix A A ℂ) (Z : Matrix A A ℂ)
    (hX : ∀ᶠ n in atTop, X n ∈ densityMatrices A)
    (hlim : Tendsto X atTop (𝓝 Z)) :
    Tendsto (fun n => matrixRenyiEntropy p (X n)) atTop (𝓝 (matrixRenyiEntropy p Z)) := by
  have hZ : Z ∈ densityMatrices A := isClosed_densityMatrices.mem_of_tendsto hlim hX
  exact (matrixRenyiEntropy_continuousOn p hp Z hZ).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hlim,hX⟩)

/-- Corollary IV.1's entropy convergence, on the genuine tensor-channel
Bell output and with no separately assumed moment, continuity or density fact. -/
theorem actual_bell_output_entropy_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hStrong : FullBlockModifiedStrongInput μ k t P hH)
    (p : ℝ) (hp : 0<p) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => matrixRenyiEntropy p
      (RevisionBell.tensorMap
        (normalizedOutput (P ω N)
          (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))))
        (conjugateMap (normalizedOutput (P ω N)
          (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N)))))
        (RevisionBell.bellState (Fin (N+1))))) atTop
      (𝓝 (matrixRenyiEntropy p (RevisionBell.isotropic (Fin k) (BellLimitVerification.mixing k t)))) := by
  let hP := fun ω N => HaarProjection.projection_posSemidef (P ω N) (hH ω N) (hId ω N)
  let D := fun ω N => marginalNormalizer (P ω N) (hP ω N)
  have hD : ∀ ω N, (D ω N).IsHermitian := fun ω N =>
    (HaarProjection.traceB_posSemidef (P ω N) (hP ω N)).posSemidef_sqrt.isHermitian.inv
  have hbase : AmplifiedBlockModifiedStrongInput μ k t P := by
    simpa only [Matrix.UnitaryGroup.one_val,localConjugate_one] using hStrong.to_amplified 1
  have hevent := ae_eventually_marginal_posDef μ hk ht ht1 hkt P hH hId hbase
  have hn : ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, D ω N*traceB (P ω N)*D ω N=1 := by
    filter_upwards [hevent] with ω hω
    filter_upwards [hω] with N hN
    exact inverse_sqrt_normalizes hN
  have hlim := RevisionBell.ae_bell_limit_and_choi_purity μ hk ht ht1 hkt P hH hId hStrong D hD hn
  filter_upwards [hlim,hn] with ω hω hnω
  apply matrixRenyiEntropy_tendsto_of_eventually_density p hp
  · filter_upwards [hnω] with N hN
    exact RevisionBell.normalizedOutput_bell_mem_densityMatrices (hP ω N) (D ω N) (hD ω N) hN
  · exact (tendsto_iff_norm_sub_tendsto_zero).mpr hω.1

#print axioms actual_bell_output_entropy_limit
end
end RevisionMatrixEntropy
