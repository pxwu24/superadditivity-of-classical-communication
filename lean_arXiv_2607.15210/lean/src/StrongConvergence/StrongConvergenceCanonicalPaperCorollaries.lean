import StrongConvergence.StrongConvergenceCanonicalStrong
import Nonadditivity.RevisionMainTheorem
import Dimension182.RevisionPropositionVI
import BellOutput.RevisionCorollaryIV

/-! Unconditional paper endpoints for the actual canonical independent Haar
ensemble. The original generic implications remain available; every strong-
convergence input in these corollaries is supplied by `canonicalStrongInput`. -/

open MeasureTheory Filter Set Matrix
open PreliminariesMatrix ProjectionChannels ProjectionChannelsCP RevisionOutput RevisionBell
open AntisymmetricVerification RevisionMatrixEntropy
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
noncomputable section

namespace ProjectionChannels.Canonical

/-- The actual inverse-square-root marginal normalizer of the canonical projection. -/
def paperNormalizer (k : ℕ) (t : ℝ) (ω : Sample k) (n : ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  marginalNormalizer (projection k t ω n) (HaarProjection.projection_posSemidef _
    (projection_isHermitian k t ω n) (projection_idempotent k t ω n))

/-- The normalized canonical channel output map. -/
def paperOutput (k : ℕ) (t : ℝ) (ω : Sample k) (n : ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ → Matrix (Fin k) (Fin k) ℂ :=
  normalizedOutput (projection k t ω n) (paperNormalizer k t ω n)

/-- The actual normalized Choi matrix. -/
def paperChoi (k : ℕ) (t : ℝ) (ω : Sample k) (n : ℕ) :
    Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ :=
  normalizedChoi (projection k t ω n) (paperNormalizer k t ω n)

/-- Canonical specialization of Lemma II.3, on one probability-one event for
all real coefficient vectors. -/
theorem paper_random_compression_limit {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂probability k, ∀ a : Fin k → ℝ,
      Tendsto (fun n => largestEigenvalue (compressionHermitian k t a ω n))
        atTop (𝓝 (bernoulliSupport t (k : ℝ) a)) := by
  have hBM : AmplifiedBlockModifiedStrongInput (probability k) k t (projection k t) := by
    simpa only [Matrix.UnitaryGroup.one_val, localConjugate_one] using
      (canonicalStrongInput k hk t ht0 ht1).to_amplified 1
  exact random_compression_from_amplified_block_strong (probability k) k hk t ht0 ht1
    (projection k t) (projection_isHermitian k t) (projection_idempotent k t) hBM

/-- Theorem III.1 for the canonical Haar ensemble, without a convergence premise. -/
theorem paper_output_space_limit {k : ℕ} [NeZero k] {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t) :
    ∀ᵐ ω ∂probability k, Tendsto (fun n => traceHausdorff
      (paperOutput k t ω n '' densityMatrices (Fin (n+1))) (spectralBody k t)) atTop (𝓝 0) :=
  RevisionOutput.output_space_limit (probability k) hk ht0 ht1 hkt
    (projection k t) (projection_isHermitian k t) (projection_idempotent k t)
    (canonicalStrongInput k hk t ht0 ht1)

/-- The one-copy entropy limit in III.2 for every positive Rényi order. -/
theorem paper_minimum_output_entropy_limit {k : ℕ} [NeZero k] {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t)
    (p : ℝ) (hp : 0 < p) :
    ∀ᵐ ω ∂probability k, Tendsto (fun n => minimumOutputEntropy p (paperOutput k t ω n))
      atTop (𝓝 (sInf ((AppendixB.renyi p Finset.univ (fun _ : Fin k => 1)) '' AppendixB.Lam k t))) :=
  actual_minimum_output_entropy_limit (probability k) hk ht0 ht1 hkt
    (projection k t) (projection_isHermitian k t) (projection_idempotent k t)
    (canonicalStrongInput k hk t ht0 ht1) p hp

/-- Theorem IV.1 and Proposition A.4 for the actual Bell output and Choi purity. -/
theorem paper_bell_output_and_purity_limit {k : ℕ} [NeZero k] {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t) :
    ∀ᵐ ω ∂probability k,
      Tendsto (fun n => ‖tensorMap (paperOutput k t ω n) (conjugateMap (paperOutput k t ω n))
        (bellState (Fin (n+1))) - isotropic (Fin k) (BellLimitVerification.mixing k t)‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => Matrix.trace (paperChoi k t ω n * paperChoi k t ω n) /
        (((n+1:ℕ):ℂ)*(k:ℂ))) atTop (𝓝 (BellLimitVerification.bellAlpha k t : ℂ)) :=
  RevisionBell.bell_output_and_purity_limit (probability k) hk ht0 ht1 hkt
    (projection k t) (projection_isHermitian k t) (projection_idempotent k t)
    (canonicalStrongInput k hk t ht0 ht1)

/-- Proposition A.3 for the actual canonical normalized Choi blocks. -/
theorem paper_normalized_choi_mixed_moment_limit {k : ℕ} [NeZero k] {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t) :
    ∀ᵐ ω ∂probability k, ∀ i j p q : Fin k,
      Tendsto (fun n => (1/((n+1:ℕ):ℂ))*Matrix.trace
        (BellLimitVerification.choiBlock (paperChoi k t ω n) i j *
         BellLimitVerification.choiBlock (paperChoi k t ω n) q p)) atTop
        (𝓝 (-(BellLimitVerification.hessianC0 k t:ℂ)*(if i=j ∧ p=q then 1 else 0)-
          (BellLimitVerification.hessianC1 k t:ℂ)*(if i=p ∧ j=q then 1 else 0))) :=
  RevisionBell.normalized_choi_mixed_moment_limit (probability k) hk ht0 ht1 hkt
    (projection k t) (projection_isHermitian k t) (projection_idempotent k t)
    (canonicalStrongInput k hk t ht0 ht1)

/-- Corollary IV.2 for the canonical product/conjugate channel. -/
theorem paper_product_entropy_limsup {k : ℕ} [NeZero k] {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t)
    (p : ℝ) (hp : 0 < p) :
    ∀ᵐ ω ∂probability k, Filter.limsup
      (fun n => minimumOutputEntropy p
        (tensorMap (paperOutput k t ω n) (conjugateMap (paperOutput k t ω n)))) atTop ≤
      AppendixB.renyi p (Finset.univ : Finset (Fin 2)) ![1,(k:ℝ)^2-1]
        ![AppendixB.alphaB k t, AppendixB.betaB k t] :=
  corollary_IV_2_fixed_k (probability k) hk ht0 ht1 hkt
    (projection k t) (projection_isHermitian k t) (projection_idempotent k t)
    (canonicalStrongInput k hk t ht0 ht1) p hp

/-- The two fixed-output-dimension limits in Theorem V.1. -/
theorem paper_antisymmetric_entropy_limits {k : ℕ} [NeZero k] {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t)
    (r : ℕ) (hrk : r+1 ≤ k) (p : ℝ) (hp : 0 < p) :
    let Θ := fun ω n => RevisionMain.antisymmetricNormalizedChannel r (projection k t ω n)
      (HaarProjection.projection_posSemidef _ (projection_isHermitian k t ω n)
        (projection_idempotent k t ω n))
    ∀ᵐ ω ∂probability k,
      Tendsto (fun n => minimumOutputEntropy p (Θ ω n)) atTop
        (𝓝 (AppendixB.infimumOutputEntropy p t k (r+1))) ∧
      Tendsto (fun n => matrixRenyiEntropy p
        (tensorMap (Θ ω n) (conjugateMap (Θ ω n)) (bellState (Fin (n+1)))))
        atTop (𝓝 (matrixRenyiEntropy p (RevisionMain.antisymmetricBellLimit k r t))) :=
  RevisionMain.theorem_V_1_fixed_k (probability k) hk ht0 ht1 hkt r hrk
    (projection k t) (projection_isHermitian k t) (projection_idempotent k t)
    (canonicalStrongInput k hk t ht0 ht1) p hp

/-- The certified dimension-182 entropy gap holds eventually almost surely. -/
theorem paper_eventual_nonadditivity_182 :
    ∀ᵐ ω ∂probability 182, ∀ᶠ n in atTop,
      (477:ℝ)/1000000 < minimumOutputEntropy 1 (paperOutput 182 K182.t ω n) +
        minimumOutputEntropy 1 (conjugateMap (paperOutput 182 K182.t ω n)) -
        minimumOutputEntropy 1 (tensorMap (paperOutput 182 K182.t ω n)
          (conjugateMap (paperOutput 182 K182.t ω n))) :=
  eventual_nonadditivity_182 (probability 182) (projection 182 K182.t)
    (projection_isHermitian 182 K182.t) (projection_idempotent 182 K182.t)
    (canonicalStrongInput 182 (by norm_num) K182.t (by norm_num [K182.t]) (by norm_num [K182.t]))

end ProjectionChannels.Canonical
namespace RevisionMain

/-- Theorem I.1 without any external strong-convergence assumption: each
positive Rényi order has actual finite-dimensional CP/TP channel witnesses. -/
theorem theorem_I_1_unconditional (p : ℝ) (hp : 0 < p) :
    ∃ k N : ℕ, 20 ≤ k ∧
      ∃ Φ : Matrix (Fin (N+1)) (Fin (N+1)) ℂ →ₗ[ℂ]
        Matrix (SubsetIndex k 5) (SubsetIndex k 5) ℂ,
      (CompletelyPositive Φ ∧ TracePreserving Φ) ∧
      (CompletelyPositive (conjugateLinearMap Φ) ∧ TracePreserving (conjugateLinearMap Φ)) ∧
      minimumOutputEntropy p (tensorMap Φ (conjugateMap Φ)) <
        minimumOutputEntropy p Φ + minimumOutputEntropy p (conjugateMap Φ) :=
  theorem_I_1 ProjectionChannels.Canonical.canonicalStrongInput p hp

end RevisionMain
namespace RevisionMatrixEntropy

/-- Actual CP/TP channels with output dimension 182 and the certified strict
von Neumann entropy gap, without a probabilistic or convergence premise. -/
theorem exists_quantum_channels_182_unconditional :
    ∃ N : ℕ, ∃ Φ Ψ : Matrix (Fin (N+1)) (Fin (N+1)) ℂ →ₗ[ℂ] Matrix (Fin 182) (Fin 182) ℂ,
      (CompletelyPositive Φ ∧ TracePreserving Φ) ∧
      (CompletelyPositive Ψ ∧ TracePreserving Ψ) ∧
      (∀ X, Ψ X = conjugateMap Φ X) ∧
      (477:ℝ)/1000000 < minimumOutputEntropy 1 Φ + minimumOutputEntropy 1 Ψ -
        minimumOutputEntropy 1 (tensorMap Φ Ψ) :=
  exists_quantum_channels_182 (Canonical.probability 182) (Canonical.projection 182 K182.t)
    (Canonical.projection_isHermitian 182 K182.t) (Canonical.projection_idempotent 182 K182.t)
    (Canonical.canonicalStrongInput 182 (by norm_num) K182.t (by norm_num [K182.t]) (by norm_num [K182.t]))

end RevisionMatrixEntropy

#print axioms RevisionMain.theorem_I_1_unconditional
#print axioms RevisionMatrixEntropy.exists_quantum_channels_182_unconditional
#print axioms ProjectionChannels.Canonical.paper_output_space_limit
#print axioms ProjectionChannels.Canonical.paper_bell_output_and_purity_limit
#print axioms ProjectionChannels.Canonical.paper_normalized_choi_mixed_moment_limit
#print axioms ProjectionChannels.Canonical.paper_antisymmetric_entropy_limits
