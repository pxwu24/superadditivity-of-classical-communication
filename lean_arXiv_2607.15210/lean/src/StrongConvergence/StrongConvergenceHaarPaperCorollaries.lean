import StrongConvergence.StrongConvergenceHaarSequenceStrong
import StrongConvergence.StrongConvergenceCanonicalPaperCorollaries
import Checks.UnprovedTargets

/-! Paper conclusions for arbitrary Haar projection sequences on arbitrary
probability spaces. Integer ranks need only have the prescribed density limit;
no independence or unproved convergence premise is imposed. -/
open MeasureTheory Filter Set Matrix
open PreliminariesMatrix ProjectionChannels ProjectionChannelsCP RevisionOutput RevisionBell
open AntisymmetricVerification RevisionMatrixEntropy
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
noncomputable section

namespace ProjectionChannels.HaarSequence
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {k : ℕ} {d : ℕ → ℕ}
variable {P₀ : (n : ℕ) → Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ}
variable {P : Ω → (n : ℕ) → Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ}

/-- The actual inverse-square-root marginal normalization. -/
def paperNormalizer (h : HaarSequence μ k d P₀ P) (ω : Ω) (n : ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  marginalNormalizer (P ω n)
    (HaarProjection.projection_posSemidef _ (h.isHermitian ω n) (h.idempotent ω n))

/-- The normalized projection-induced channel output map. -/
def paperOutput (h : HaarSequence μ k d P₀ P) (ω : Ω) (n : ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ → Matrix (Fin k) (Fin k) ℂ :=
  normalizedOutput (P ω n) (paperNormalizer h ω n)

/-- The actual normalized Choi matrix. -/
def paperChoi (h : HaarSequence μ k d P₀ P) (ω : Ω) (n : ℕ) :
    Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ :=
  normalizedChoi (P ω n) (paperNormalizer h ω n)

/-- Random compression on one probability-one event for every real coefficient
vector, with only the original Haar marginal and rank-density assumptions. -/
theorem paper_random_compression_limit (h : HaarSequence μ k d P₀ P) {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hdt : Tendsto (density k d) atTop (𝓝 t)) :
    ∀ᵐ ω ∂μ, ∀ a : Fin k → ℝ,
      Tendsto (fun n => largestEigenvalue
        (blockCompression_isHermitian (diagonalBlock (P ω n))
          (fun i => (projection_diagonalBlock_contraction (P ω n)
            (h.isHermitian ω n) (h.idempotent ω n) i).1.1) a))
        atTop (𝓝 (bernoulliSupport t (k:ℝ) a)) := by
  have hBM : AmplifiedBlockModifiedStrongInput μ k t P := by
    simpa only [Matrix.UnitaryGroup.one_val, localConjugate_one] using
      (h.fullBlockModifiedStrongInput hk ht0 ht1 hdt).to_amplified 1
  exact random_compression_from_amplified_block_strong μ k hk t ht0 ht1
    P h.isHermitian h.idempotent hBM

/-- Theorem III.1 for every admissible Haar projection sequence. -/
theorem paper_output_space_limit [NeZero k] (h : HaarSequence μ k d P₀ P) {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (hkt : 1<(k:ℝ)^2*t)
    (hdt : Tendsto (density k d) atTop (𝓝 t)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => traceHausdorff
      (paperOutput h ω n '' densityMatrices (Fin (n+1))) (spectralBody k t)) atTop (𝓝 0) :=
  RevisionOutput.output_space_limit μ hk ht0 ht1 hkt P h.isHermitian h.idempotent
    (h.fullBlockModifiedStrongInput hk ht0 ht1 hdt)

/-- The one-copy entropy limit in Corollary III.2 for every positive Rényi order. -/
theorem paper_minimum_output_entropy_limit [NeZero k] (h : HaarSequence μ k d P₀ P) {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (hkt : 1<(k:ℝ)^2*t)
    (hdt : Tendsto (density k d) atTop (𝓝 t)) (p : ℝ) (hp : 0<p) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => minimumOutputEntropy p (paperOutput h ω n))
      atTop (𝓝 (sInf ((AppendixB.renyi p Finset.univ (fun _ : Fin k => 1)) '' AppendixB.Lam k t))) :=
  actual_minimum_output_entropy_limit μ hk ht0 ht1 hkt P h.isHermitian h.idempotent
    (h.fullBlockModifiedStrongInput hk ht0 ht1 hdt) p hp

/-- Theorem IV.1 and Proposition A.4 for actual Bell outputs and Choi purities. -/
theorem paper_bell_output_and_purity_limit [NeZero k] (h : HaarSequence μ k d P₀ P) {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (hkt : 1<(k:ℝ)^2*t)
    (hdt : Tendsto (density k d) atTop (𝓝 t)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => ‖tensorMap (paperOutput h ω n) (conjugateMap (paperOutput h ω n))
        (bellState (Fin (n+1))) - isotropic (Fin k) (BellLimitVerification.mixing k t)‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => Matrix.trace (paperChoi h ω n * paperChoi h ω n) /
        (((n+1:ℕ):ℂ)*(k:ℂ))) atTop (𝓝 (BellLimitVerification.bellAlpha k t:ℂ)) :=
  RevisionBell.bell_output_and_purity_limit μ hk ht0 ht1 hkt P h.isHermitian h.idempotent
    (h.fullBlockModifiedStrongInput hk ht0 ht1 hdt)

/-- Theorem IV.1, separately exposed for the actual Bell output. -/
theorem paper_bell_output_limit [NeZero k] (h : HaarSequence μ k d P₀ P) {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (hkt : 1<(k:ℝ)^2*t)
    (hdt : Tendsto (density k d) atTop (𝓝 t)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => ‖tensorMap (paperOutput h ω n) (conjugateMap (paperOutput h ω n))
        (bellState (Fin (n+1))) - isotropic (Fin k) (BellLimitVerification.mixing k t)‖)
        atTop (𝓝 0) :=
  (h.paper_bell_output_and_purity_limit hk ht0 ht1 hkt hdt).mono fun _ hω => hω.1

/-- Proposition A.4, separately exposed as a full normalized Choi trace limit. -/
theorem paper_choi_purity_limit [NeZero k] (h : HaarSequence μ k d P₀ P) {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (hkt : 1<(k:ℝ)^2*t)
    (hdt : Tendsto (density k d) atTop (𝓝 t)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Matrix.trace (paperChoi h ω n * paperChoi h ω n) /
      (((n+1:ℕ):ℂ)*(k:ℂ))) atTop (𝓝 (BellLimitVerification.bellAlpha k t:ℂ)) :=
  (h.paper_bell_output_and_purity_limit hk ht0 ht1 hkt hdt).mono fun _ hω => hω.2

/-- Proposition A.3 for all actual normalized Choi blocks simultaneously. -/
theorem paper_normalized_choi_mixed_moment_limit [NeZero k] (h : HaarSequence μ k d P₀ P) {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (hkt : 1<(k:ℝ)^2*t)
    (hdt : Tendsto (density k d) atTop (𝓝 t)) :
    ∀ᵐ ω ∂μ, ∀ i j p q : Fin k,
      Tendsto (fun n => (1/((n+1:ℕ):ℂ))*Matrix.trace
        (BellLimitVerification.choiBlock (paperChoi h ω n) i j *
          BellLimitVerification.choiBlock (paperChoi h ω n) q p)) atTop
        (𝓝 (-(BellLimitVerification.hessianC0 k t:ℂ)*(if i=j ∧ p=q then 1 else 0)-
          (BellLimitVerification.hessianC1 k t:ℂ)*(if i=p ∧ j=q then 1 else 0))) :=
  RevisionBell.normalized_choi_mixed_moment_limit μ hk ht0 ht1 hkt P h.isHermitian h.idempotent
    (h.fullBlockModifiedStrongInput hk ht0 ht1 hdt)

/-- Corollary IV.2 for the actual product/conjugate-channel entropy minimum. -/
theorem paper_product_entropy_limsup [NeZero k] (h : HaarSequence μ k d P₀ P) {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (hkt : 1<(k:ℝ)^2*t)
    (hdt : Tendsto (density k d) atTop (𝓝 t)) (p : ℝ) (hp : 0<p) :
    ∀ᵐ ω ∂μ, Filter.limsup
      (fun n => minimumOutputEntropy p
        (tensorMap (paperOutput h ω n) (conjugateMap (paperOutput h ω n)))) atTop ≤
      AppendixB.renyi p (Finset.univ : Finset (Fin 2)) ![1,(k:ℝ)^2-1]
        ![AppendixB.alphaB k t, AppendixB.betaB k t] :=
  corollary_IV_2_fixed_k μ hk ht0 ht1 hkt P h.isHermitian h.idempotent
    (h.fullBlockModifiedStrongInput hk ht0 ht1 hdt) p hp

/-- Both fixed-output-dimension entropy limits in Theorem V.1. -/
theorem paper_antisymmetric_entropy_limits [NeZero k] (h : HaarSequence μ k d P₀ P) {t : ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1) (hkt : 1<(k:ℝ)^2*t)
    (hdt : Tendsto (density k d) atTop (𝓝 t))
    (r : ℕ) (hrk : r+1≤k) (p : ℝ) (hp : 0<p) :
    let Θ := fun ω n => RevisionMain.antisymmetricNormalizedChannel r (P ω n)
      (HaarProjection.projection_posSemidef _ (h.isHermitian ω n) (h.idempotent ω n))
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => minimumOutputEntropy p (Θ ω n)) atTop
        (𝓝 (AppendixB.infimumOutputEntropy p t k (r+1))) ∧
      Tendsto (fun n => matrixRenyiEntropy p
        (tensorMap (Θ ω n) (conjugateMap (Θ ω n)) (bellState (Fin (n+1)))))
        atTop (𝓝 (matrixRenyiEntropy p (RevisionMain.antisymmetricBellLimit k r t))) :=
  RevisionMain.theorem_V_1_fixed_k μ hk ht0 ht1 hkt r hrk P h.isHermitian h.idempotent
    (h.fullBlockModifiedStrongInput hk ht0 ht1 hdt) p hp

end ProjectionChannels.HaarSequence

namespace ProjectionChannels
universe u

/-- Verification of the exact pre-existing full random-compression target,
including arbitrary probability spaces, arbitrary rank sequences, and one
probability-one event for all real coefficient vectors. -/
theorem randomCompressionStatement_verified : randomCompressionStatement.{u} := by
  intro Ω _ μ _ k hk t ht0 ht1 d P₀ P hP₀ hH hId hMeas hLaw hRatio
  let h : HaarSequence μ k d P₀ P :=
    ⟨fun n => (hP₀ n).1, fun n => (hP₀ n).2.1, fun n => (hP₀ n).2.2,
      hH, hId, hMeas, hLaw⟩
  exact h.paper_random_compression_limit hk ht0 ht1 hRatio

end ProjectionChannels

#print axioms ProjectionChannels.randomCompressionStatement_verified
#print axioms ProjectionChannels.HaarSequence.paper_output_space_limit
#print axioms ProjectionChannels.HaarSequence.paper_minimum_output_entropy_limit
#print axioms ProjectionChannels.HaarSequence.paper_bell_output_limit
#print axioms ProjectionChannels.HaarSequence.paper_choi_purity_limit
#print axioms ProjectionChannels.HaarSequence.paper_normalized_choi_mixed_moment_limit
#print axioms ProjectionChannels.HaarSequence.paper_product_entropy_limsup
#print axioms ProjectionChannels.HaarSequence.paper_antisymmetric_entropy_limits
