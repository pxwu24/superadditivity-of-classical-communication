import Entropy.RevisionMatrixEntropyBody
import BellOutput.RevisionBellEntropyTransport
import Entropy.RevisionMatrixEntropyWitness
import Entropy.RevisionMatrixEntropyBell

/-! Proposition VI.1 and the corresponding finite-channel conclusion.
The exact rational certificate is applied to actual matrix entropies. The
finite-channel violation is derived from the two proved random limits;
no minimizer-shape, entropy-limit or Bell-witness premise is assumed. -/

open MeasureTheory Filter Set Matrix PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped Topology BigOperators ComplexOrder
namespace RevisionMatrixEntropy
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma isotropic_shannon_182 :
    matrixRenyiEntropy 1 (RevisionBell.isotropic (Fin 182)
      (BellLimitVerification.mixing 182 K182.t))=K182.bellEntropy := by
  rw [matrixRenyiEntropy_isotropic 1 (by norm_num)]
  simp only [Fintype.card_fin,Nat.cast_ofNat,if_pos rfl]
  have hr : BellLimitVerification.mixing 182 K182.t=K182.bellMixing := by
    norm_num [BellLimitVerification.mixing,BellLimitVerification.denominator,K182.t,
      K182.bellMixing,K182.density]
  rw [hr]
  have ha : K182.bellMixing+(1-K182.bellMixing)/(182:ℝ)^2=K182.bellAlpha := by
    unfold K182.bellAlpha
    ring
  change -( (K182.bellMixing+(1-K182.bellMixing)/(182:ℝ)^2)*
    Real.log (K182.bellMixing+(1-K182.bellMixing)/(182:ℝ)^2)+
    ((182:ℝ)^2-1)*(K182.bellBeta*Real.log K182.bellBeta))=K182.bellEntropy
  rw [ha]
  unfold K182.bellEntropy
  ring

/-- Proposition VI.1 exactly as an inequality between the minimum entropy
of the actual limiting matrix body and its actual isotropic Bell state. -/
theorem proposition_VI_1 :
    (477:ℝ)/1000000 <
      2*sInf (matrixRenyiEntropy 1 '' spectralBody 182 K182.t)-
        matrixRenyiEntropy 1 (RevisionBell.isotropic (Fin 182)
          (BellLimitVerification.mixing 182 K182.t)) := by
  rw [isotropic_shannon_182]
  exact proposition_VI_1_body

/-- The strict certified limiting gap holds for all sufficiently large
finite input dimensions, almost surely. This compares actual minimum output
von Neumann entropies of the channel, its conjugate, and their tensor product. -/
theorem eventual_nonadditivity_182
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin 182) (Fin (N+1) × Fin 182) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hStrong : FullBlockModifiedStrongInput μ 182 K182.t P hH) :
    let Φ := fun ω N => normalizedOutput (P ω N)
      (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N)))
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop,
      (477:ℝ)/1000000 < minimumOutputEntropy 1 (Φ ω N)+
        minimumOutputEntropy 1 (conjugateMap (Φ ω N))-
          minimumOutputEntropy 1 (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N))) := by
  let hP := fun ω N => HaarProjection.projection_posSemidef (P ω N) (hH ω N) (hId ω N)
  let D := fun ω N => marginalNormalizer (P ω N) (hP ω N)
  let Φ := fun ω N => normalizedOutput (P ω N) (D ω N)
  let A := sInf (matrixRenyiEntropy 1 '' spectralBody 182 K182.t)
  have ht : 0<K182.t := by norm_num [K182.t]
  have ht1 : K182.t<1 := by norm_num [K182.t]
  have hkt : 1<(182:ℝ)^2*K182.t := by norm_num [K182.t]
  have hs : ∀ᵐ ω ∂μ, Tendsto (fun N=>minimumOutputEntropy 1 (Φ ω N)) atTop (𝓝 A) :=
    output_continuous_minimum_limit μ (by norm_num) ht ht1 hkt P hH hId hStrong
      (matrixRenyiEntropy 1) (matrixRenyiEntropy_continuousOn 1 (by norm_num))
  have hb : ∀ᵐ ω ∂μ, Tendsto (fun N=>matrixRenyiEntropy 1
      (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N))
        (RevisionBell.bellState (Fin (N+1))))) atTop (𝓝 K182.bellEntropy) := by
    simpa only [Nat.cast_ofNat,isotropic_shannon_182] using actual_bell_output_entropy_limit μ
      (by norm_num) ht ht1 hkt P hH hId hStrong 1 (by norm_num)
  have hbase : AmplifiedBlockModifiedStrongInput μ 182 K182.t P := by
    simpa only [Matrix.UnitaryGroup.one_val,localConjugate_one] using hStrong.to_amplified 1
  have hn := ae_eventually_marginal_posDef μ (by norm_num) ht ht1 hkt P hH hId hbase
  filter_upwards [hs,hb,hn] with ω hsω hbω hnω
  have hlim := (hsω.const_mul 2).sub hbω
  have hgap : (477:ℝ)/1000000<2*A-K182.bellEntropy := proposition_VI_1_body
  have he := hlim.eventually (lt_mem_nhds hgap)
  filter_upwards [he,hnω] with N hN hAN
  have hDN : (D ω N).IsHermitian :=
    (HaarProjection.traceB_posSemidef (P ω N) (hP ω N)).posSemidef_sqrt.isHermitian.inv
  have hnorm : D ω N*traceB (P ω N)*D ω N=1 := inverse_sqrt_normalizes hAN
  have hw := normalizedOutput_minimum_bell_le 1 (by norm_num) (hP ω N) (D ω N) hDN hnorm
  have hc : minimumOutputEntropy 1 (conjugateMap (Φ ω N))=minimumOutputEntropy 1 (Φ ω N) :=
    minimumOutputEntropy_conjugateMap 1 (by norm_num) (Φ ω N)
      (fun ρ hρ => (normalizedOutput_posSemidef (hP ω N) (D ω N) hDN hρ.1).isHermitian)
  change (477:ℝ)/1000000 < minimumOutputEntropy 1 (Φ ω N)+
    minimumOutputEntropy 1 (conjugateMap (Φ ω N))-
    minimumOutputEntropy 1 (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N)))
  rw [hc]
  change (477:ℝ)/1000000 < 2*minimumOutputEntropy 1 (Φ ω N)-
    matrixRenyiEntropy 1 (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N))
      (RevisionBell.bellState (Fin (N+1)))) at hN
  change minimumOutputEntropy 1 (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N))) ≤
    matrixRenyiEntropy 1 (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N))
      (RevisionBell.bellState (Fin (N+1)))) at hw
  linarith only [hN,hw]

/-- Explicit finite-dimensional channel witnesses. The probability-space
assumption turns the almost-sure eventual result into actual CP/TP linear
maps, both with output dimension 182. -/
theorem exists_quantum_channels_182
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin 182) (Fin (N+1) × Fin 182) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hStrong : FullBlockModifiedStrongInput μ 182 K182.t P hH) :
    ∃ N : ℕ, ∃ Φ Ψ : Matrix (Fin (N+1)) (Fin (N+1)) ℂ →ₗ[ℂ] Matrix (Fin 182) (Fin 182) ℂ,
      (ProjectionChannelsCP.CompletelyPositive Φ ∧ ProjectionChannelsCP.TracePreserving Φ) ∧
      (ProjectionChannelsCP.CompletelyPositive Ψ ∧ ProjectionChannelsCP.TracePreserving Ψ) ∧
      (∀ X, Ψ X=conjugateMap Φ X) ∧
      (477:ℝ)/1000000 < minimumOutputEntropy 1 Φ+minimumOutputEntropy 1 Ψ-
        minimumOutputEntropy 1 (RevisionBell.tensorMap Φ Ψ) := by
  have hbase : AmplifiedBlockModifiedStrongInput μ 182 K182.t P := by
    simpa only [Matrix.UnitaryGroup.one_val,localConjugate_one] using hStrong.to_amplified 1
  have hpos := ae_eventually_marginal_posDef μ (by norm_num) (by norm_num [K182.t])
    (by norm_num [K182.t]) (by norm_num [K182.t]) P hH hId hbase
  have hgap := eventual_nonadditivity_182 μ P hH hId hStrong
  obtain ⟨ω,hωgap,hωpos⟩ := (hgap.and hpos).exists
  obtain ⟨N,hNgap,hNpos⟩ := (hωgap.and hωpos).exists
  let hP := HaarProjection.projection_posSemidef (P ω N) (hH ω N) (hId ω N)
  let D := marginalNormalizer (P ω N) hP
  let J := RevisionBell.normalizedChoi (P ω N) D
  let Φ := ProjectionChannelsCP.choiChannel J
  let Ψ := ProjectionChannelsCP.choiChannel (entrywiseConjugate J)
  have hD : D.IsHermitian := (HaarProjection.traceB_posSemidef (P ω N) hP).posSemidef_sqrt.isHermitian.inv
  have hn : D*traceB (P ω N)*D=1 := inverse_sqrt_normalizes hNpos
  have hJ : J.PosSemidef := RevisionBell.normalizedChoi_posSemidef hP D hD hn
  have hT : traceB J=1 := (normalized_choi D (P ω N) hD hP hn).2
  have hTbar : traceB (entrywiseConjugate J)=1 := by
    rw [RevisionBell.traceB_entrywiseConjugate,hT,entrywiseConjugate_one]
  refine ⟨N,Φ,Ψ,RevisionBell.choiChannel_CP_TP hJ hT,
    RevisionBell.choiChannel_CP_TP (RevisionBell.entrywiseConjugate_posSemidef hJ) hTbar,?_,?_⟩
  · intro X
    exact congrFun (RevisionBell.channel_entrywiseConjugate J) X
  · have heq : normalizedOutput (P ω N) D=channel J :=
      funext fun ρ => (RevisionBell.channel_normalizedChoi (P ω N) D ρ).symm
    change (477:ℝ)/1000000 < minimumOutputEntropy 1 (normalizedOutput (P ω N) D)+
      minimumOutputEntropy 1 (conjugateMap (normalizedOutput (P ω N) D))-
      minimumOutputEntropy 1 (RevisionBell.tensorMap (normalizedOutput (P ω N) D)
        (conjugateMap (normalizedOutput (P ω N) D))) at hNgap
    rw [heq,←RevisionBell.channel_entrywiseConjugate] at hNgap
    exact hNgap

#print axioms proposition_VI_1
#print axioms eventual_nonadditivity_182
#print axioms exists_quantum_channels_182
end
end RevisionMatrixEntropy
