import Antisymmetric.RevisionEntropyTheoremV
import Nonadditivity.RevisionMainExistence

/-! Theorem I.1. Actual finite-dimensional completely positive trace-preserving
channels violate additivity for every positive finite Rényi order. All entropy,
spectral, variational, tensor, and probabilistic-event steps are proved. The
only external theorem parameter is block-modified strong convergence for the
explicit independent Haar ensemble. -/
open MeasureTheory Filter Set Matrix
open PreliminariesMatrix ProjectionChannels ProjectionChannelsCP RevisionOutput RevisionBell
open AntisymmetricVerification RevisionMatrixEntropy
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
noncomputable section
namespace RevisionMain

/-- **Theorem I.1**, with an actual channel and its actual conjugate. The output
space is the five-particle antisymmetric subspace of C^k, of dimension choose(k,5).
The channel is obtained at a finite index of the canonical Haar ensemble. -/
theorem theorem_I_1
    (hStrong : ProjectionChannels.Canonical.CanonicalStrongInput)
    (p : ℝ) (hp : 0<p) :
    ∃ k N : ℕ, 20≤k ∧
      ∃ Φ : Matrix (Fin (N+1)) (Fin (N+1)) ℂ →ₗ[ℂ]
        Matrix (SubsetIndex k 5) (SubsetIndex k 5) ℂ,
      (CompletelyPositive Φ ∧ TracePreserving Φ) ∧
      (CompletelyPositive (conjugateLinearMap Φ) ∧ TracePreserving (conjugateLinearMap Φ)) ∧
      minimumOutputEntropy p (tensorMap Φ (conjugateMap Φ)) <
        minimumOutputEntropy p Φ+minimumOutputEntropy p (conjugateMap Φ) := by
  obtain ⟨K,hK⟩ := AppendixB.spectral_nonadditivity_all_orders p hp
  obtain ⟨k,hkK⟩ := exists_nat_ge K
  obtain ⟨hk20,hgap⟩ := hK k hkK
  have hk : 0<k := by omega
  letI : NeZero k := ⟨hk.ne'⟩
  have hrk : 4+1≤k := by omega
  letI := nonempty_subsetIndex (show 5≤k by omega)
  have hkt : 1<(k:ℝ)^2*((1:ℝ)/376) := by
    have hkR : (20:ℝ)≤k := by exact_mod_cast hk20
    nlinarith [sq_nonneg ((k:ℝ)-20)]
  have hgapActual : matrixRenyiEntropy p
      (tensorMap (antisymmetricChannel (k:=k) (r:=4))
        (conjugateMap (antisymmetricChannel (k:=k) (r:=4)))
        (isotropic (Fin k) (BellLimitVerification.mixing k ((1:ℝ)/376)))) <
      2*sInf ((fun M=>matrixRenyiEntropy p (antisymmetricChannel (k:=k) (r:=4) M)) ''
        spectralBody k ((1:ℝ)/376)) := by
    rw [antisymmetric_body_infimum hrk _ p hp]
    change matrixRenyiEntropy p (antisymmetricBellLimit k 4 ((1:ℝ)/376)) < _
    rw [antisymmetricBellLimit_entropy (by omega) p hp]
    exact hgap
  obtain ⟨N,Φ,hΦ⟩ := exists_nonadditive_channel_of_postprocessed_body_gap hStrong hk
    (by norm_num : 0<(1:ℝ)/376) (by norm_num : (1:ℝ)/376<1) hkt
    (antisymmetricChannel (k:=k) (r:=4)) (antisymmetricChannel_quantumChannel hrk) p hp hgapActual
  exact ⟨k,N,hk20,Φ,hΦ⟩

#print axioms theorem_I_1
end RevisionMain
