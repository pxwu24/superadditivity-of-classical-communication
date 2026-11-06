import Antisymmetric.RevisionPostprocessingTransport
import Entropy.MainSpectral

/-! The finite-channel implication of a strict limiting Bell witness.
Every quantity is the entropy or minimum output entropy of an actual
finite-dimensional CP/TP map. -/
open MeasureTheory Filter Set Matrix
open PreliminariesMatrix ProjectionChannels ProjectionChannelsCP RevisionOutput RevisionBell
open AntisymmetricVerification RevisionMatrixEntropy
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
noncomputable section
namespace RevisionMain

theorem quantum_channel_eventual_nonadditivity
    {B : Type} [Fintype B] [DecidableEq B] [Nonempty B]
    (A : ℕ → Type) [∀ n,Fintype (A n)] [∀ n,DecidableEq (A n)] [∀ n,Nonempty (A n)]
    (Θ : ∀ n, Matrix (A n) (A n) ℂ →ₗ[ℂ] Matrix B B ℂ)
    (p : ℝ) (hp : 0<p) (S Bval : ℝ)
    (hΘ : ∀ᶠ n in atTop, CompletelyPositive (Θ n) ∧ TracePreserving (Θ n))
    (hS : Tendsto (fun n => minimumOutputEntropy p (Θ n)) atTop (nhds S))
    (hB : Tendsto (fun n => matrixRenyiEntropy p
      (tensorMap (Θ n) (conjugateMap (Θ n)) (bellState (A n)))) atTop (nhds Bval))
    (hgap : Bval<2*S) :
    ∀ᶠ n in atTop, (CompletelyPositive (Θ n) ∧ TracePreserving (Θ n)) ∧
      (CompletelyPositive (conjugateLinearMap (Θ n)) ∧ TracePreserving (conjugateLinearMap (Θ n))) ∧
      minimumOutputEntropy p (tensorMap (Θ n) (conjugateMap (Θ n))) <
        minimumOutputEntropy p (Θ n)+minimumOutputEntropy p (conjugateMap (Θ n)) := by
  have hprod : ∀ᶠ n in atTop,
      minimumOutputEntropy p (tensorMap (Θ n) (conjugateMap (Θ n))) ≤
        matrixRenyiEntropy p (tensorMap (Θ n) (conjugateMap (Θ n)) (bellState (A n))) := by
    filter_upwards [hΘ] with n hn
    exact minimumOutputEntropy_tensor_bell_le p hp (Θ n) (conjugateLinearMap (Θ n))
      hn (quantumChannel_conjugate (Θ n) hn)
  have hconj : ∀ᶠ n in atTop,
      minimumOutputEntropy p (conjugateMap (Θ n))=minimumOutputEntropy p (Θ n) := by
    filter_upwards [hΘ] with n hn
    exact minimumOutputEntropy_conjugateMap p hp (Θ n)
      (fun _ hρ => (quantumChannel_density (Θ n) hn hρ).1.isHermitian)
  have he := AppendixB.eventual_nonadditivity_from_limits _ _ _ _ S Bval hS hB hgap hprod hconj
  filter_upwards [hΘ,he] with n hn hg
  exact ⟨hn,quantumChannel_conjugate (Θ n) hn,hg⟩

end RevisionMain
