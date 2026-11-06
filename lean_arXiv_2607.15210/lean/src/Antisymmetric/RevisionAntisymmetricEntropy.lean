import Antisymmetric.RevisionAntisymmetricUnitary
import Entropy.RevisionMatrixEntropyConjugate
import OutputStates.RevisionOutputContinuousMinimum
import Entropy.Infimum

/-! Genuine-channel minimum entropy after antisymmetric postprocessing.
All identifications with the scalar shuffle body are proved here. -/

open MeasureTheory Filter Set Matrix PreliminariesMatrix ProjectionChannels ProjectionChannelsCP
open scoped Topology BigOperators ComplexOrder
namespace AntisymmetricVerification
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open RevisionOutput RevisionMatrixEntropy
variable {k r : ℕ}

lemma completelyPositive_posSemidef {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (Φ : Matrix A A ℂ→ₗ[ℂ]Matrix B B ℂ)
    (hΦ : CompletelyPositive Φ) {X : Matrix A A ℂ} (hX : X.PosSemidef) :
    (Φ X).PosSemidef := by
  have h := hΦ Unit (X.submatrix Prod.snd Prod.snd) (hX.submatrix Prod.snd)
  have hh := h.submatrix (fun b:B=>((),b))
  simpa only [amplify,Matrix.submatrix_apply] using hh

lemma antisymmetricChannel_density (hrk : r+1≤k)
    {ρ : Matrix (Fin k) (Fin k) ℂ} (hρ : ρ∈densityMatrices (Fin k)) :
    antisymmetricChannel (r:=r) ρ∈densityMatrices (SubsetIndex k (r+1)) :=
  ⟨completelyPositive_posSemidef antisymmetricChannel antisymmetricChannel_completelyPositive hρ.1,
    (antisymmetricChannel_tracePreserving hrk ρ).trans hρ.2⟩

lemma antisymmetricChannel_continuous : Continuous (antisymmetricChannel (k:=k) (r:=r)) :=
  antisymmetricChannel.continuous_of_finiteDimensional

lemma nonempty_subsetIndex (hrk : r≤k) : Nonempty (SubsetIndex k r) := by
  apply Fintype.card_pos_iff.mp
  rw [card_subsetIndex]
  exact Nat.choose_pos hrk

lemma antisymmetric_entropy_continuousOn (hrk : r+1≤k) (p : ℝ) (hp : 0<p) :
    ContinuousOn (fun M=>matrixRenyiEntropy p (antisymmetricChannel (r:=r) M))
      (densityMatrices (Fin k)) := by
  letI := nonempty_subsetIndex hrk
  exact (matrixRenyiEntropy_continuousOn p hp).comp
    antisymmetricChannel_continuous.continuousOn (fun _ h=>antisymmetricChannel_density hrk h)

/-- Exact equality of the entropy image of the actual postprocessed body
and the shuffle image used in Proposition B.1. -/
theorem antisymmetric_spectralBody_entropy_image (hrk : r+1≤k) (t p : ℝ) (hp : 0<p) :
    (fun M=>matrixRenyiEntropy p (antisymmetricChannel (r:=r) M)) '' spectralBody k t =
      (fun v=>AppendixB.renyi p (AppendixB.subsets k (r+1)) (fun _=>1)
        (AppendixB.shuffle k (r+1) v)) '' AppendixB.Lam k t := by
  ext a
  constructor
  · rintro ⟨M,⟨v,hv,U,rfl⟩,rfl⟩
    exact ⟨v,hv,(antisymmetricChannel_entropy hrk p hp U v).symm⟩
  · rintro ⟨v,hv,rfl⟩
    refine ⟨unitaryDiagonal (1:Matrix.unitaryGroup (Fin k) ℂ) v,⟨v,hv,1,rfl⟩,?_⟩
    exact antisymmetricChannel_entropy hrk p hp 1 v

/-- The actual postprocessed body minimum is exactly the scalar infimum
appearing in the proved large-k estimates. -/
theorem antisymmetric_body_infimum (hrk : r+1≤k) (t p : ℝ) (hp : 0<p) :
    sInf ((fun M=>matrixRenyiEntropy p (antisymmetricChannel (r:=r) M)) '' spectralBody k t)=
      AppendixB.infimumOutputEntropy p t k (r+1) := by
  rw [antisymmetric_spectralBody_entropy_image hrk t p hp]
  unfold AppendixB.infimumOutputEntropy AppendixB.outputEntropyValues
  congr 1
  ext a
  constructor
  · rintro ⟨v,hv,heq⟩
    exact ⟨v,hv,heq.symm⟩
  · rintro ⟨v,hv,heq⟩
    exact ⟨v,hv,heq.symm⟩

/-- The fixed-k single-output entropy limit in Theorem V.1, for the actual
postprocessed normalized Haar-projection channel. -/
theorem actual_antisymmetric_minimum_output_entropy_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t) (r : ℕ) (hrk : r+1≤k)
    (P : Ω→(N:ℕ)→Matrix (Fin (N+1)×Fin k) (Fin (N+1)×Fin k) ℂ)
    (hH : ∀ω N,(P ω N).IsHermitian) (hId : ∀ω N,P ω N*P ω N=P ω N)
    (hStrong : FullBlockModifiedStrongInput μ k t P hH) (p : ℝ) (hp : 0<p) :
    ∀ᵐ ω∂μ, Tendsto (fun N=>minimumOutputEntropy p
      (fun ρ=>antisymmetricChannel (r:=r) (normalizedOutput (P ω N)
        (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))) ρ)))
      atTop (𝓝 (sInf ((fun v=>AppendixB.renyi p (AppendixB.subsets k (r+1)) (fun _=>1)
        (AppendixB.shuffle k (r+1) v)) '' AppendixB.Lam k t))) := by
  have h := output_continuous_minimum_limit μ hk ht ht1 hkt P hH hId hStrong
    (fun M=>matrixRenyiEntropy p (antisymmetricChannel (r:=r) M))
    (antisymmetric_entropy_continuousOn hrk p hp)
  rw [antisymmetric_spectralBody_entropy_image hrk t p hp] at h
  simpa only [minimumOutputEntropy,Set.image_image,Function.comp_def] using h

end
end AntisymmetricVerification
