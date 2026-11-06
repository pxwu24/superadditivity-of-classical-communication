import BellOutput.RevisionBellEntropyTransport
import Entropy.RevisionMatrixEntropyBody
import Entropy.RevisionMatrixEntropyWitness
import Antisymmetric.RevisionAntisymmetricBellBridge

/-! General finite-channel and continuous-objective transport through a fixed
CP/TP postprocessing map. These lemmas apply directly to the actual
antisymmetric channel, with its positivity and trace preservation proved. -/
open MeasureTheory Filter Set Matrix
open PreliminariesMatrix ProjectionChannels ProjectionChannelsCP RevisionOutput RevisionBell
open AntisymmetricVerification RevisionMatrixEntropy
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
noncomputable section
namespace RevisionMain
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

lemma completelyPositive_comp
    (E : Matrix B B ℂ →ₗ[ℂ] Matrix C C ℂ)
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hE : CompletelyPositive E) (hΦ : CompletelyPositive Φ) :
    CompletelyPositive (E.comp Φ) := by
  intro D _ _ X hX
  exact hE D (amplify Φ X) (hΦ D X hX)

lemma tracePreserving_comp
    (E : Matrix B B ℂ →ₗ[ℂ] Matrix C C ℂ)
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hE : TracePreserving E) (hΦ : TracePreserving Φ) :
    TracePreserving (E.comp Φ) := fun X => (hE (Φ X)).trans (hΦ X)

lemma quantumChannel_conjugate
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hΦ : CompletelyPositive Φ ∧ TracePreserving Φ) :
    CompletelyPositive (conjugateLinearMap Φ) ∧ TracePreserving (conjugateLinearMap Φ) := by
  rw [quantumChannel_iff_choi] at hΦ ⊢
  change (choiInput (conjugateMap Φ)).PosSemidef ∧ traceB (choiInput (conjugateMap Φ))=1
  rw [conjugateMap_choi,traceB_entrywiseConjugate,hΦ.2]
  exact ⟨RevisionBell.entrywiseConjugate_posSemidef hΦ.1,
    AntisymmetricVerification.entrywiseConjugate_one⟩

lemma completelyPositive_posSemidef
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (hΦ : CompletelyPositive Φ)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) : (Φ ρ).PosSemidef := by
  have h := hΦ Unit (ρ.submatrix Prod.snd Prod.snd) (hρ.submatrix Prod.snd)
  exact h.submatrix (fun b => ((),b))

lemma quantumChannel_density
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hΦ : CompletelyPositive Φ ∧ TracePreserving Φ)
    {ρ : Matrix A A ℂ} (hρ : ρ ∈ densityMatrices A) : Φ ρ ∈ densityMatrices B :=
  ⟨completelyPositive_posSemidef Φ hΦ.1 hρ.1,(hΦ.2 ρ).trans hρ.2⟩

/-- The paper's normalized channel as an actual complex-linear map. -/
def normalizedChannel (P : Matrix (A×B) (A×B) ℂ) (D : Matrix A A ℂ) :
    Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ := choiChannel (normalizedChoi P D)

lemma normalizedChannel_apply [Nonempty A] [Nonempty B]
    (P : Matrix (A×B) (A×B) ℂ) (D : Matrix A A ℂ) (ρ : Matrix A A ℂ) :
    normalizedChannel P D ρ=normalizedOutput P D ρ := channel_normalizedChoi P D ρ

lemma normalizedChannel_quantumChannel [Nonempty A] [Nonempty B]
    {P : Matrix (A×B) (A×B) ℂ} (hP : P.PosSemidef)
    (D : Matrix A A ℂ) (hD : D.IsHermitian) (hn : D*traceB P*D=1) :
    CompletelyPositive (normalizedChannel P D) ∧ TracePreserving (normalizedChannel P D) :=
  choiChannel_CP_TP (normalizedChoi_posSemidef hP D hD hn) (normalized_choi D P hD hP hn).2

lemma postprocessed_entropy_continuousOn [Nonempty A] [Nonempty B]
    (E : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hE : CompletelyPositive E ∧ TracePreserving E) (p : ℝ) (hp : 0<p) :
    ContinuousOn (fun X => matrixRenyiEntropy p (E X)) (densityMatrices A) := by
  exact (matrixRenyiEntropy_continuousOn p hp).comp
    E.continuous_of_finiteDimensional.continuousOn (fun _ hX => quantumChannel_density E hE hX)

/-- Fixed-k single-output entropy limit after any genuine CP/TP postprocessing.
The objective and output image are actual matrices; no spectral identification
is imposed as a premise. -/
theorem postprocessed_minimum_output_entropy_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH)
    (E : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix B B ℂ) [Nonempty B]
    (hE : CompletelyPositive E ∧ TracePreserving E) (p : ℝ) (hp : 0<p) :
    let D := fun ω n => marginalNormalizer (P ω n)
      (HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    ∀ᵐ ω ∂μ, Tendsto (fun n => minimumOutputEntropy p (E.comp (normalizedChannel (P ω n) (D ω n))))
      atTop (nhds (sInf ((fun X => matrixRenyiEntropy p (E X)) '' spectralBody k t))) := by
  dsimp only
  have h := output_continuous_minimum_limit μ hk ht0 ht1 hkt P hH hId hFull
    (fun X => matrixRenyiEntropy p (E X)) (postprocessed_entropy_continuousOn E hE p hp)
  simpa only [minimumOutputEntropy,← Set.image_comp,Function.comp_def,LinearMap.comp_apply,
    normalizedChannel_apply] using h

lemma normalizedChannel_coe [Nonempty A] [Nonempty B]
    (P : Matrix (A×B) (A×B) ℂ) (D : Matrix A A ℂ) :
    (normalizedChannel P D : Matrix A A ℂ → Matrix B B ℂ)=normalizedOutput P D :=
  funext (normalizedChannel_apply P D)

/-- The actual local normalizer is eventually valid, with invertibility
proved from the sole strong-convergence input. -/
theorem ae_marginalNormalizer_normalizes
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH) :
    let D := fun ω n => marginalNormalizer (P ω n)
      (HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, D ω n*traceB (P ω n)*D ω n=1 := by
  dsimp only
  have hBM : AmplifiedBlockModifiedStrongInput μ k t P := by
    simpa only [Matrix.UnitaryGroup.one_val,localConjugate_one] using hFull.to_amplified 1
  filter_upwards [ae_eventually_marginal_posDef μ hk ht0 ht1 hkt P hH hId hBM] with ω hω
  filter_upwards [hω] with n hn
  exact inverse_sqrt_normalizes hn

end RevisionMain
