import BellOutput.RevisionBellSpectralGap
import BellOutput.RevisionBellPositiveLaw
import BellOutput.RevisionBellTraceConvergence
import BellOutput.RevisionBellMatrixLog
import BellOutput.RevisionBellFiniteMoments

/-! Actual normalized logarithmic traces from the sole permitted full
block-modification theorem. The logarithm is handled by a bounded continuous
extension after deriving the positive finite and limiting spectral gaps. -/
open MeasureTheory Filter Set Matrix
open PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace RevisionBell

theorem ae_rotated_logPotential_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH)
    (U : Matrix.unitaryGroup (Fin k) ℂ) (a : Fin k → ℝ)
    (ha : ∀ i, 0<a i) (ν : Measure ℝ)
    (hν : IsBernoulliFreeSumLaw k t a ν)
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      ∀ᵐ ω ∂μ, Tendsto
        (fun n => (1/((n+1 : ℕ) : ℝ))*∑ i,
          f ((rotatedCompressionHermitian k P hH U a ω n).eigenvalues i))
        atTop (nhds (∫ x, f x ∂ν))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => normalizedLogAbsDet
      (blockCompression (diagonalBlock (localConjugate (P ω n) U)) a))
      atTop (nhds (logPotential ν 0)) := by
  letI := hν.probability
  obtain ⟨mν,Mν,hmν,hboundν⟩ := hν.positive_bounds hk ht0 ht1 hkt a ha ν
  obtain ⟨mN,hmN,hgap⟩ := ae_eventually_rotatedCompression_spectral_gap μ hk ht0 ht1 hkt
    P hH hId hFull U a ha
  let m := min mν mN
  let M := max Mν (∑ j, |a j|)
  have hm : 0<m := lt_min hmν hmN
  have hbν : ∀ᵐ x ∂ν, x ∈ Icc m M := by
    filter_upwards [hboundν] with x hx
    exact ⟨(min_le_left _ _).trans hx.1,hx.2.trans (le_max_left _ _)⟩
  obtain ⟨x,hx⟩ := hbν.exists
  have htest := hweak (clippedLog m M) (continuous_clippedLog hm)
    (clippedLog_bounded hm (hx.1.trans hx.2))
  filter_upwards [hgap,htest] with ω hω htestω
  have hb : ∀ᶠ n in atTop, ∀ i,
      (rotatedCompressionHermitian k P hH U a ω n).eigenvalues i ∈ Icc m M := by
    filter_upwards [hω] with n hn
    intro i
    exact ⟨(min_le_right _ _).trans (hn i),
      (rotatedCompression_eigenvalue_upper P hH hId U a ω n i).trans (le_max_right _ _)⟩
  have hh := spectral_log_mean_tendsto_of_clipped
    (fun n => (rotatedCompressionHermitian k P hH U a ω n).eigenvalues) ν m M hm hbν hb
    (by simpa only [Fintype.card_fin,one_div] using htestω)
  have hh' : Tendsto (fun n => (1/((n+1:ℕ):ℝ))*∑ i,
      Real.log ((rotatedCompressionHermitian k P hH U a ω n).eigenvalues i))
      atTop (nhds (logPotential ν 0)) := by
    simpa only [Fintype.card_fin,one_div,logPotential,sub_zero] using hh
  apply hh'.congr'
  filter_upwards [hb] with n hn
  simpa only [Fintype.card_fin] using (normalizedLogAbsDet_eq_spectralMean _
    (rotatedCompressionHermitian k P hH U a ω n) (fun i => hm.trans_le (hn i).1)).symm

lemma rotatedCompression_affine {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A]
    (P : Matrix (A × B) (A × B) ℂ) (H : Matrix B B ℂ) (hH : H.IsHermitian) (x : ℝ) :
    blockCompression (diagonalBlock (localConjugate P hH.eigenvectorUnitary))
      (fun i => 1+x*hH.eigenvalues i) = contraction P (1+(x:ℂ) • H) := by
  rw [affine_matrix_spectral H hH x, ← contraction_localConjugate, contraction_diagonal]
  rfl

lemma positive_affine_coefficients {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    (H : Matrix B B ℂ) (hH : H.IsHermitian) (x : ℝ)
    (hx : |x| * ‖H‖ ≤ 1/2) : ∀ i, 0<1+x*hH.eigenvalues i := by
  intro i
  have he := eigenvalue_abs_le_operator_norm H hH i
  have hp : |x*hH.eigenvalues i| ≤ 1/2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left he (abs_nonneg x)).trans hx
  linarith [neg_abs_le (x*hH.eigenvalues i)]

theorem ae_matrixLogPotential_affine_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH)
    (H : Matrix (Fin k) (Fin k) ℂ) (hHerm : H.IsHermitian)
    (x : ℝ) (hx : |x| * ‖H‖ ≤ 1/2) (ν : Measure ℝ)
    (hν : IsBernoulliFreeSumLaw k t (fun i => 1+x*hHerm.eigenvalues i) ν)
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ y, |f y| ≤ C) →
      ∀ᵐ ω ∂μ, Tendsto
        (fun n => (1/((n+1 : ℕ) : ℝ))*∑ i,
          f ((rotatedCompressionHermitian k P hH hHerm.eigenvectorUnitary
            (fun i => 1+x*hHerm.eigenvalues i) ω n).eigenvalues i))
        atTop (nhds (∫ y, f y ∂ν))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => matrixLogPotential (P ω n) (1+(x:ℂ) • H))
      atTop (nhds (logPotential ν 0)) := by
  have h := ae_rotated_logPotential_tendsto μ hk ht0 ht1 hkt P hH hId hFull
    hHerm.eigenvectorUnitary (fun i => 1+x*hHerm.eigenvalues i)
    (positive_affine_coefficients H hHerm x hx) ν hν hweak
  simpa only [rotatedCompression_affine, matrixLogPotential] using h

end RevisionBell
