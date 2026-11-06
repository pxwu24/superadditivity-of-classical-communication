import BellOutput.RevisionBellQuadraticLimit
import BellOutput.RevisionBellAEPPolarization
import OutputStates.RevisionOutputTheorem

/-! Theorem IV.1 and Proposition A.4, assembled from the one permitted full
block-modified strong-convergence input. All Choi moment and Bell-output
identities are evaluated on the actual matrices and channels. -/
open MeasureTheory Filter Finset
open PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
set_option maxHeartbeats 1200000
namespace RevisionBell

lemma normalizedChoi_isHermitian_unconditionally
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    {P : Matrix (A × B) (A × B) ℂ} (hP : P.IsHermitian)
    (D : Matrix A A ℂ) (hD : D.IsHermitian) : (normalizedChoi P D).IsHermitian := by
  have hK : (Matrix.kronecker D (1 : Matrix B B ℂ)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    rintro ⟨a,i⟩ ⟨b,j⟩
    by_cases hij : i=j
    · subst j
      simpa only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply_eq,mul_one] using hD.apply a b
    · simp [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,hij,Ne.symm hij]
  exact hermitian_sandwich hP hK

/-- The full normalized Choi-block mixed moment in Proposition A.3. -/
theorem ae_normalized_choi_mixed_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH)
    (D : Ω → (n : ℕ) → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hD : ∀ ω n, (D ω n).IsHermitian)
    (hn : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, D ω n*traceB (P ω n)*D ω n=1) :
    ∀ᵐ ω ∂μ, ∀ i j p q : Fin k,
      Tendsto (fun n => (1/((n+1:ℕ):ℂ))*Matrix.trace
        (BellLimitVerification.choiBlock (normalizedChoi (P ω n) (D ω n)) i j*
         BellLimitVerification.choiBlock (normalizedChoi (P ω n) (D ω n)) q p)) atTop
        (nhds (-(BellLimitVerification.hessianC0 k t:ℂ)*(if i=j ∧ p=q then 1 else 0)-
          (BellLimitVerification.hessianC1 k t:ℂ)*(if i=p ∧ j=q then 1 else 0))) := by
  have hq : ∀ H : Matrix (Fin k) (Fin k) ℂ, H.IsHermitian →
      ∀ᵐ ω ∂μ, Tendsto (fun n => (1/(Fintype.card (Fin (n+1)):ℂ))*Matrix.trace
        (choiAdjoint (normalizedChoi (P ω n) (D ω n)) H*
          choiAdjoint (normalizedChoi (P ω n) (D ω n)) H)) atTop
        (nhds (-(BellLimitVerification.hessianC0 k t:ℂ)*Matrix.trace H*Matrix.trace H-
          (BellLimitVerification.hessianC1 k t:ℂ)*Matrix.trace (H*H))) := by
    intro H hHerm
    filter_upwards [ae_normalized_square_moment_limit μ hk ht0 ht1 hkt P hH hId hFull D hD hn H hHerm]
      with ω hω
    simp_rw [choiAdjoint_normalizedChoi]
    exact real_square_moment_limit_to_complex (fun n => Fin (n+1))
      (fun n => D ω n*contraction (P ω n) H*D ω n)
      (fun n => hermitian_sandwich (contraction_isHermitian (hH ω n) hHerm) (hD ω n))
      H hHerm _ _ (by simpa only [Fintype.card_fin] using hω)
  have hm := ae_choi_mixed_moments_of_hermitian_square_limits μ (fun n => Fin (n+1))
    (fun ω n => normalizedChoi (P ω n) (D ω n))
    (BellLimitVerification.hessianC0 k t:ℂ) (BellLimitVerification.hessianC1 k t:ℂ) hq
  simpa only [Fintype.card_fin] using
    (ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun p => ae_all_iff.mpr (fun q => hm i j p q)))))

/-- The Bell norm limit and Choi purity limit for any eventually valid local
normalizer. Only finitely many mixed-moment probability-one events are used. -/
theorem ae_bell_limit_and_choi_purity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH)
    (D : Ω → (n : ℕ) → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hD : ∀ ω n, (D ω n).IsHermitian)
    (hn : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, D ω n*traceB (P ω n)*D ω n=1) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => ‖tensorMap (normalizedOutput (P ω n) (D ω n))
        (conjugateMap (normalizedOutput (P ω n) (D ω n))) (bellState (Fin (n+1)))-
        isotropic (Fin k) (BellLimitVerification.mixing k t)‖) atTop (nhds 0) ∧
      Tendsto (fun n => Matrix.trace (normalizedChoi (P ω n) (D ω n)*normalizedChoi (P ω n) (D ω n))/
        (((n+1:ℕ):ℂ)*(k:ℂ))) atTop (nhds (BellLimitVerification.bellAlpha k t:ℂ)) := by
  have hkR : (Fintype.card (Fin k):ℝ) ≠ 0 := by simpa using (Nat.cast_ne_zero.mpr hk.ne' : (k:ℝ) ≠ 0)
  have hd : BellLimitVerification.denominator (Fintype.card (Fin k)) t ≠ 0 :=
    (BellLimitVerification.denominator_pos ht0 ht1).ne'
  filter_upwards [ae_normalized_choi_mixed_moments μ hk ht0 ht1 hkt P hH hId hFull D hD hn] with ω hω
  constructor
  · simp_rw [normalizedOutput_bell_eq]
    simpa only [Fintype.card_fin] using
      bell_operator_norm_limit_of_mixed_moments (fun n => Fin (n+1))
        (fun n => normalizedChoi (P ω n) (D ω n)) t
        (fun n x y => (normalizedChoi_isHermitian_unconditionally (hH ω n) (D ω n) (hD ω n)).apply y x)
        hkR hd (fun i j p q => by
          simpa only [Fintype.card_fin,sub_eq_add_neg,Complex.ofReal_neg,neg_mul] using hω i j p q)
  · simpa only [Fintype.card_fin] using
      choi_purity_limit_of_mixed_moments (fun n => Fin (n+1))
        (fun n => normalizedChoi (P ω n) (D ω n)) t hkR hd
        (fun i j => by simpa only [Fintype.card_fin,and_self,ite_true,mul_one,Complex.ofReal_neg] using hω i j i j)

/-- **Theorem IV.1 and Proposition A.4.** The normalizer is the actual inverse
positive square root. Eventual invertibility follows from the block theorem,
so it is not assumed. No logarithmic, moment, or isotropy hypothesis remains. -/
theorem bell_output_and_purity_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH) :
    let D := fun ω n => marginalNormalizer (P ω n)
      (HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => ‖tensorMap (normalizedOutput (P ω n) (D ω n))
        (conjugateMap (normalizedOutput (P ω n) (D ω n))) (bellState (Fin (n+1)))-
        isotropic (Fin k) (BellLimitVerification.mixing k t)‖) atTop (nhds 0) ∧
      Tendsto (fun n => Matrix.trace (normalizedChoi (P ω n) (D ω n)*normalizedChoi (P ω n) (D ω n))/
        (((n+1:ℕ):ℂ)*(k:ℂ))) atTop (nhds (BellLimitVerification.bellAlpha k t:ℂ)) := by
  dsimp only
  let hP := fun ω n => HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n)
  let D := fun ω n => marginalNormalizer (P ω n) (hP ω n)
  have hD : ∀ ω n, (D ω n).IsHermitian := fun ω n =>
    (HaarProjection.traceB_posSemidef (P ω n) (hP ω n)).posSemidef_sqrt.isHermitian.inv
  have hBM : AmplifiedBlockModifiedStrongInput μ k t P := by
    have hh := hFull.to_amplified (1 : Matrix.unitaryGroup (Fin k) ℂ)
    change AmplifiedBlockModifiedStrongInput μ k t
      (fun ω n => localConjugate (P ω n) (1 : Matrix (Fin k) (Fin k) ℂ)) at hh
    have heq : (fun ω n => localConjugate (P ω n) (1 : Matrix (Fin k) (Fin k) ℂ)) = P := by
      funext ω n
      exact localConjugate_one (P ω n)
    rw [heq] at hh
    exact hh
  have hpd := ae_eventually_marginal_posDef μ hk ht0 ht1 hkt P hH hId hBM
  have hn : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, D ω n*traceB (P ω n)*D ω n=1 := by
    filter_upwards [hpd] with ω hω
    filter_upwards [hω] with n hn
    exact inverse_sqrt_normalizes hn
  exact ae_bell_limit_and_choi_purity μ hk ht0 ht1 hkt P hH hId hFull D hD hn

/-- Theorem IV.1, stated separately for convenient downstream use. -/
theorem bell_output_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH) :
    let D := fun ω n => marginalNormalizer (P ω n)
      (HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    ∀ᵐ ω ∂μ, Tendsto (fun n => ‖tensorMap (normalizedOutput (P ω n) (D ω n))
      (conjugateMap (normalizedOutput (P ω n) (D ω n))) (bellState (Fin (n+1)))-
      isotropic (Fin k) (BellLimitVerification.mixing k t)‖) atTop (nhds 0) :=
  (bell_output_and_purity_limit μ hk ht0 ht1 hkt P hH hId hFull).mono fun _ h => h.1

/-- Proposition A.4, as a limit of actual full Choi matrix traces. -/
theorem asymptotic_choi_purity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH) :
    let D := fun ω n => marginalNormalizer (P ω n)
      (HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    ∀ᵐ ω ∂μ, Tendsto (fun n =>
      Matrix.trace (normalizedChoi (P ω n) (D ω n)*normalizedChoi (P ω n) (D ω n))/
      (((n+1:ℕ):ℂ)*(k:ℂ))) atTop (nhds (BellLimitVerification.bellAlpha k t:ℂ)) :=
  (bell_output_and_purity_limit μ hk ht0 ht1 hkt P hH hId hFull).mono fun _ h => h.2

/-- **Proposition A.3.** The normalizer is the actual inverse
positive square root. Eventual invertibility follows from the block theorem,
so it is not assumed. No logarithmic, moment, or isotropy hypothesis remains. -/
theorem normalized_choi_mixed_moment_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH) :
    let D := fun ω n => marginalNormalizer (P ω n)
      (HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    ∀ᵐ ω ∂μ, ∀ i j p q : Fin k,
      Tendsto (fun n => (1/((n+1:ℕ):ℂ))*Matrix.trace
        (BellLimitVerification.choiBlock (normalizedChoi (P ω n) (D ω n)) i j*
         BellLimitVerification.choiBlock (normalizedChoi (P ω n) (D ω n)) q p)) atTop
        (nhds (-(BellLimitVerification.hessianC0 k t:ℂ)*(if i=j ∧ p=q then 1 else 0)-
          (BellLimitVerification.hessianC1 k t:ℂ)*(if i=p ∧ j=q then 1 else 0))) := by
  dsimp only
  let hP := fun ω n => HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n)
  let D := fun ω n => marginalNormalizer (P ω n) (hP ω n)
  have hD : ∀ ω n, (D ω n).IsHermitian := fun ω n =>
    (HaarProjection.traceB_posSemidef (P ω n) (hP ω n)).posSemidef_sqrt.isHermitian.inv
  have hBM : AmplifiedBlockModifiedStrongInput μ k t P := by
    have hh := hFull.to_amplified (1 : Matrix.unitaryGroup (Fin k) ℂ)
    change AmplifiedBlockModifiedStrongInput μ k t
      (fun ω n => localConjugate (P ω n) (1 : Matrix (Fin k) (Fin k) ℂ)) at hh
    have heq : (fun ω n => localConjugate (P ω n) (1 : Matrix (Fin k) (Fin k) ℂ)) = P := by
      funext ω n
      exact localConjugate_one (P ω n)
    rw [heq] at hh
    exact hh
  have hpd := ae_eventually_marginal_posDef μ hk ht0 ht1 hkt P hH hId hBM
  have hn : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, D ω n*traceB (P ω n)*D ω n=1 := by
    filter_upwards [hpd] with ω hω
    filter_upwards [hω] with n hn
    exact inverse_sqrt_normalizes hn
  exact ae_normalized_choi_mixed_moments μ hk ht0 ht1 hkt P hH hId hFull D hD hn


end RevisionBell
