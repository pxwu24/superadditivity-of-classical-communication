import StrongConvergence.StrongConvergenceCanonicalConcentration
import StrongConvergence.StrongConvergenceRotationTransfer
import StrongConvergence.StrongConvergenceEdgeBootstrap
import StrongConvergence.StrongConvergenceEdgeSandwich

/-! Actual summable centered tails of the largest compression eigenvalue,
and the upgrade from vanishing outlier probability to an almost-sure upper edge. -/

open Matrix MeasureTheory Filter
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder ENNReal
noncomputable section
namespace ProjectionChannels.Canonical

/-- Uniformly bounded Lipschitz projection tests admit centers with
summable deviations at every positive threshold. -/
theorem exists_projection_observable_center_summable {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (Φ : (n : ℕ) → Matrix (Index k n) (Index k n) ℂ → ℝ)
    (hΦ : ∀ n, Measurable (Φ n)) {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hbound : ∀ n (P : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → P*P = P → |Φ n P| ≤ M)
    (hLip : ∀ n (P Q : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → Q.IsHermitian → P*P = P → Q*Q = Q →
      |Φ n P - Φ n Q| ≤ H * ‖P-Q‖) :
    ∃ center : ℕ → ℝ, ∀ r : ℝ, 0 < r →
      (∑' n, probability k {ω | r ≤ |Φ n (projection k t ω n)-center n|}) ≠ ∞ := by
  choose center hcenter htail using
    fun n => exists_projection_center_exp hk ht0 ht1 n (Φ n) (hΦ n) hH hM (hbound n) (hLip n)
  refine ⟨center, ?_⟩
  intro r hr
  have hdim (n : ℕ) : (n : ℝ) ≤ Fintype.card (Index k n) := by
    exact_mod_cast (show n ≤ Fintype.card (Index k n) by
      simp only [Index, Fintype.card_prod, Fintype.card_fin]
      nlinarith)
  apply StrongConvergenceProbability.tsum_tail_ne_top_of_exponential_bound
    (probability k) _ (show 0 < concentrationRate t H*r^2 from
      mul_pos (concentrationRate_pos t hH) (sq_pos_of_pos hr))
  intro n
  apply (htail n r hr).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (hdim n))) (by norm_num)
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    rw [neg_mul]
    exact mul_le_mul_of_nonpos_left (hdim n)
      (neg_nonpos.mpr (mul_nonneg (concentrationRate_pos t hH).le (sq_nonneg r)))

/-- The shifted norm formula extends the largest compression eigenvalue
to a continuous observable on all matrices. -/
def largestCompressionObservable {E D : Type*} [Fintype E] [Fintype D]
    [DecidableEq E] (a : D → ℝ) (P : Matrix (E × D) (E × D) ℂ) : ℝ :=
  ‖((∑ i, |a i| : ℝ) : ℂ) • (1 : Matrix E E ℂ) + blockCompression (diagonalBlock P) a‖ -
    ∑ i, |a i|

theorem largestCompressionObservable_eq {E D : Type*} [Fintype E] [Fintype D]
    [DecidableEq E] [DecidableEq D] [Nonempty E]
    (a : D → ℝ) (P : Matrix (E × D) (E × D) ℂ) (hP : P.IsHermitian) (hPId : P*P=P) :
    largestCompressionObservable a P =
      largestEigenvalue
        (blockCompression_isHermitian _ (fun i => hP.submatrix (fun e => (e,i))) a) := by
  have he := norm_shift_eq_largest
    (blockCompression_isHermitian _ (fun i => hP.submatrix (fun e => (e,i))) a)
    (∑ i, |a i|) (blockCompression_positive_shift (diagonalBlock P)
      (fun i => (projection_diagonalBlock_contraction P hP hPId i).1)
      (fun i => (projection_diagonalBlock_contraction P hP hPId i).2) a _ le_rfl)
  simpa only [largestCompressionObservable, diagonalBlock, add_sub_cancel_left] using
    congrArg (fun x : ℝ => x-∑ i, |a i|) he

lemma continuous_largestCompressionObservable {E D : Type*} [Fintype E] [Fintype D]
    [DecidableEq E] (a : D → ℝ) :
    Continuous (largestCompressionObservable (E := E) a) :=
  ((continuous_const.add (continuous_projection_compression a)).norm).sub continuous_const

lemma largestCompressionObservable_abs_le {E D : Type*} [Fintype E] [Fintype D]
    [DecidableEq E] [DecidableEq D] [Nonempty E] (a : D → ℝ)
    (P : Matrix (E × D) (E × D) ℂ) (hP : P.IsHermitian) (hPId : P*P=P) :
    |largestCompressionObservable a P| ≤ 3 * ∑ i, |a i| := by
  let K : ℝ := ∑ i, |a i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hS := StrongConvergence.projection_compression_norm_le P hP hPId a
  have hI : ‖(K:ℂ) • (1 : Matrix E E ℂ)‖ ≤ K := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
    exact mul_le_of_le_one_right hK (StrongConvergence.hermitian_idempotent_norm_le_one
      _ Matrix.isHermitian_one (by simp))
  have hnorm := (norm_add_le ((K:ℂ) • (1 : Matrix E E ℂ))
    (blockCompression (diagonalBlock P) a)).trans (add_le_add hI hS)
  unfold largestCompressionObservable
  have h := abs_sub ‖(K:ℂ) • (1 : Matrix E E ℂ) + blockCompression (diagonalBlock P) a‖ K
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hK] at h
  exact h.trans (by dsimp only [K] at *; linarith)

/-- Actual canonical largest eigenvalues have summable centered tails.
The centers arise from the proved Gaussian extension construction. -/
theorem exists_largestCompression_center_summable {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ) :
    ∃ center : ℕ → ℝ, ∀ r : ℝ, 0 < r →
      (∑' n, probability k {ω | r ≤
        |largestEigenvalue (compressionHermitian k t a ω n)-center n|}) ≠ ∞ := by
  let K : ℝ := ∑ i, |a i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  obtain ⟨center, hcenter⟩ := exists_projection_observable_center_summable hk ht0 ht1
    (fun n => largestCompressionObservable (E := Fin (n+1)) a)
    (fun n => (continuous_largestCompressionObservable a).measurable)
    (H := max 1 K) (M := 3*K) (lt_max_of_lt_left zero_lt_one) (by positivity)
    (fun n P hP hPId => largestCompressionObservable_abs_le a P hP hPId)
    (by
      intro n P Q _ _ _ _
      have h := StrongConvergence.affineCompressionNorm_lipschitz P Q a K
      have he : largestCompressionObservable a P-largestCompressionObservable a Q =
          ‖(K:ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) + blockCompression (diagonalBlock P) a‖ -
          ‖(K:ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) + blockCompression (diagonalBlock Q) a‖ := by
        unfold largestCompressionObservable
        dsimp only [K]
        ring
      rw [he]
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right 1 K) (norm_nonneg _)))
  refine ⟨center, ?_⟩
  intro r hr
  have he (n : ℕ) (ω : Sample k) : largestCompressionObservable a (projection k t ω n) =
      largestEigenvalue (compressionHermitian k t a ω n) :=
    largestCompressionObservable_eq a _ (projection_isHermitian k t ω n) (projection_idempotent k t ω n)
  simpa only [he] using hcenter r hr

/-- Vanishing upper outlier probabilities for the actual canonical
compression imply an almost-sure upper spectral edge. The necessary
summable concentration is supplied here, not assumed. -/
theorem ae_largestCompression_upper_of_vanishing_probability {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ) (edge : ℝ)
    (hu : ∀ ε > 0, Tendsto (fun n => probability k
      {ω | edge+ε ≤ largestEigenvalue (compressionHermitian k t a ω n)})
      atTop (𝓝 0)) :
    ∀ᵐ ω ∂probability k, ∀ ε > 0, ∀ᶠ n in atTop,
      largestEigenvalue (compressionHermitian k t a ω n) < edge+ε := by
  obtain ⟨center, hcenter⟩ := exists_largestCompression_center_summable hk ht0 ht1 a
  exact StrongConvergenceProbability.ae_upper_of_vanishing_upper_and_summable_centered_tails
    (probability k) _ center edge hu hcenter

private lemma largestEigenvalue_congr {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    {P Q : Matrix E E ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (heq : P=Q) :
    largestEigenvalue hP = largestEigenvalue hQ := by
  subst Q
  rfl

/-- Negating the coefficients gives precisely the negative Hermitian
compression, so the same concentration upgrade controls the lower edge. -/
theorem largestCompression_neg_coefficients (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (ω : Sample k) (n : ℕ) :
    largestEigenvalue (compressionHermitian k t (fun i => -a i) ω n) =
      largestEigenvalue (compressionHermitian k t a ω n).neg :=
  largestEigenvalue_congr _ _ (StrongConvergence.blockCompression_neg _ a)

theorem ae_neg_compression_upper_of_vanishing_probability {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ) (edge : ℝ)
    (hu : ∀ ε > 0, Tendsto (fun n => probability k
      {ω | edge+ε ≤ largestEigenvalue (compressionHermitian k t (fun i => -a i) ω n)})
      atTop (𝓝 0)) :
    ∀ᵐ ω ∂probability k, ∀ ε > 0, ∀ᶠ n in atTop,
      largestEigenvalue (compressionHermitian k t a ω n).neg < edge+ε := by
  simpa only [largestCompression_neg_coefficients] using
    ae_largestCompression_upper_of_vanishing_probability hk ht0 ht1 (fun i => -a i) edge hu

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.exists_largestCompression_center_summable
#print axioms ProjectionChannels.Canonical.ae_largestCompression_upper_of_vanishing_probability
#print axioms ProjectionChannels.Canonical.ae_neg_compression_upper_of_vanishing_probability
