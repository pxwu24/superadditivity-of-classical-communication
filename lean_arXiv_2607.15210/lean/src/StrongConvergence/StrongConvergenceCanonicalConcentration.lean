import StrongConvergence.StrongConvergenceCanonicalTails
import StrongConvergence.StrongConvergenceExponentialTails
import StrongConvergence.StrongConvergenceGaussGoodEvent
import StrongConvergence.StrongConvergenceGenusMomentLimit

/-!
# Actual canonical concentration and almost-sure moments

The estimates here use the proved Gaussian good-event estimate, Gaussian
concentration, and exact equality with the Haar projection law. No random
convergence or tail assumption is supplied.
-/

open Matrix MeasureTheory Filter GaussianRank
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace ProjectionChannels.Canonical
open GaussConcentration

def concentrationRate (t H : ℝ) : ℝ := gaussianFrameConstant t ^ 2 / (4 * Real.pi^2 * H^2)

lemma concentrationRate_pos (t : ℝ) {H : ℝ} (hH : 0 < H) : 0 < concentrationRate t H := by
  unfold concentrationRate
  have hc := gaussianFrameConstant_pos t
  have hp := Real.pi_pos
  positivity

/-- The clamped extension has exponential canonical tails, and its mean
differs exponentially little from the actual Haar expectation. -/
theorem exists_projection_center_exp {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (n : ℕ)
    (Φ : Matrix (Index k n) (Index k n) ℂ → ℝ) (hΦ : Measurable Φ)
    {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hbound : ∀ P : Matrix (Index k n) (Index k n) ℂ,
      P.IsHermitian → P*P = P → |Φ P| ≤ M)
    (hLip : ∀ P Q : Matrix (Index k n) (Index k n) ℂ,
      P.IsHermitian → Q.IsHermitian → P*P = P → Q*Q = Q →
      |Φ P - Φ Q| ≤ H * ‖P-Q‖) :
    ∃ m : ℝ,
      |m - ∫ ω, Φ (projection k t ω n) ∂probability k| ≤
        4 * M * Real.exp (-(Fintype.card (Index k n) : ℝ)) ∧
      ∀ r : ℝ, 0 < r →
        (probability k).real {ω | r ≤ |Φ (projection k t ω n)-m|} ≤
          2 * Real.exp (-(Fintype.card (Index k n) : ℝ)) +
          2 * Real.exp (-concentrationRate t H * r^2 * Fintype.card (Index k n)) := by
  have hN : 0 < (Fintype.card (Index k n) : ℝ) := by
    exact_mod_cast (show 0 < Fintype.card (Index k n) by
      simpa only [Index, Fintype.card_prod, Fintype.card_fin] using Nat.mul_pos (Nat.succ_pos n) hk)
  have hdim : (Fintype.card (Fin (rankSequence k t n)) : ℝ) ≤
      t * Fintype.card (Index k n) := by
    have h := Nat.floor_le (show 0 ≤ t*((k:ℝ)*(n+1)) by positivity)
    simpa only [Fintype.card_fin, rankSequence, Index, Fintype.card_prod,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm (n+1:ℝ) (k:ℝ)] using h
  have hbad := matrixGaussian_lowerFrame_failure_real (E := Index k n)
    (D := Fin (rankSequence k t n)) t ht0 ht1 hdim
  have hs : 0 < gaussianFrameConstant t * Real.sqrt (Fintype.card (Index k n)) :=
    mul_pos (gaussianFrameConstant_pos t) (Real.sqrt_pos.mpr hN)
  obtain ⟨m, hm, htail⟩ := exists_projection_center ht0 ht1.le n Φ hΦ hH hM hs hbound hLip
  refine ⟨m, hm.trans ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hbad (by positivity)).trans_eq (by ring)
  · intro r hr
    apply (htail r hr).trans
    have he : -((gaussianFrameConstant t * Real.sqrt (Fintype.card (Index k n)))^2*r^2) /
        (4*Real.pi^2*H^2) = -concentrationRate t H*r^2*Fintype.card (Index k n) := by
      rw [mul_pow, Real.sq_sqrt hN.le]
      unfold concentrationRate
      ring
    rw [he]
    exact add_le_add_right hbad _

/-- Every uniformly bounded Lipschitz projection observable concentrates
almost surely about its actual expectation, along the canonical sequence. -/
theorem ae_projection_observable_sub_mean_tendsto_zero {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (Φ : (n : ℕ) → Matrix (Index k n) (Index k n) ℂ → ℝ)
    (hΦ : ∀ n, Measurable (Φ n)) {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hbound : ∀ n (P : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → P*P = P → |Φ n P| ≤ M)
    (hLip : ∀ n (P Q : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → Q.IsHermitian → P*P = P → Q*Q = Q →
      |Φ n P - Φ n Q| ≤ H * ‖P-Q‖) :
    ∀ᵐ ω ∂probability k, Tendsto
      (fun n => Φ n (projection k t ω n) -
        ∫ ω', Φ n (projection k t ω' n) ∂probability k) atTop (𝓝 0) := by
  choose center hcenter htail using
    fun n => exists_projection_center_exp hk ht0 ht1 n (Φ n) (hΦ n) hH hM (hbound n) (hLip n)
  have hdim (n : ℕ) : (n : ℝ) ≤ Fintype.card (Index k n) := by
    exact_mod_cast (show n ≤ Fintype.card (Index k n) by
      simp only [Index, Fintype.card_prod, Fintype.card_fin]
      nlinarith)
  apply StrongConvergenceProbability.ae_tendsto_sub_mean_of_exponential_tails
    (probability k) _ center _ (concentrationRate_pos t hH)
  · intro n
    exact (hcenter n).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (hdim n))) (by positivity : 0 ≤ 4*M))
  · intro r hr n
    apply (htail n r hr).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (hdim n)))
        (by norm_num)
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hdim n)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (concentrationRate_pos t hH).le)
          (sq_nonneg r))

lemma continuous_projection_compression {E D : Type*} [Fintype E] [Fintype D]
    (a : D → ℝ) : Continuous
      (fun P : Matrix (E × D) (E × D) ℂ => blockCompression (diagonalBlock P) a) := by
  unfold blockCompression diagonalBlock
  exact continuous_finset_sum _ (fun i _ => continuous_const.smul
    (continuous_id.matrix_submatrix (fun x => (x,i)) (fun x => (x,i))))

/-- Affine operator norms of the actual canonical block compression have
almost-sure fluctuations tending to zero. -/
theorem ae_affineCompressionNorm_sub_mean_tendsto_zero {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ) (c : ℝ) :
    ∀ᵐ ω ∂probability k, Tendsto
      (fun n => ‖(c : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
        blockCompression (diagonalBlock (projection k t ω n)) a‖ -
        ∫ ω', ‖(c : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
          blockCompression (diagonalBlock (projection k t ω' n)) a‖ ∂probability k)
      atTop (𝓝 0) := by
  let K : ℝ := ∑ i, |a i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply ae_projection_observable_sub_mean_tendsto_zero hk ht0 ht1
    (fun n P => ‖(c : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
      blockCompression (diagonalBlock P) a‖)
    (fun n => (continuous_const.add (continuous_projection_compression a)).norm.measurable)
    (H := max 1 K) (M := |c|+K) (lt_max_of_lt_left zero_lt_one) (by positivity)
  · intro n P hP hPId
    rw [abs_of_nonneg (norm_nonneg _)]
    calc
      _ ≤ ‖(c : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)‖ +
          ‖blockCompression (diagonalBlock P) a‖ := norm_add_le _ _
      _ ≤ |c| + K := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        apply add_le_add _ (StrongConvergence.projection_compression_norm_le P hP hPId a)
        exact mul_le_of_le_one_right (abs_nonneg _) (StrongConvergence.hermitian_idempotent_norm_le_one
          _ Matrix.isHermitian_one (by simp))
  · intro n P Q _ _ _ _
    exact (StrongConvergence.affineCompressionNorm_lipschitz P Q a c).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 K) (norm_nonneg _))

/-- Positive normalized trace moments concentrate about their actual Haar
expectations on one probability-one event for every fixed degree. -/
theorem ae_compressionMoment_sub_mean_tendsto_zero {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ) (m : ℕ) :
    ∀ᵐ ω ∂probability k, Tendsto
      (fun n => (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^(m+1))).re /
          ((n:ℝ)+1) -
        ∫ ω', (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω' n)) a)^(m+1))).re /
          ((n:ℝ)+1) ∂probability k) atTop (𝓝 0) := by
  let K : ℝ := ∑ i, |a i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply ae_projection_observable_sub_mean_tendsto_zero hk ht0 ht1
    (fun n P => (Matrix.trace ((blockCompression (diagonalBlock P) a)^(m+1))).re / ((n:ℝ)+1))
    (fun n => ((Complex.continuous_re.comp
      ((continuous_projection_compression a).pow (m+1)).matrix_trace).div_const _).measurable)
    (H := max 1 (((m+1:ℕ):ℝ)*K^(m+1))) (M := K^(m+1))
    (lt_max_of_lt_left zero_lt_one) (by positivity)
  · intro n P hP hPId
    have hb := StrongConvergence.abs_normalized_real_trace_le
      ((blockCompression (diagonalBlock P) a)^(m+1))
      ((blockCompression_isHermitian _ (fun i => hP.submatrix (fun e => (e,i))) a).pow _)
    have hnorm := (norm_pow_le' (blockCompression (diagonalBlock P) a) (Nat.succ_pos m)).trans
      (pow_le_pow_left₀ (norm_nonneg _) (StrongConvergence.projection_compression_norm_le P hP hPId a) _)
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hb.trans hnorm
  · intro n P Q hP hQ hPId hQId
    have hl := StrongConvergence.compressionMoment_lipschitz P Q hP hQ hPId hQId a m
    apply le_trans (b := ((m+1:ℕ):ℝ)*K^(m+1)*‖P-Q‖)
    · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hl
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

lemma integral_normalized_compressionMoment_eq_re_expected (k : ℕ) (t : ℝ)
    (a : Fin k → ℝ) (n m : ℕ) :
    (∫ ω, (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^(m+1))).re /
      ((n:ℝ)+1) ∂probability k) = (expectedNormalizedMoment k t n m a).re := by
  have hi : Integrable (fun ω : Sample k => Matrix.trace
      ((blockCompression (diagonalBlock (projection k t ω n)) a)^(m+1))) (probability k) :=
    ((TensorHaar.continuous_compression_trace_power (baseProjection k t n) a m).comp
      (continuous_apply n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_div]
  change (∫ ω, RCLike.re (Matrix.trace
      ((blockCompression (diagonalBlock (projection k t ω n)) a)^(m+1))) ∂probability k) /
      ((n:ℝ)+1) = _
  rw [integral_re hi]
  unfold expectedNormalizedMoment
  rw [show ((n+1:ℕ):ℂ) = (((n:ℝ)+1):ℂ) by push_cast; rfl]
  simpa only [Complex.ofReal_add, Complex.ofReal_one] using
    (Complex.div_ofReal_re (∫ ω : Sample k, Matrix.trace
      ((blockCompression (diagonalBlock (projection k t ω n)) a)^(m+1)) ∂probability k)
      ((n:ℝ)+1)).symm

/-- All positive normalized trace moments of the canonical ensemble
converge simultaneously almost surely to the actual genus-zero coefficients. -/
theorem ae_compressionMoment_tendsto_genus {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin k → ℝ) :
    ∀ᵐ ω ∂probability k, ∀ m : ℕ, Tendsto
      (fun n => (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^(m+1))).re /
        ((n:ℝ)+1)) atTop (𝓝 ((TensorHaar.genusRankCoefficient k (m+1) a 0).eval t)) := by
  apply ae_all_iff.mpr
  intro m
  have hmean := (Complex.continuous_re.tendsto _).comp
    (expectedNormalizedMoment_tendsto_genus hk ht0 ht1.le m a)
  simp only [Complex.ofReal_re] at hmean
  filter_upwards [ae_compressionMoment_sub_mean_tendsto_zero hk ht0 ht1 a m] with ω hω
  simp_rw [integral_normalized_compressionMoment_eq_re_expected] at hω
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hω.add hmean

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.exists_projection_center_exp
#print axioms ProjectionChannels.Canonical.ae_projection_observable_sub_mean_tendsto_zero
#print axioms ProjectionChannels.Canonical.ae_affineCompressionNorm_sub_mean_tendsto_zero
#print axioms ProjectionChannels.Canonical.ae_compressionMoment_tendsto_genus
