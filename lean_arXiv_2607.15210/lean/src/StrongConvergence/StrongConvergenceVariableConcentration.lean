import StrongConvergence.StrongConvergenceCanonicalConcentration
import StrongConvergence.StrongConvergenceCanonicalEdgeConcentration
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Uniform Gaussian concentration for convergent sequences of projection
rank densities. Finitely many initial densities require no constraints. -/

open Matrix MeasureTheory Filter GaussianRank
open scoped Topology BigOperators ENNReal Matrix.L2OpNorm ComplexOrder
noncomputable section

namespace StrongConvergenceProbability

theorem tsum_tail_ne_top_of_eventually_exponential_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : ℕ → Set Ω) {a : ℝ} (ha : 0 < a)
    (hbound : ∀ᶠ n in atTop, μ.real (E n) ≤
      2 * Real.exp (-(n : ℝ)) + 2 * Real.exp (-a*(n : ℝ))) :
    (∑' n, μ (E n)) ≠ ∞ := by
  have hs : Summable (fun n : ℕ =>
      2 * Real.exp (-(n : ℝ)) + 2 * Real.exp (-a*(n : ℝ))) := by
    apply (Real.summable_exp_neg_nat.mul_left 2).add
    have h := (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha)).mul_left 2
    simpa only [mul_comm (-a)] using h
  have hreal : Summable (fun n => μ.real (E n)) :=
    Summable.of_norm_bounded_eventually_nat _ hs (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)] using hbound)
  have he : (∑' n, μ (E n)) = ENNReal.ofReal (∑' n, μ.real (E n)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => measureReal_nonneg) hreal]
    exact tsum_congr (fun n => (ENNReal.ofReal_toReal (measure_ne_top μ (E n))).symm)
  rw [he]
  exact ENNReal.ofReal_ne_top

theorem ae_tendsto_sub_mean_of_eventually_exponential_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℕ → ℝ) (center mean : ℕ → ℝ)
    {C α : ℝ} (hα : 0 < α)
    (hcenter : ∀ᶠ n in atTop, |center n-mean n| ≤ C*Real.exp (-(n : ℝ)))
    (htail : ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
      μ.real {ω | r ≤ |X ω n-center n|} ≤
        2 * Real.exp (-(n : ℝ)) + 2 * Real.exp (-α*r^2*(n : ℝ))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X ω n-mean n) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => center n-mean n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (by simpa only [Real.norm_eq_abs] using hcenter)
    simpa only [mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul C
  have hx := ae_countable_tendsto_of_summable_deviations μ
    (fun ω n (_ : Unit) => X ω n-center n) (fun _ => (0 : ℝ)) (by
      intro i m
      apply tsum_tail_ne_top_of_eventually_exponential_bound μ _
        (show 0 < α*(1/((m:ℝ)+1))^2 by positivity)
      simpa only [Real.dist_eq, sub_zero, neg_mul] using htail (1/((m:ℝ)+1)) (by positivity))
  filter_upwards [hx] with ω hω
  simpa only [sub_add_sub_cancel, add_zero] using (hω ()).add hc

end StrongConvergenceProbability

namespace ProjectionChannels.Canonical
open GaussConcentration

/-- One density cap below one gives uniform concentration for every
smaller nonnegative rank density. -/
theorem exists_projection_center_uniform_density {k : ℕ} {u T : ℝ}
    (hk : 0 < k) (hu0 : 0 ≤ u) (huT : u ≤ T) (hT : T < 1) (n : ℕ)
    (Φ : Matrix (Index k n) (Index k n) ℂ → ℝ) (hΦ : Measurable Φ)
    {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hbound : ∀ P : Matrix (Index k n) (Index k n) ℂ,
      P.IsHermitian → P*P = P → |Φ P| ≤ M)
    (hLip : ∀ P Q : Matrix (Index k n) (Index k n) ℂ,
      P.IsHermitian → Q.IsHermitian → P*P = P → Q*Q = Q →
      |Φ P - Φ Q| ≤ H * ‖P-Q‖) :
    ∃ m : ℝ,
      |m - ∫ ω, Φ (projection k u ω n) ∂probability k| ≤
        4 * M * Real.exp (-(Fintype.card (Index k n) : ℝ)) ∧
      ∀ r : ℝ, 0 < r →
        (probability k).real {ω | r ≤ |Φ (projection k u ω n)-m|} ≤
          2 * Real.exp (-(Fintype.card (Index k n) : ℝ)) +
          2 * Real.exp (-concentrationRate T H * r^2 * Fintype.card (Index k n)) := by
  have hN : 0 < (Fintype.card (Index k n) : ℝ) := by
    exact_mod_cast (show 0 < Fintype.card (Index k n) by
      simpa only [Index, Fintype.card_prod, Fintype.card_fin] using Nat.mul_pos (Nat.succ_pos n) hk)
  have hdim : (Fintype.card (Fin (rankSequence k u n)) : ℝ) ≤
      T * Fintype.card (Index k n) := by
    apply le_trans (b := u * Fintype.card (Index k n))
    · have h := Nat.floor_le (show 0 ≤ u*((k:ℝ)*(n+1)) by positivity)
      simpa only [Fintype.card_fin, rankSequence, Index, Fintype.card_prod,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm (n+1:ℝ) (k:ℝ)] using h
    · exact mul_le_mul_of_nonneg_right huT hN.le
  have hbad := matrixGaussian_lowerFrame_failure_real (E := Index k n)
    (D := Fin (rankSequence k u n)) T (hu0.trans huT) hT hdim
  have hs : 0 < gaussianFrameConstant T * Real.sqrt (Fintype.card (Index k n)) :=
    mul_pos (gaussianFrameConstant_pos T) (Real.sqrt_pos.mpr hN)
  obtain ⟨m, hm, htail⟩ := exists_projection_center hu0 (huT.trans hT.le) n Φ hΦ hH hM hs hbound hLip
  refine ⟨m, hm.trans ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hbad (by positivity)).trans_eq (by ring)
  · intro r hr
    apply (htail r hr).trans
    have he : -((gaussianFrameConstant T * Real.sqrt (Fintype.card (Index k n)))^2*r^2) /
        (4*Real.pi^2*H^2) = -concentrationRate T H*r^2*Fintype.card (Index k n) := by
      rw [mul_pow, Real.sq_sqrt hN.le]
      unfold concentrationRate
      ring
    rw [he]
    exact add_le_add_right hbad _

/-- A convergent density sequence has centers with a single uniform
exponential concentration rate from some index onward. -/
theorem exists_variable_projection_centers {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℕ → ℝ) (hst : Tendsto s atTop (𝓝 t))
    (Φ : (n : ℕ) → Matrix (Index k n) (Index k n) ℂ → ℝ)
    (hΦ : ∀ n, Measurable (Φ n)) {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hbound : ∀ n (P : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → P*P = P → |Φ n P| ≤ M)
    (hLip : ∀ n (P Q : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → Q.IsHermitian → P*P = P → Q*Q = Q →
      |Φ n P - Φ n Q| ≤ H * ‖P-Q‖) :
    ∃ center : ℕ → ℝ,
      (∀ᶠ n in atTop, |center n - ∫ ω, Φ n (projection k (s n) ω n) ∂probability k| ≤
        4*M*Real.exp (-(n:ℝ))) ∧
      ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
        (probability k).real {ω | r ≤ |Φ n (projection k (s n) ω n)-center n|} ≤
          2*Real.exp (-(n:ℝ)) + 2*Real.exp (-concentrationRate ((1+t)/2) H*r^2*(n:ℝ)) := by
  let T := (1+t)/2
  have hT : T < 1 := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hvalid : ∀ᶠ n in atTop, 0 ≤ s n ∧ s n ≤ T := by
    filter_upwards [hst.eventually (Ioi_mem_nhds ht0), hst.eventually (Iio_mem_nhds htT)]
      with n hn0 hnT
    exact ⟨le_of_lt hn0, le_of_lt hnT⟩
  have hex (n : ℕ) : ∃ m : ℝ, (0 ≤ s n ∧ s n ≤ T) →
      |m - ∫ ω, Φ n (projection k (s n) ω n) ∂probability k| ≤
        4*M*Real.exp (-(Fintype.card (Index k n):ℝ)) ∧
      ∀ r : ℝ, 0 < r →
        (probability k).real {ω | r ≤ |Φ n (projection k (s n) ω n)-m|} ≤
          2*Real.exp (-(Fintype.card (Index k n):ℝ)) +
          2*Real.exp (-concentrationRate T H*r^2*Fintype.card (Index k n)) := by
    by_cases hn : 0 ≤ s n ∧ s n ≤ T
    · obtain ⟨m, hm, htail⟩ := exists_projection_center_uniform_density hk hn.1 hn.2 hT n
        (Φ n) (hΦ n) hH hM (hbound n) (hLip n)
      exact ⟨m, fun _ => ⟨hm, htail⟩⟩
    · exact ⟨0, fun h => (hn h).elim⟩
  choose center hcenter using hex
  have hdim (n : ℕ) : (n : ℝ) ≤ Fintype.card (Index k n) := by
    exact_mod_cast (show n ≤ Fintype.card (Index k n) by
      simp only [Index, Fintype.card_prod, Fintype.card_fin]
      nlinarith)
  refine ⟨center, ?_, ?_⟩
  · filter_upwards [hvalid] with n hn
    exact ((hcenter n hn).1).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (hdim n))) (by positivity : 0 ≤ 4*M))
  · intro r hr
    filter_upwards [hvalid] with n hn
    apply ((hcenter n hn).2 r hr).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (hdim n))) (by norm_num)
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hdim n)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (concentrationRate_pos T hH).le)
          (sq_nonneg r))

theorem ae_variable_projection_observable_sub_mean_tendsto_zero {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℕ → ℝ) (hst : Tendsto s atTop (𝓝 t))
    (Φ : (n : ℕ) → Matrix (Index k n) (Index k n) ℂ → ℝ)
    (hΦ : ∀ n, Measurable (Φ n)) {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hbound : ∀ n (P : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → P*P = P → |Φ n P| ≤ M)
    (hLip : ∀ n (P Q : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → Q.IsHermitian → P*P = P → Q*Q = Q →
      |Φ n P - Φ n Q| ≤ H * ‖P-Q‖) :
    ∀ᵐ ω ∂probability k, Tendsto
      (fun n => Φ n (projection k (s n) ω n) -
        ∫ ω', Φ n (projection k (s n) ω' n) ∂probability k) atTop (𝓝 0) := by
  obtain ⟨center, hcenter, htail⟩ := exists_variable_projection_centers hk ht0 ht1 s hst
    Φ hΦ hH hM hbound hLip
  exact StrongConvergenceProbability.ae_tendsto_sub_mean_of_eventually_exponential_tails
    (probability k) _ center _ (concentrationRate_pos _ hH) hcenter htail

theorem exists_variable_projection_observable_center_summable {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℕ → ℝ) (hst : Tendsto s atTop (𝓝 t))
    (Φ : (n : ℕ) → Matrix (Index k n) (Index k n) ℂ → ℝ)
    (hΦ : ∀ n, Measurable (Φ n)) {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hbound : ∀ n (P : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → P*P = P → |Φ n P| ≤ M)
    (hLip : ∀ n (P Q : Matrix (Index k n) (Index k n) ℂ),
      P.IsHermitian → Q.IsHermitian → P*P = P → Q*Q = Q →
      |Φ n P - Φ n Q| ≤ H * ‖P-Q‖) :
    ∃ center : ℕ → ℝ, ∀ r : ℝ, 0 < r →
      (∑' n, probability k {ω | r ≤ |Φ n (projection k (s n) ω n)-center n|}) ≠ ∞ := by
  obtain ⟨center, _, htail⟩ := exists_variable_projection_centers hk ht0 ht1 s hst
    Φ hΦ hH hM hbound hLip
  refine ⟨center, fun r hr => ?_⟩
  apply StrongConvergenceProbability.tsum_tail_ne_top_of_eventually_exponential_bound
    (probability k) _ (mul_pos (concentrationRate_pos ((1+t)/2) hH) (sq_pos_of_pos hr))
  simpa only [neg_mul] using htail r hr

/-- Every fixed positive moment has almost-sure fluctuations tending to zero
for arbitrary convergent interior rank densities. -/
theorem ae_variable_compressionMoment_sub_mean_tendsto_zero {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℕ → ℝ) (hst : Tendsto s atTop (𝓝 t)) (a : Fin k → ℝ) (m : ℕ) :
    ∀ᵐ ω ∂probability k, Tendsto
      (fun n => (Matrix.trace ((blockCompression (diagonalBlock (projection k (s n) ω n)) a)^(m+1))).re /
          ((n:ℝ)+1) -
        ∫ ω', (Matrix.trace ((blockCompression (diagonalBlock (projection k (s n) ω' n)) a)^(m+1))).re /
          ((n:ℝ)+1) ∂probability k) atTop (𝓝 0) := by
  let K : ℝ := ∑ i, |a i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply ae_variable_projection_observable_sub_mean_tendsto_zero hk ht0 ht1 s hst
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


/-- Largest eigenvalues admit summable centers uniformly along every
convergent interior density sequence. -/
theorem exists_variable_largestCompression_center_summable {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℕ → ℝ) (hst : Tendsto s atTop (𝓝 t)) (a : Fin k → ℝ) :
    ∃ center : ℕ → ℝ, ∀ r : ℝ, 0 < r →
      (∑' n, probability k {ω | r ≤
        |largestEigenvalue (compressionHermitian k (s n) a ω n)-center n|}) ≠ ∞ := by
  let K : ℝ := ∑ i, |a i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  obtain ⟨center, hcenter⟩ := exists_variable_projection_observable_center_summable hk ht0 ht1 s hst
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
  have he (n : ℕ) (ω : Sample k) : largestCompressionObservable a (projection k (s n) ω n) =
      largestEigenvalue (compressionHermitian k (s n) a ω n) :=
    largestCompressionObservable_eq a _ (projection_isHermitian k (s n) ω n) (projection_idempotent k (s n) ω n)
  simpa only [he] using hcenter r hr

/-- Vanishing upper outlier probabilities for the actual canonical
compression imply an almost-sure upper spectral edge. The necessary
summable concentration is supplied here, not assumed. -/
theorem ae_variable_largestCompression_upper_of_vanishing_probability {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℕ → ℝ) (hst : Tendsto s atTop (𝓝 t)) (a : Fin k → ℝ) (edge : ℝ)
    (hu : ∀ ε > 0, Tendsto (fun n => probability k
      {ω | edge+ε ≤ largestEigenvalue (compressionHermitian k (s n) a ω n)})
      atTop (𝓝 0)) :
    ∀ᵐ ω ∂probability k, ∀ ε > 0, ∀ᶠ n in atTop,
      largestEigenvalue (compressionHermitian k (s n) a ω n) < edge+ε := by
  obtain ⟨center, hcenter⟩ := exists_variable_largestCompression_center_summable hk ht0 ht1 s hst a
  exact StrongConvergenceProbability.ae_upper_of_vanishing_upper_and_summable_centered_tails
    (probability k) _ center edge hu hcenter

theorem ae_variable_neg_compression_upper_of_vanishing_probability {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℕ → ℝ) (hst : Tendsto s atTop (𝓝 t)) (a : Fin k → ℝ) (edge : ℝ)
    (hu : ∀ ε > 0, Tendsto (fun n => probability k
      {ω | edge+ε ≤ largestEigenvalue (compressionHermitian k (s n) (fun i => -a i) ω n)})
      atTop (𝓝 0)) :
    ∀ᵐ ω ∂probability k, ∀ ε > 0, ∀ᶠ n in atTop,
      largestEigenvalue (compressionHermitian k (s n) a ω n).neg < edge+ε := by
  simpa only [largestCompression_neg_coefficients] using
    ae_variable_largestCompression_upper_of_vanishing_probability hk ht0 ht1 s hst (fun i => -a i) edge hu

theorem exists_variable_shiftedCompressionNorm_center_summable {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℕ → ℝ) (hst : Tendsto s atTop (𝓝 t)) (a : Fin k → ℝ) (c : ℝ) :
    ∃ center : ℕ → ℝ, ∀ r : ℝ, 0 < r →
      (∑' n, probability k {ω | r ≤
        |‖(c : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
          blockCompression (diagonalBlock (projection k (s n) ω n)) a‖ - center n|}) ≠ ∞ := by
  let K : ℝ := ∑ i, |a i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply exists_variable_projection_observable_center_summable hk ht0 ht1 s hst
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

theorem exists_variable_compressionMoment_center_summable {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℕ → ℝ) (hst : Tendsto s atTop (𝓝 t)) (a : Fin k → ℝ) (m : ℕ) :
    ∃ center : ℕ → ℝ, ∀ r : ℝ, 0 < r →
      (∑' n, probability k {ω | r ≤
        |(Matrix.trace ((blockCompression (diagonalBlock (projection k (s n) ω n)) a)^(m+1))).re /
          ((n:ℝ)+1) - center n|}) ≠ ∞ := by
  let K : ℝ := ∑ i, |a i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply exists_variable_projection_observable_center_summable hk ht0 ht1 s hst
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

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.exists_projection_center_uniform_density
#print axioms ProjectionChannels.Canonical.ae_variable_projection_observable_sub_mean_tendsto_zero
#print axioms ProjectionChannels.Canonical.exists_variable_projection_observable_center_summable

#print axioms ProjectionChannels.Canonical.ae_variable_compressionMoment_sub_mean_tendsto_zero

#print axioms ProjectionChannels.Canonical.exists_variable_largestCompression_center_summable
#print axioms ProjectionChannels.Canonical.ae_variable_largestCompression_upper_of_vanishing_probability
#print axioms ProjectionChannels.Canonical.ae_variable_neg_compression_upper_of_vanishing_probability

#print axioms ProjectionChannels.Canonical.exists_variable_shiftedCompressionNorm_center_summable
#print axioms ProjectionChannels.Canonical.exists_variable_compressionMoment_center_summable
