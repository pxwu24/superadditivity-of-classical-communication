import StrongConvergence.StrongConvergencePowerSeriesEvaluation
import StrongConvergence.StrongConvergenceFreeCumulantAnalytic
import StrongConvergence.StrongConvergenceCauchyMoments

open PowerSeries MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels
open PowerSeriesEvaluation FreeCumulant

/-- Cumulants of the `k` copies of each of the `k` scaled Bernoulli variables.
The coefficient of order `r` is `k * ∑ i, (a i / k)^r * κ_r(t)`. -/
def freeSumCumulantSeries (k : ℕ) (t : ℝ) (a : Fin k → ℝ) : PowerSeries ℝ :=
  ∑ i, C ℝ (k : ℝ) * rescale (a i / k) (bernoulliCumulantSeries t)

@[simp] theorem coeff_freeSumCumulantSeries (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (r : ℕ) :
    coeff ℝ r (freeSumCumulantSeries k t a) =
      (k : ℝ) * ∑ i, (a i / k) ^ r * bernoulliCumulant t r := by
  simp only [freeSumCumulantSeries, map_sum, coeff_C_mul, coeff_rescale,
    coeff_bernoulliCumulantSeries, Finset.mul_sum]

@[simp] theorem constantCoeff_freeSumCumulantSeries (k : ℕ) (t : ℝ) (a : Fin k → ℝ) :
    constantCoeff ℝ (freeSumCumulantSeries k t a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_freeSumCumulantSeries]
  simp

theorem absSummable_freeSumCumulantSeries {k : ℕ} {t z : ℝ} {a : Fin k → ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hz : ∀i, |(a i / k) * z| < 1 / 8) :
    AbsSummable (freeSumCumulantSeries k t a) z := by
  apply AbsSummable.sum
  intro i _
  apply (absSummable_C _ _).mul
  rw [absSummable_rescale_iff]
  simpa only [AbsSummable, coeff_bernoulliCumulantSeries] using
    summable_abs_bernoulliCumulant ht0 ht1 (hz i)

theorem eval_freeSumCumulantSeries {k : ℕ} {t z : ℝ} {a : Fin k → ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hz : ∀i, |(a i / k) * z| ≤ 1 / 16) :
    PowerSeriesEvaluation.eval (freeSumCumulantSeries k t a) z =
      z * bernoulliFreeSumR k t a z := by
  have hi (i : Fin k) : AbsSummable (rescale (a i / (k : ℝ)) (bernoulliCumulantSeries t)) z := by
    rw [absSummable_rescale_iff]
    simpa only [AbsSummable, coeff_bernoulliCumulantSeries] using
      summable_abs_bernoulliCumulant ht0 ht1 (show |a i / (k : ℝ) * z| < 1/8 by
        linarith [hz i])
  rw [freeSumCumulantSeries, eval_sum Finset.univ _ (fun i _ => (absSummable_C _ _).mul (hi i))]
  unfold bernoulliFreeSumR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_mul (absSummable_C _ _) (hi i), eval_C, eval_rescale]
  have heval : PowerSeriesEvaluation.eval (bernoulliCumulantSeries t) ((a i / k) * z) =
      bernoulliDual t ((a i / k) * z) := by
    simpa only [PowerSeriesEvaluation.eval, coeff_bernoulliCumulantSeries] using
      (bernoulliDual_eq_cumulant_sum ht0 ht1 (hz i)).symm
  rw [heval, ← bernoulliR_mul]
  ring

/-- The moment series of an actual probability law. -/
def lawMomentSeries (ν : Measure ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n : ℕ => ∫ y, y ^ n ∂ν)

@[simp] theorem coeff_lawMomentSeries (ν : Measure ℝ) (n : ℕ) :
    coeff ℝ n (lawMomentSeries ν) = ∫ y, y^n ∂ν := by
  simp [lawMomentSeries]

@[simp] theorem constantCoeff_lawMomentSeries (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    constantCoeff ℝ (lawMomentSeries ν) = 1 := by
  simp [lawMomentSeries]

theorem absSummable_lawMomentSeries (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {K z : ℝ} (hK : 0 ≤ K) (hs : ∀ᵐ y ∂ν, |y| ≤ K) (hz : K * |z| < 1) :
    AbsSummable (lawMomentSeries ν) z := by
  simpa only [AbsSummable, coeff_lawMomentSeries, Real.norm_eq_abs] using
    summable_norm_moments ν hK hs hz

theorem absSum_lawMomentSeries_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {K z : ℝ} (hK : 0 ≤ K) (hs : ∀ᵐ y ∂ν, |y| ≤ K) (hz : K * |z| < 1) :
    absSum (lawMomentSeries ν) z ≤ (1 - K * |z|)⁻¹ := by
  have hq : |K * abs z| < 1 := by rw [abs_of_nonneg (by positivity)]; exact hz
  have hgeo := summable_geometric_of_abs_lt_one hq
  calc
    _ ≤ ∑' n : ℕ, (K * |z|)^n := by
      apply Summable.tsum_le_tsum _ (absSummable_lawMomentSeries ν hK hs hz) hgeo
      intro n
      rw [coeff_lawMomentSeries, abs_mul, abs_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right (abs_moment_le_of_support ν hs n) (by positivity)
    _ = _ := tsum_geometric_of_abs_lt_one hq

/-- Evaluating the formal moment-cumulant identity proves the inverse-Cauchy
formula at every sufficiently remote point, on either side of the support. -/
theorem law_inverse_of_formal_identity_at (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {k : ℕ} {t K x : ℝ} {a : Fin k → ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (hs : ∀ᵐ y ∂ν, |y| ≤ K)
    (hformal : formalSubst (X * lawMomentSeries ν) (by simp)
      (freeSumCumulantSeries k t a) = lawMomentSeries ν - 1)
    (hx : K < |x|) (hsmall : K * |x⁻¹| ≤ 1/2)
    (hscale : ∀i, |(a i / k) * x⁻¹| ≤ 1/32) :
    (realCauchyTransform ν x)⁻¹ +
      bernoulliFreeSumR k t a (realCauchyTransform ν x) = x := by
  let M := lawMomentSeries ν
  let W : PowerSeries ℝ := X * M
  have hW0 : constantCoeff ℝ W = 0 := by simp [W]
  have hz : K * |x⁻¹| < 1 := by linarith
  have hM : AbsSummable M x⁻¹ := absSummable_lawMomentSeries ν hK hs hz
  have hW : AbsSummable W x⁻¹ := (absSummable_X _).mul hM
  have hMbound : absSum M x⁻¹ ≤ 2 := by
    apply (absSum_lawMomentSeries_le ν hK hs hz).trans
    apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1-K*|x⁻¹|)).mpr
    linarith
  have hWbound : absSum W x⁻¹ ≤ 2 * |x⁻¹| := by
    calc
      _ ≤ absSum (X : PowerSeries ℝ) x⁻¹ * absSum M x⁻¹ :=
        absSum_mul_le (absSummable_X _) hM
      _ ≤ |x⁻¹| * 2 := by rw [absSum_X]; exact mul_le_mul_of_nonneg_left hMbound (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hscalemass (i : Fin k) : |(a i / k) * absSum W x⁻¹| ≤ 1/16 := by
    rw [abs_mul, abs_of_nonneg (absSum_nonneg W x⁻¹)]
    calc
      _ ≤ |a i / k| * (2 * |x⁻¹|) := mul_le_mul_of_nonneg_left hWbound (abs_nonneg _)
      _ = 2 * |(a i / k) * x⁻¹| := by rw [abs_mul]; ring
      _ ≤ _ := by linarith [hscale i]
  have hG : AbsSummable (freeSumCumulantSeries k t a) (absSum W x⁻¹) :=
    absSummable_freeSumCumulantSeries ht0 ht1 (fun i => by linarith [hscalemass i])
  have hWeval : PowerSeriesEvaluation.eval W x⁻¹ = realCauchyTransform ν x := by
    rw [show W = X * M from rfl, eval_mul (absSummable_X _) hM, eval_X]
    simpa only [M, PowerSeriesEvaluation.eval, coeff_lawMomentSeries] using
      (realCauchyTransform_eq_moment_tsum ν hK hs hx).symm
  have hscalew (i : Fin k) : |(a i / k) * realCauchyTransform ν x| ≤ 1/16 := by
    rw [← hWeval, abs_mul]
    apply (mul_le_mul_of_nonneg_left (abs_eval_le_absSum hW) (abs_nonneg (a i / k))).trans
    simpa only [abs_mul, abs_of_nonneg (absSum_nonneg W x⁻¹)] using hscalemass i
  have heq : realCauchyTransform ν x * bernoulliFreeSumR k t a (realCauchyTransform ν x) =
      PowerSeriesEvaluation.eval M x⁻¹ - 1 := by
    calc
      _ = PowerSeriesEvaluation.eval (freeSumCumulantSeries k t a) (realCauchyTransform ν x) :=
        (eval_freeSumCumulantSeries ht0 ht1 hscalew).symm
      _ = PowerSeriesEvaluation.eval (formalSubst W hW0 (freeSumCumulantSeries k t a)) x⁻¹ := by
        rw [eval_formalSubst hW0 hW hG, hWeval]
      _ = _ := by
        rw [show formalSubst W hW0 (freeSumCumulantSeries k t a) = M-1 from hformal,
          eval_sub hM (absSummable_one _), eval_one]
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; linarith
  have hxw : x * realCauchyTransform ν x = PowerSeriesEvaluation.eval M x⁻¹ := by
    rw [← hWeval, show W = X * M from rfl, eval_mul (absSummable_X _) hM, eval_X]
    simp [← mul_assoc, hx0]
  have hw0 : realCauchyTransform ν x ≠ 0 := by
    intro hw
    rw [hw, zero_mul] at heq
    rw [hw, mul_zero] at hxw
    linarith
  apply (mul_right_cancel₀ hw0)
  rw [add_mul, inv_mul_cancel₀ hw0]
  nlinarith

/-- A compactly supported probability law satisfying the formal cumulant
identity has both actual inverse-Cauchy germs required by the project. The
formal identity is the sole combinatorial input to this analytic bridge. -/
theorem isBernoulliFreeSumLaw_of_formal_identity
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {k : ℕ} {t K : ℝ} {a : Fin k → ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (hs : ∀ᵐ y ∂ν, |y| ≤ K)
    (hformal : formalSubst (X * lawMomentSeries ν) (by simp)
      (freeSumCumulantSeries k t a) = lawMomentSeries ν - 1) :
    IsBernoulliFreeSumLaw k t a ν := by
  let A : ℝ := ∑i, |a i / k|
  let B : ℝ := 2*K + 32*A + 1
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hAi (i : Fin k) : |a i / k| ≤ A :=
    Finset.single_le_sum (f := fun j : Fin k => |a j / (k : ℝ)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hB : 0 < B := by dsimp [B]; positivity
  have hremote (x : ℝ) (hx : B < |x|) :
      (realCauchyTransform ν x)⁻¹ +
        bernoulliFreeSumR k t a (realCauchyTransform ν x) = x := by
    have hxpos : 0 < |x| := hB.trans hx
    have hxK : K < |x| := by dsimp [B] at hx; linarith
    apply law_inverse_of_formal_identity_at ν ht0 ht1 hK hs hformal hxK
    · rw [abs_inv, ← div_eq_mul_inv]
      apply (div_le_iff₀ hxpos).mpr
      dsimp [B] at hx
      linarith
    · intro i
      rw [abs_mul, abs_inv, ← div_eq_mul_inv]
      apply (div_le_iff₀ hxpos).mpr
      have hi := hAi i
      dsimp [B] at hx
      linarith
  refine ⟨inferInstance, ⟨K, hs⟩, ?_, ?_⟩
  · filter_upwards [eventually_gt_atTop B] with x hx
    exact hremote x (hx.trans_le (le_abs_self x))
  · filter_upwards [eventually_lt_atBot (-B)] with x hx
    apply hremote x
    linarith [neg_le_abs x]

#print axioms law_inverse_of_formal_identity_at
#print axioms isBernoulliFreeSumLaw_of_formal_identity
end ProjectionChannels
