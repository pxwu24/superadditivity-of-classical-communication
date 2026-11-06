import Preliminaries.PreliminariesLegendre
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Finset
open scoped Topology BigOperators

namespace ProjectionChannels
noncomputable section

private theorem deltaRadicand_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    0 < (y + 2 * t - 1) ^ 2 + 4 * t * (1 - t) := by
  have h : 0 < 1 - t := sub_pos.mpr ht1
  positivity

theorem hasDerivAt_bernoulliDelta {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    HasDerivAt (bernoulliDelta t) ((y + 2 * t - 1) / bernoulliDelta t y) y := by
  have hlin := ((hasDerivAt_id' y).add_const (2 * t)).sub_const 1
  have h := ((hlin.pow 2).add_const (4 * t * (1 - t))).sqrt
    (ne_of_gt (deltaRadicand_pos ht0 ht1 y))
  convert h using 1 <;> simp only [bernoulliDelta, pow_one, mul_one]
  ring

theorem hasDerivAt_bernoulliDual {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    HasDerivAt (bernoulliDual t) (bernoulliMaximizer t y) y := by
  convert (((hasDerivAt_id' y).sub_const 1).add
    (hasDerivAt_bernoulliDelta ht0 ht1 y)).div_const 2 using 1

theorem hasDerivAt_bernoulliMaximizer {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    HasDerivAt (bernoulliMaximizer t)
      (2 * t * (1 - t) / bernoulliDelta t y ^ 3) y := by
  have hD := bernoulliDelta_pos ht0 ht1 y
  have hDs := bernoulliDelta_sq ht0.le ht1.le y
  have hlin := ((hasDerivAt_id' y).add_const (2 * t)).sub_const 1
  have h := ((hlin.div (hasDerivAt_bernoulliDelta ht0 ht1 y) (ne_of_gt hD)).const_add 1).div_const 2
  convert h using 1
  dsimp
  have hid : (1 * bernoulliDelta t y - (y + 2 * t - 1) *
      ((y + 2 * t - 1) / bernoulliDelta t y)) / bernoulliDelta t y ^ 2 / 2 =
      (bernoulliDelta t y ^ 2 - (y + 2 * t - 1) ^ 2) /
        (2 * bernoulliDelta t y ^ 3) := by
    field_simp only [ne_of_gt hD]
    ring
  rw [hid]
  have hnum : bernoulliDelta t y ^ 2 - (y + 2 * t - 1) ^ 2 =
      4 * t * (1 - t) := by linarith
  rw [hnum]
  ring

theorem continuous_bernoulliMaximizer {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Continuous (bernoulliMaximizer t) :=
  continuous_iff_continuousAt.mpr (fun y =>
    (hasDerivAt_bernoulliMaximizer ht0 ht1 y).continuousAt)

theorem bernoulliMaximizer_zero (t : ℝ) : bernoulliMaximizer t 0 = t := by
  have hD : bernoulliDelta t 0 = 1 := by
    unfold bernoulliDelta
    have h : (0 + 2 * t - 1) ^ 2 + 4 * t * (1 - t) = 1 := by ring
    rw [h, Real.sqrt_one]
  unfold bernoulliMaximizer
  rw [hD]
  ring

theorem hasDerivAt_bernoulliCost_maximizer {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    HasDerivAt (fun y => bernoulliCost t (bernoulliMaximizer t y))
      (y * (2 * t * (1 - t) / bernoulliDelta t y ^ 3)) y := by
  have heq : (fun y => bernoulliCost t (bernoulliMaximizer t y)) =
      (fun y => y * bernoulliMaximizer t y - bernoulliDual t y) := by
    funext y
    linarith [bernoulli_legendre_equality ht0 ht1 y]
  rw [heq]
  convert ((hasDerivAt_id' y).mul (hasDerivAt_bernoulliMaximizer ht0 ht1 y)).sub
    (hasDerivAt_bernoulliDual ht0 ht1 y) using 1 <;> ring


theorem bernoulliCost_zero {t : ℝ} (ht0 : 0 ≤ t) : bernoulliCost t 0 = t := by
  simp [bernoulliCost, Real.sq_sqrt ht0]

theorem bernoulliCost_one {t : ℝ} (ht1 : t ≤ 1) : bernoulliCost t 1 = 1 - t := by
  simp [bernoulliCost, Real.sq_sqrt (sub_nonneg.mpr ht1)]

theorem bernoulliMaximizer_lower {t y : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hy : 0 < y) :
    1 - 1 / y ≤ bernoulliMaximizer t y := by
  have h := bernoulli_legendre_inequality ht0.le ht1.le (by norm_num : (0:ℝ) ≤ 1)
    (by norm_num : (1:ℝ) ≤ 1) y
  rw [bernoulliCost_one ht1.le] at h
  have heq := bernoulli_legendre_equality ht0 ht1 y
  have hc := bernoulliCost_nonneg t (bernoulliMaximizer t y)
  have hdiv : 1 - bernoulliMaximizer t y ≤ 1 / y := by
    apply (le_div_iff₀ hy).2
    nlinarith
  linarith

theorem bernoulliMaximizer_upper {t y : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hy : y < 0) :
    bernoulliMaximizer t y ≤ 1 / (-y) := by
  have h := bernoulli_legendre_inequality ht0.le ht1.le (by norm_num : (0:ℝ) ≤ 0)
    (by norm_num : (0:ℝ) ≤ 1) y
  rw [bernoulliCost_zero ht0.le] at h
  have heq := bernoulli_legendre_equality ht0 ht1 y
  have hc := bernoulliCost_nonneg t (bernoulliMaximizer t y)
  apply (le_div_iff₀ (neg_pos.mpr hy)).2
  nlinarith

theorem tendsto_bernoulliMaximizer_atTop {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (bernoulliMaximizer t) atTop (𝓝 1) := by
  have hi : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
  have hlo : Tendsto (fun y : ℝ => 1 - 1 / y) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact bernoulliMaximizer_lower ht0 ht1 hy
  · exact Filter.Eventually.of_forall (fun y => (bernoulliMaximizer_mem_Ioo ht0 ht1 y).2.le)

theorem tendsto_bernoulliMaximizer_atBot {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (bernoulliMaximizer t) atBot (𝓝 0) := by
  have hi : Tendsto (fun y : ℝ => 1 / (-y)) atBot (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).comp
        (tendsto_neg_atBot_atTop : Tendsto (fun y : ℝ => -y) atBot atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
  · exact Filter.Eventually.of_forall (fun y => (bernoulliMaximizer_mem_Ioo ht0 ht1 y).1.le)
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with y hy
    exact bernoulliMaximizer_upper ht0 ht1 hy


theorem hasDerivAt_bernoulliCost {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (bernoulliCost t)
      (1 - 2 * t - Real.sqrt (t * (1 - t)) * (1 - 2 * u) /
        Real.sqrt (u * (1 - u))) u := by
  have hp : 0 < u * (1 - u) := mul_pos hu0 (sub_pos.mpr hu1)
  have hid := hasDerivAt_id' u
  have hroot := (hid.mul (hid.const_sub 1)).sqrt (ne_of_gt hp)
  have h := ((hid.const_mul (1 - 2 * t)).const_add t).sub
    (hroot.const_mul (2 * Real.sqrt (t * (1 - t))))
  have heq : bernoulliCost t =ᶠ[𝓝 u]
      (fun u => t + (1 - 2 * t) * u -
        2 * Real.sqrt (t * (1 - t)) * Real.sqrt (u * (1 - u))) := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv
    exact bernoulliCost_expansion ht0 ht1 hv.1.le hv.2.le
  convert h.congr_of_eventuallyEq heq using 1 <;> ring

theorem hasDerivAt_bernoulliCost_at_maximizer {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    HasDerivAt (bernoulliCost t) y (bernoulliMaximizer t y) := by
  have hu := bernoulliMaximizer_mem_Ioo ht0 ht1 y
  have hD := bernoulliDelta_pos ht0 ht1 y
  have hb : 0 < Real.sqrt (t * (1 - t)) :=
    Real.sqrt_pos.mpr (mul_pos ht0 (sub_pos.mpr ht1))
  convert hasDerivAt_bernoulliCost ht0.le ht1.le hu.1 hu.2 using 1
  rw [bernoulliMaximizer_product ht0 ht1 y,
    Real.sqrt_sq (div_nonneg hb.le hD.le)]
  unfold bernoulliMaximizer
  field_simp only [ne_of_gt hD, ne_of_gt hb]
  ring

theorem bernoulli_secondDerivative_pos {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    0 < 2 * t * (1 - t) / bernoulliDelta t y ^ 3 := by
  have ht : 0 < 1 - t := sub_pos.mpr ht1
  have hD := bernoulliDelta_pos ht0 ht1 y
  positivity

theorem strictMono_bernoulliMaximizer {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : StrictMono (bernoulliMaximizer t) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_bernoulliMaximizer ht0 ht1)
    (bernoulli_secondDerivative_pos ht0 ht1)

theorem hasDerivAt_bernoulliBudget {ι : Type*} [Fintype ι]
    {t k : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : ι → ℝ) (w : ℝ) :
    HasDerivAt (fun w => ∑ i, bernoulliCost t (bernoulliMaximizer t (a i * w / k)))
      (∑ i, (a i ^ 2 * w / k ^ 2) *
        (2 * t * (1 - t) / bernoulliDelta t (a i * w / k) ^ 3)) w := by
  apply HasDerivAt.sum
  intro i _
  convert (hasDerivAt_bernoulliCost_maximizer ht0 ht1 (a i * w / k)).comp w
    (((hasDerivAt_id' w).const_mul (a i)).div_const k) using 1 <;> ring

theorem continuous_bernoulliBudget {ι : Type*} [Fintype ι]
    {t k : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : ι → ℝ) :
    Continuous (fun w => ∑ i, bernoulliCost t (bernoulliMaximizer t (a i * w / k))) :=
  continuous_iff_continuousAt.mpr (fun w =>
    (hasDerivAt_bernoulliBudget (k:=k) ht0 ht1 a w).continuousAt)

theorem monotoneOn_bernoulliBudget {ι : Type*} [Fintype ι]
    {t k : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : ι → ℝ) :
    MonotoneOn (fun w => ∑ i, bernoulliCost t (bernoulliMaximizer t (a i * w / k)))
      (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (continuous_bernoulliBudget ht0 ht1 a).continuousOn
  · intro w _
    exact (hasDerivAt_bernoulliBudget ht0 ht1 a w).differentiableAt.differentiableWithinAt
  · intro w hw
    have hwpos : 0 < w := by simpa only [interior_Ici, Set.mem_Ioi] using hw
    have hw' : 0 ≤ w := hwpos.le
    rw [(hasDerivAt_bernoulliBudget ht0 ht1 a w).deriv]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hw') (sq_nonneg _))
      (bernoulli_secondDerivative_pos ht0 ht1 _).le

theorem strictMonoOn_bernoulliBudget {ι : Type*} [Fintype ι]
    {t k : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hk : k ≠ 0)
    (a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    StrictMonoOn (fun w => ∑ i, bernoulliCost t (bernoulliMaximizer t (a i * w / k)))
      (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    (continuous_bernoulliBudget ht0 ht1 a).continuousOn
  intro w hw
  have hw' : 0 < w := by simpa only [interior_Ici, Set.mem_Ioi] using hw
  rw [(hasDerivAt_bernoulliBudget ht0 ht1 a w).deriv]
  obtain ⟨j, hj⟩ := ha
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hw'.le) (sq_nonneg _))
      (bernoulli_secondDerivative_pos ht0 ht1 _).le
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    exact mul_pos (div_pos (mul_pos (sq_pos_of_ne_zero hj) hw') (sq_pos_of_ne_zero hk))
      (bernoulli_secondDerivative_pos ht0 ht1 _)

theorem bernoulliBudget_zero {ι : Type*} [Fintype ι] (t k : ℝ) (a : ι → ℝ) :
    (∑ i, bernoulliCost t (bernoulliMaximizer t (a i * 0 / k))) = 0 := by
  simp [bernoulliMaximizer_zero, bernoulliCost_self]

theorem tendsto_bernoulliBudget_zero {ι : Type*} [Fintype ι]
    {t k : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : ι → ℝ) :
    Tendsto (fun w => ∑ i, bernoulliCost t (bernoulliMaximizer t (a i * w / k)))
      (𝓝 0) (𝓝 0) := by
  simpa only [mul_zero, zero_div, bernoulliMaximizer_zero, bernoulliCost_self, Finset.sum_const_zero]
    using (continuous_bernoulliBudget (k:=k) ht0 ht1 a).tendsto (0 : ℝ)


def bernoulliCostSlope (t u : ℝ) : ℝ :=
  1 - 2 * t - Real.sqrt (t * (1 - t)) * (1 - 2 * u) / Real.sqrt (u * (1 - u))

theorem hasDerivAt_bernoulliCostSlope {t u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (bernoulliCostSlope t)
      (Real.sqrt (t * (1 - t)) / (2 * Real.sqrt (u * (1 - u)) ^ 3)) u := by
  have hp : 0 < u * (1 - u) := mul_pos hu0 (sub_pos.mpr hu1)
  have hq : 0 < Real.sqrt (u * (1 - u)) := Real.sqrt_pos.mpr hp
  have hqs := Real.sq_sqrt hp.le
  have hid := hasDerivAt_id' u
  have hroot := (hid.mul (hid.const_sub 1)).sqrt (ne_of_gt hp)
  have h := (((hid.const_mul 2).const_sub 1).const_mul
    (Real.sqrt (t * (1 - t)))).div hroot (ne_of_gt hq)
  have h := h.const_sub (1 - 2 * t)
  convert h using 1
  dsimp
  have halg :
      -(Real.sqrt (t * (1 - t)) * (-(2 * 1)) * Real.sqrt (u * (1 - u)) -
        Real.sqrt (t * (1 - t)) * (1 - 2 * u) *
          ((1 * (1 - u) + u * -1) / (2 * Real.sqrt (u * (1 - u))))) /
        Real.sqrt (u * (1 - u)) ^ 2 =
      Real.sqrt (t * (1 - t)) *
        (4 * Real.sqrt (u * (1 - u)) ^ 2 + (1 - 2 * u) ^ 2) /
        (2 * Real.sqrt (u * (1 - u)) ^ 3) := by
    field_simp only [ne_of_gt hq]
    ring
  rw [← neg_div, halg]
  have hnum : 4 * Real.sqrt (u * (1 - u)) ^ 2 + (1 - 2 * u) ^ 2 = 1 := by
    nlinarith
  rw [hnum]
  ring

theorem hasDerivAt_deriv_bernoulliCost {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (deriv (bernoulliCost t))
      (Real.sqrt (t * (1 - t)) / (2 * Real.sqrt (u * (1 - u)) ^ 3)) u := by
  apply (hasDerivAt_bernoulliCostSlope (t:=t) hu0 hu1).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv
  exact (hasDerivAt_bernoulliCost ht0 ht1 hv.1 hv.2).deriv

theorem strictMonoOn_deriv_bernoulliCost {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    StrictMonoOn (deriv (bernoulliCost t)) (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro u hu
    exact (hasDerivAt_deriv_bernoulliCost ht0.le ht1.le hu.1 hu.2).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Set.Ioo (0:ℝ) 1 := by simpa only [interior_Ioo] using hu
    rw [(hasDerivAt_deriv_bernoulliCost ht0.le ht1.le hu'.1 hu'.2).deriv]
    exact div_pos (Real.sqrt_pos.mpr (mul_pos ht0 (sub_pos.mpr ht1)))
      (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr (mul_pos hu'.1 (sub_pos.mpr hu'.2))) _))

theorem tendsto_deriv_bernoulliCost_zero {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (deriv (bernoulliCost t)) (𝓝[>] 0) atBot := by
  apply tendsto_atBot.2
  intro M
  have hu := bernoulliMaximizer_mem_Ioo ht0 ht1 M
  have hsmall : ∀ᶠ u : ℝ in 𝓝[>] (0:ℝ), u < bernoulliMaximizer t M :=
    nhdsWithin_le_nhds (eventually_lt_nhds hu.1)
  filter_upwards [self_mem_nhdsWithin, hsmall] with u hu0 husmall
  have hint : u ∈ Set.Ioo (0:ℝ) 1 := ⟨hu0, husmall.trans hu.2⟩
  have h := strictMonoOn_deriv_bernoulliCost ht0 ht1 hint hu husmall
  rw [(hasDerivAt_bernoulliCost_at_maximizer ht0 ht1 M).deriv] at h
  exact h.le

theorem tendsto_deriv_bernoulliCost_one {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (deriv (bernoulliCost t)) (𝓝[<] 1) atTop := by
  apply tendsto_atTop.2
  intro M
  have hu := bernoulliMaximizer_mem_Ioo ht0 ht1 M
  have hlarge : ∀ᶠ u : ℝ in 𝓝[<] (1:ℝ), bernoulliMaximizer t M < u :=
    nhdsWithin_le_nhds (eventually_gt_nhds hu.2)
  filter_upwards [self_mem_nhdsWithin, hlarge] with u hu1 hubig
  have hint : u ∈ Set.Ioo (0:ℝ) 1 := ⟨hu.1.trans hubig, hu1⟩
  have h := strictMonoOn_deriv_bernoulliCost ht0 ht1 hu hint hubig
  rw [(hasDerivAt_bernoulliCost_at_maximizer ht0 ht1 M).deriv] at h
  exact h.le


theorem hasDerivAt_deriv_bernoulliCost_rpow {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (deriv (bernoulliCost t))
      (Real.sqrt (t * (1 - t)) / (2 * (u * (1 - u)) ^ ((3:ℝ)/2))) u := by
  have hs : Real.sqrt (u * (1 - u)) ^ (3:ℕ) = (u * (1 - u)) ^ ((3:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (mul_nonneg hu0.le (sub_pos.mpr hu1).le)]
    norm_num
  simpa only [hs] using hasDerivAt_deriv_bernoulliCost ht0 ht1 hu0 hu1

theorem strictConvexOn_bernoulliCost {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    StrictConvexOn ℝ (Set.Icc 0 1) (bernoulliCost t) := by
  have hc : Continuous (bernoulliCost t) :=
    ((Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.sub continuous_id))).sub
      (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))).pow 2
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1) hc.continuousOn
  simpa only [interior_Icc] using strictMonoOn_deriv_bernoulliCost ht0 ht1

theorem deriv_bernoulliDual {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    deriv (bernoulliDual t) = bernoulliMaximizer t := by
  funext y
  exact (hasDerivAt_bernoulliDual ht0 ht1 y).deriv

theorem hasDerivAt_deriv_bernoulliDual {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    HasDerivAt (deriv (bernoulliDual t))
      (2 * t * (1 - t) / bernoulliDelta t y ^ 3) y := by
  rw [deriv_bernoulliDual ht0 ht1]
  exact hasDerivAt_bernoulliMaximizer ht0 ht1 y

end
end ProjectionChannels

