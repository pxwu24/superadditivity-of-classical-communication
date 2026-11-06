import RandomCompression.BernoulliEdgeCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Filter Finset Set
open scoped Topology BigOperators
namespace ProjectionChannels
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The endpoint budget reached by the increasing cost profile. -/
def bernoulliEndpointBudget (t : ℝ) (a : ι → ℝ) : ℝ :=
  ∑ i, bernoulliCost t (bernoulliEndpoint t (a i))

theorem bernoulliDual_zero (t : ℝ) : bernoulliDual t 0 = 0 := by
  unfold bernoulliDual bernoulliDelta
  have h : (0 + 2 * t - 1) ^ 2 + 4 * t * (1 - t) = 1 := by ring
  rw [h, Real.sqrt_one]
  ring

theorem bernoulliK_zero_coefficients (t k w : ℝ) :
    bernoulliK t k (fun _ : ι => 0) w = 1 / w := by
  simp [bernoulliK, bernoulliDual_zero]

theorem bernoulliProfile_zero_coefficients (t k w : ℝ) :
    bernoulliProfile t k (fun _ : ι => 0) w = 0 := by
  simp [bernoulliProfile, bernoulliMaximizer_zero, bernoulliCost_self]

theorem bernoulliProfile_lt_endpoint
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (ha : ∃ i, a i ≠ 0) (w : ℝ) (hw : 0 ≤ w) :
    bernoulliProfile t k a w < bernoulliEndpointBudget t a := by
  have hs : StrictMonoOn (bernoulliProfile t k a) (Set.Ici 0) :=
    strictMonoOn_bernoulliBudget ht0 ht1 (ne_of_gt hk) a ha
  have hw1 : 0 ≤ w + 1 := by linarith
  have hle : bernoulliProfile t k a (w + 1) ≤ bernoulliEndpointBudget t a := by
    apply ge_of_tendsto (tendsto_bernoulliProfile_atTop t k a ht0 ht1 hk)
    filter_upwards [eventually_ge_atTop (w + 1)] with v hv
    exact hs.monotoneOn hw1 (hw1.trans hv) hv
  exact (hs hw hw1 (by linarith)).trans_le hle

theorem bernoulliProfile_lt_budget_of_endpoint_le
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hend : bernoulliEndpointBudget t a ≤ 1 / k)
    (w : ℝ) (hw : 0 ≤ w) : bernoulliProfile t k a w < 1 / k := by
  by_cases ha : ∃ i, a i ≠ 0
  · exact (bernoulliProfile_lt_endpoint t k a ht0 ht1 hk ha w hw).trans_le hend
  · have haz : a = (fun _ => 0) := by
      funext i
      by_contra hi
      exact ha ⟨i, hi⟩
    rw [haz, bernoulliProfile_zero_coefficients]
    exact one_div_pos.mpr hk

theorem bernoulliK_has_critical_iff
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    (∃ w : ℝ, 0 < w ∧ deriv (bernoulliK t k a) w = 0) ↔
      1 / k < bernoulliEndpointBudget t a := by
  constructor
  · rintro ⟨w, hw, hd⟩
    have hsat := (bernoulliK_deriv_zero_iff t k a ht0 ht1 hk w hw).mp hd
    by_contra h
    have hlt := bernoulliProfile_lt_budget_of_endpoint_le t k a ht0 ht1 hk
      (le_of_not_gt h) w hw.le
    linarith
  · intro hend
    obtain ⟨w, hw, hsat⟩ := exists_positive_saturation
      (bernoulliProfile t k a) (1 / k) (bernoulliEndpointBudget t a)
      (continuous_bernoulliProfile t k a ht0 ht1) (bernoulliProfile_zero t k a)
      (one_div_pos.mpr hk) hend (tendsto_bernoulliProfile_atTop t k a ht0 ht1 hk)
    exact ⟨w, hw, (bernoulliK_deriv_zero_iff t k a ht0 ht1 hk w hw).mpr hsat⟩

theorem bernoulliK_deriv_neg_of_endpoint_le
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hend : bernoulliEndpointBudget t a ≤ 1 / k)
    (w : ℝ) (hw : 0 < w) : deriv (bernoulliK t k a) w < 0 := by
  rw [(hasDerivAt_bernoulliK t k a ht0 ht1 hk w hw).deriv]
  apply div_neg_of_neg_of_pos
  · have h := bernoulliProfile_lt_budget_of_endpoint_le t k a ht0 ht1 hk hend w hw.le
    have hh := (lt_div_iff₀ hk).mp h
    nlinarith
  · exact pow_pos hw _

theorem strictAntiOn_bernoulliK_of_endpoint_le
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hend : bernoulliEndpointBudget t a ≤ 1 / k) :
    StrictAntiOn (bernoulliK t k a) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro w hw
    exact (hasDerivAt_bernoulliK t k a ht0 ht1 hk w hw).continuousAt.continuousWithinAt
  · intro w hw
    apply bernoulliK_deriv_neg_of_endpoint_le t k a ht0 ht1 hk hend w
    simpa only [interior_Ioi, Set.mem_Ioi] using hw

theorem bernoulliK_minimum_is_critical
    (t k : ℝ) (a : ι → ℝ) (w : ℝ) (hw : 0 < w)
    (hmin : ∀ v : ℝ, 0 < v → bernoulliK t k a w ≤ bernoulliK t k a v) :
    deriv (bernoulliK t k a) w = 0 := by
  have hlocal : IsLocalMin (bernoulliK t k a) w := by
    filter_upwards [Ioi_mem_nhds hw] with v hv
    exact hmin v hv
  exact hlocal.deriv_eq_zero

theorem bernoulliK_unique_global_minimum
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hend : 1 / k < bernoulliEndpointBudget t a) :
    ∃! w : ℝ, 0 < w ∧ ∀ v : ℝ, 0 < v → bernoulliK t k a w ≤ bernoulliK t k a v := by
  obtain ⟨w, hw, hd⟩ := (bernoulliK_has_critical_iff t k a ht0 ht1 hk).mpr hend
  have ha : ∃ i, a i ≠ 0 := by
    by_contra hn
    have haz : a = (fun _ => 0) := by
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    have hsat := (bernoulliK_deriv_zero_iff t k a ht0 ht1 hk w hw).mp hd
    rw [haz, bernoulliProfile_zero_coefficients] at hsat
    have hpos := one_div_pos.mpr hk
    linarith
  refine ⟨w, ⟨hw, bernoulliK_critical_minimum t k a ht0 ht1 hk w hw hd⟩, ?_⟩
  intro v hv
  exact bernoulliK_critical_unique t k a ht0 ht1 hk ha hv.1 hw
    (bernoulliK_minimum_is_critical t k a v hv.1 hv.2) hd

theorem bernoulliK_endpoint_isGLB
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hend : bernoulliEndpointBudget t a ≤ 1 / k) :
    IsGLB (bernoulliKValues t k a) (∑ i, max (a i) 0) := by
  have hmax := bernoulli_endpoint_support t k a ht0.le ht1.le hend
  constructor
  · rintro _ ⟨w, hw, rfl⟩
    exact bernoulli_support_le_K t k w a _ ht0.le ht1.le hk hw hmax
  · intro z hz
    apply ge_of_tendsto (tendsto_bernoulliK_atTop t k a ht0 ht1 hk)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    exact hz ⟨w, hw, rfl⟩

theorem bernoulliK_infimum_at_infinity
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hend : bernoulliEndpointBudget t a ≤ 1 / k) :
    Tendsto (bernoulliK t k a) atTop (𝓝 (sInf (bernoulliKValues t k a))) ∧
      sInf (bernoulliKValues t k a) = ∑ i, max (a i) 0 ∧
      ∀ w : ℝ, 0 < w → sInf (bernoulliKValues t k a) < bernoulliK t k a w := by
  have hglb := bernoulliK_endpoint_isGLB t k a ht0 ht1 hk hend
  have hne : (bernoulliKValues t k a).Nonempty := ⟨bernoulliK t k a 1, ⟨1, by norm_num, rfl⟩⟩
  rw [hglb.csInf_eq hne]
  refine ⟨tendsto_bernoulliK_atTop t k a ht0 ht1 hk, rfl, ?_⟩
  intro w hw
  have hw1 : 0 < w + 1 := by linarith
  exact (hglb.1 ⟨w + 1, hw1, rfl⟩).trans_lt
    (strictAntiOn_bernoulliK_of_endpoint_le t k a ht0 ht1 hk hend hw hw1 (by linarith))


theorem bernoulliK_deriv_sign_around_critical
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (ha : ∃ i, a i ≠ 0) (w₀ : ℝ) (hw₀ : 0 < w₀)
    (hcrit : deriv (bernoulliK t k a) w₀ = 0) :
    (∀ w : ℝ, 0 < w → w < w₀ → deriv (bernoulliK t k a) w < 0) ∧
    (∀ w : ℝ, w₀ < w → 0 < deriv (bernoulliK t k a) w) := by
  have hsat := (bernoulliK_deriv_zero_iff t k a ht0 ht1 hk w₀ hw₀).mp hcrit
  have hs : StrictMonoOn (bernoulliProfile t k a) (Set.Ici 0) :=
    strictMonoOn_bernoulliBudget ht0 ht1 (ne_of_gt hk) a ha
  constructor
  · intro w hw hww
    rw [(hasDerivAt_bernoulliK t k a ht0 ht1 hk w hw).deriv]
    have hlt := hs hw.le hw₀.le hww
    rw [hsat] at hlt
    have hscaled := (lt_div_iff₀ hk).mp hlt
    exact div_neg_of_neg_of_pos (by nlinarith) (pow_pos hw _)
  · intro w hww
    have hw := hw₀.trans hww
    rw [(hasDerivAt_bernoulliK t k a ht0 ht1 hk w hw).deriv]
    have hlt := hs hw₀.le hw.le hww
    rw [hsat] at hlt
    have hscaled := (div_lt_iff₀ hk).mp hlt
    exact div_pos (by nlinarith) (pow_pos hw _)

end
end ProjectionChannels

