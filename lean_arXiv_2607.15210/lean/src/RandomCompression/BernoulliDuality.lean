import Preliminaries.PreliminariesAnalysis
import RandomCompression.BernoulliCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp

/-!
# Full finite-dimensional Bernoulli convex duality

This file proves equality of the support function and the infimum over
positive parameters, treating both finite saturation and endpoint regimes.
-/

open Filter Finset Set
open scoped Topology BigOperators

namespace ProjectionChannels

noncomputable section

def bernoulliProfile {ι : Type*} [Fintype ι] (t k : ℝ) (a : ι → ℝ) (w : ℝ) : ℝ :=
  ∑ i, bernoulliCost t (bernoulliMaximizer t (a i * w / k))

def bernoulliK {ι : Type*} [Fintype ι] (t k : ℝ) (a : ι → ℝ) (w : ℝ) : ℝ :=
  (1 + k * ∑ i, bernoulliDual t (a i * w / k)) / w

def bernoulliObjectiveValues {ι : Type*} [Fintype ι] (t k : ℝ) (a : ι → ℝ) : Set ℝ :=
  (fun u : ι → ℝ => ∑ i, a i * u i) '' bernoulliFeasible t k

def bernoulliKValues {ι : Type*} [Fintype ι] (t k : ℝ) (a : ι → ℝ) : Set ℝ :=
  bernoulliK t k a '' Set.Ioi 0

theorem continuous_bernoulliCost (t : ℝ) : Continuous (bernoulliCost t) := by
  unfold bernoulliCost
  fun_prop

theorem continuous_bernoulliProfile {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Continuous (bernoulliProfile t k a) := by
  unfold bernoulliProfile
  refine continuous_finset_sum Finset.univ fun i _ => ?_
  exact (continuous_bernoulliCost t).comp
    ((continuous_bernoulliMaximizer ht0 ht1).comp (by fun_prop))

theorem bernoulliProfile_zero {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) : bernoulliProfile t k a 0 = 0 := by
  simp [bernoulliProfile, bernoulliMaximizer_zero, bernoulliCost_self]

theorem bernoulli_endpoint_objective (t a : ℝ) :
    a * bernoulliEndpoint t a = max a 0 := by
  by_cases hp : 0 < a
  · simp [bernoulliEndpoint, hp, max_eq_left hp.le]
  · by_cases hn : a < 0
    · simp [bernoulliEndpoint, hp, hn, max_eq_right hn.le]
    · have hz : a = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      simp [hz]

theorem tendsto_bernoulliMaximizer_scaled
    (t k a : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    Tendsto (fun w : ℝ => bernoulliMaximizer t (a * w / k)) atTop
      (𝓝 (bernoulliEndpoint t a)) := by
  by_cases hp : 0 < a
  · rw [bernoulliEndpoint, if_pos hp]
    apply (tendsto_bernoulliMaximizer_atTop ht0 ht1).comp
    simpa only [div_mul_eq_mul_div] using
      (tendsto_const_mul_atTop_of_pos (div_pos hp hk)).2
        (tendsto_id : Tendsto (fun w : ℝ => w) atTop atTop)
  · by_cases hn : a < 0
    · rw [bernoulliEndpoint, if_neg hp, if_pos hn]
      apply (tendsto_bernoulliMaximizer_atBot ht0 ht1).comp
      simpa only [div_mul_eq_mul_div] using
        (tendsto_const_mul_atBot_of_neg (div_neg_of_neg_of_pos hn hk)).2
          (tendsto_id : Tendsto (fun w : ℝ => w) atTop atTop)
    · have hz : a = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      simp [hz, bernoulliEndpoint, bernoulliMaximizer_zero]

theorem tendsto_bernoulliProfile_atTop {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    Tendsto (bernoulliProfile t k a) atTop
      (𝓝 (∑ i, bernoulliCost t (bernoulliEndpoint t (a i)))) := by
  unfold bernoulliProfile
  refine tendsto_finset_sum Finset.univ fun i _ => ?_
  exact ((continuous_bernoulliCost t).tendsto _).comp
    (tendsto_bernoulliMaximizer_scaled t k (a i) ht0 ht1 hk)

theorem tendsto_bernoulli_objective_atTop {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    Tendsto (fun w : ℝ => ∑ i, a i * bernoulliMaximizer t (a i * w / k))
      atTop (𝓝 (∑ i, max (a i) 0)) := by
  refine tendsto_finset_sum Finset.univ fun i _ => ?_
  rw [← bernoulli_endpoint_objective t (a i)]
  exact (tendsto_bernoulliMaximizer_scaled t k (a i) ht0 ht1 hk).const_mul (a i)

theorem bernoulliK_profile_identity {ι : Type*} [Fintype ι]
    (t k w : ℝ) (a : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) (hw : 0 < w) :
    bernoulliK t k a w =
      (∑ i, a i * bernoulliMaximizer t (a i * w / k)) +
      (1 - k * bernoulliProfile t k a w) / w := by
  have hsum : (∑ i, ((a i * w / k) * bernoulliMaximizer t (a i * w / k) -
      bernoulliCost t (bernoulliMaximizer t (a i * w / k)))) =
      ∑ i, bernoulliDual t (a i * w / k) := by
    apply Finset.sum_congr rfl
    intro i _
    exact bernoulli_legendre_equality ht0 ht1 (a i * w / k)
  have hfactor : (∑ i, (a i * w / k) * bernoulliMaximizer t (a i * w / k)) =
      (w / k) * ∑ i, a i * bernoulliMaximizer t (a i * w / k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_sub_distrib, hfactor] at hsum
  unfold bernoulliK bernoulliProfile
  rw [← hsum]
  field_simp [ne_of_gt hk, ne_of_gt hw]
  ring

theorem tendsto_bernoulliK_atTop {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    Tendsto (bernoulliK t k a) atTop (𝓝 (∑ i, max (a i) 0)) := by
  have hnum : Tendsto (fun w : ℝ => 1 - k * bernoulliProfile t k a w) atTop
      (𝓝 (1 - k * ∑ i, bernoulliCost t (bernoulliEndpoint t (a i)))) :=
    tendsto_const_nhds.sub ((tendsto_bernoulliProfile_atTop t k a ht0 ht1 hk).const_mul k)
  have hrem : Tendsto (fun w : ℝ => (1 - k * bernoulliProfile t k a w) / w)
      atTop (𝓝 0) := hnum.div_atTop tendsto_id
  have hsum := (tendsto_bernoulli_objective_atTop t k a ht0 ht1 hk).add hrem
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  exact (bernoulliK_profile_identity t k w a ht0 ht1 hk hw).symm

/-- A continuous profile starting below the budget and tending to a value
above it necessarily saturates at a strictly positive finite parameter. -/
theorem exists_positive_saturation
    (F : ℝ → ℝ) (B L : ℝ) (hF : Continuous F)
    (hzero : F 0 = 0) (hB : 0 < B) (hBL : B < L)
    (hlimit : Tendsto F atTop (𝓝 L)) :
    ∃ w : ℝ, 0 < w ∧ F w = B := by
  have hevent : ∀ᶠ w : ℝ in atTop, B < F w :=
    hlimit.eventually (lt_mem_nhds hBL)
  obtain ⟨w, hwpos, hwval⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and hevent).exists
  have hbetween : B ∈ Set.Icc (F 0) (F w) := by
    rw [hzero]
    exact ⟨hB.le, hwval.le⟩
  obtain ⟨v, hv, hval⟩ :=
    intermediate_value_Icc hwpos.le hF.continuousOn hbetween
  refine ⟨v, ?_, hval⟩
  have hvne : v ≠ 0 := by
    intro h
    rw [h, hzero] at hval
    linarith
  exact lt_of_le_of_ne hv.1 (Ne.symm hvne)

/-- A support maximizer is a lower bound for every dual value. -/
theorem bernoulli_support_le_K
    {ι : Type*} [Fintype ι] (t k w : ℝ) (a : ι → ℝ) (M : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hk : 0 < k) (hw : 0 < w)
    (hmax : IsGreatest (bernoulliObjectiveValues t k a) M) :
    M ≤ bernoulliK t k a w := by
  obtain ⟨u, hu, rfl⟩ := hmax.1
  exact bernoulli_support_upper_bound t k w a u ht0 ht1 hk hw
    hu.1 hu.2.1 hu.2.2

/-- Complete duality follows from the actual continuity and endpoint
limits of the explicitly specified Bernoulli profile and dual function. -/
theorem bernoulli_duality_from_continuity_and_limits
    {ι : Type*} [Fintype ι] (t k : ℝ) (a : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hcont : Continuous (bernoulliProfile t k a))
    (hzero : bernoulliProfile t k a 0 = 0)
    (hprofile : Tendsto (bernoulliProfile t k a) atTop
      (𝓝 (∑ i, bernoulliCost t (bernoulliEndpoint t (a i)))))
    (hK : Tendsto (bernoulliK t k a) atTop (𝓝 (∑ i, max (a i) 0))) :
    ∃ M : ℝ, IsGreatest (bernoulliObjectiveValues t k a) M ∧
      IsGLB (bernoulliKValues t k a) M := by
  by_cases hend : (∑ i, bernoulliCost t (bernoulliEndpoint t (a i))) ≤ 1 / k
  · have hmax := bernoulli_endpoint_support t k a ht0.le ht1.le hend
    refine ⟨∑ i, max (a i) 0, hmax, ?_⟩
    constructor
    · rintro _ ⟨w, hw, rfl⟩
      exact bernoulli_support_le_K t k w a _ ht0.le ht1.le hk hw hmax
    · intro z hz
      apply ge_of_tendsto hK
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
      exact hz ⟨w, hw, rfl⟩
  · obtain ⟨w, hw, hsat⟩ := exists_positive_saturation
      (bernoulliProfile t k a) (1 / k)
      (∑ i, bernoulliCost t (bernoulliEndpoint t (a i))) hcont hzero
      (one_div_pos.mpr hk) (lt_of_not_ge hend) hprofile
    have hmax := bernoulli_support_attainment t k w a ht0 ht1 hk hw hsat
    refine ⟨bernoulliK t k a w, hmax, ?_⟩
    apply IsLeast.isGLB
    constructor
    · exact ⟨w, hw, rfl⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact bernoulli_support_le_K t k v a _ ht0.le ht1.le hk hv hmax

/-- Full deterministic duality, with all analytic hypotheses discharged.
The coefficients can have arbitrary signs. The positive real parameter k
need not equal the number of coordinates. -/
theorem bernoulli_full_duality
    {ι : Type*} [Fintype ι] (t k : ℝ) (a : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    ∃ M : ℝ, IsGreatest (bernoulliObjectiveValues t k a) M ∧
      IsGLB (bernoulliKValues t k a) M := by
  exact bernoulli_duality_from_continuity_and_limits t k a ht0 ht1 hk
    (continuous_bernoulliProfile t k a ht0 ht1)
    (bernoulliProfile_zero t k a)
    (tendsto_bernoulliProfile_atTop t k a ht0 ht1 hk)
    (tendsto_bernoulliK_atTop t k a ht0 ht1 hk)

/-- The maximum over the feasible region equals the infimum over w > 0. -/
theorem bernoulli_support_eq_inf
    {ι : Type*} [Fintype ι] (t k : ℝ) (a : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    sSup (bernoulliObjectiveValues t k a) = sInf (bernoulliKValues t k a) := by
  obtain ⟨M, hmax, hglb⟩ := bernoulli_full_duality t k a ht0 ht1 hk
  have hne : (bernoulliKValues t k a).Nonempty :=
    ⟨bernoulliK t k a 1, ⟨1, by norm_num, rfl⟩⟩
  rw [hmax.csSup_eq, hglb.csInf_eq hne]

/-- The infimum dual value is actually attained by a feasible vector. -/
theorem bernoulli_support_attains_inf
    {ι : Type*} [Fintype ι] (t k : ℝ) (a : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    IsGreatest (bernoulliObjectiveValues t k a) (sInf (bernoulliKValues t k a)) := by
  obtain ⟨M, hmax, hglb⟩ := bernoulli_full_duality t k a ht0 ht1 hk
  have hne : (bernoulliKValues t k a).Nonempty :=
    ⟨bernoulliK t k a 1, ⟨1, by norm_num, rfl⟩⟩
  rw [hglb.csInf_eq hne]
  exact hmax

/-- The paper's k-coordinate case, for every integer k ≥ 1. -/
theorem bernoulli_support_eq_inf_nat
    (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (hk : 1 ≤ k) (ht0 : 0 < t) (ht1 : t < 1) :
    sSup (bernoulliObjectiveValues t (k : ℝ) a) =
      sInf (bernoulliKValues t (k : ℝ) a) := by
  exact bernoulli_support_eq_inf t (k : ℝ) a ht0 ht1
    (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hk))

end
end ProjectionChannels

