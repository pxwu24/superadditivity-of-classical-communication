import RandomCompression.BernoulliDuality

open Filter Finset Set
open scoped Topology BigOperators
namespace ProjectionChannels
noncomputable section

theorem hasDerivAt_bernoulliK {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (_hk : 0 < k)
    (w : ℝ) (hw : 0 < w) :
    HasDerivAt (bernoulliK t k a)
      ((k * bernoulliProfile t k a w - 1) / w ^ 2) w := by
  have hterms : HasDerivAt (fun v => ∑ i, bernoulliDual t (a i * v / k))
      (∑ i, bernoulliMaximizer t (a i * w / k) * (a i / k)) w := by
    apply HasDerivAt.sum
    intro i _
    simpa only [mul_one, Function.comp_def] using
      (hasDerivAt_bernoulliDual ht0 ht1 (a i * w / k)).comp w
        (((hasDerivAt_id' w).const_mul (a i)).div_const k)
  have hnum := (hterms.const_mul k).const_add 1
  have hder := hnum.div (hasDerivAt_id' w) (ne_of_gt hw)
  have hsum : (∑ i, ((a i * w / k) * bernoulliMaximizer t (a i * w / k) -
      bernoulliCost t (bernoulliMaximizer t (a i * w / k)))) =
      ∑ i, bernoulliDual t (a i * w / k) := by
    apply Finset.sum_congr rfl
    intro i _
    exact bernoulli_legendre_equality ht0 ht1 (a i * w / k)
  have hfactor : (∑ i, (a i * w / k) * bernoulliMaximizer t (a i * w / k)) =
      w * (∑ i, bernoulliMaximizer t (a i * w / k) * (a i / k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_sub_distrib, hfactor] at hsum
  convert hder using 1
  unfold bernoulliProfile
  rw [← hsum]
  ring

theorem bernoulliK_deriv_zero_iff {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (w : ℝ) (hw : 0 < w) :
    deriv (bernoulliK t k a) w = 0 ↔ bernoulliProfile t k a w = 1 / k := by
  rw [(hasDerivAt_bernoulliK t k a ht0 ht1 hk w hw).deriv]
  rw [div_eq_zero_iff]
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hw)
  simp only [hw2, or_false]
  constructor
  · intro h
    apply (eq_div_iff (ne_of_gt hk)).2
    nlinarith
  · intro h
    rw [h]
    field_simp

/-- There is at most one positive critical point when a is nonzero. -/
theorem bernoulliK_critical_unique {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (ha : ∃ i, a i ≠ 0) {v w : ℝ} (hv : 0 < v) (hw : 0 < w)
    (hdv : deriv (bernoulliK t k a) v = 0)
    (hdw : deriv (bernoulliK t k a) w = 0) : v = w := by
  have hvbudget := (bernoulliK_deriv_zero_iff t k a ht0 ht1 hk v hv).mp hdv
  have hwbudget := (bernoulliK_deriv_zero_iff t k a ht0 ht1 hk w hw).mp hdw
  have hstrict := strictMonoOn_bernoulliBudget ht0 ht1 (ne_of_gt hk) a ha
  apply hstrict.injOn hv.le hw.le
  exact hvbudget.trans hwbudget.symm

/-- A positive critical point is a global minimizer on w > 0. -/
theorem bernoulliK_critical_minimum {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (w : ℝ) (hw : 0 < w) (hdw : deriv (bernoulliK t k a) w = 0) :
    ∀ v : ℝ, 0 < v → bernoulliK t k a w ≤ bernoulliK t k a v := by
  have hsat := (bernoulliK_deriv_zero_iff t k a ht0 ht1 hk w hw).mp hdw
  have hmax := bernoulli_support_attainment t k w a ht0 ht1 hk hw hsat
  intro v hv
  exact bernoulli_support_le_K t k v a _ ht0.le ht1.le hk hv hmax

/-- In the absence of a positive critical point, the derivative is strictly
negative everywhere on the positive half-line. -/
theorem bernoulliK_deriv_neg_of_no_critical {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hnocrit : ∀ w : ℝ, 0 < w → deriv (bernoulliK t k a) w ≠ 0)
    (w : ℝ) (hw : 0 < w) : deriv (bernoulliK t k a) w < 0 := by
  have hF : bernoulliProfile t k a w < 1 / k := by
    by_contra hnot
    have hle : 1 / k ≤ bernoulliProfile t k a w := le_of_not_gt hnot
    have hbetween : 1 / k ∈ Icc (bernoulliProfile t k a 0) (bernoulliProfile t k a w) := by
      rw [bernoulliProfile_zero]
      exact ⟨(one_div_pos.mpr hk).le, hle⟩
    obtain ⟨v, hv, hval⟩ := intermediate_value_Icc hw.le
      (continuous_bernoulliProfile t k a ht0 ht1).continuousOn hbetween
    have hvne : v ≠ 0 := by
      intro hz
      rw [hz, bernoulliProfile_zero] at hval
      exact (ne_of_gt (one_div_pos.mpr hk)) hval.symm
    have hvpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hvne)
    exact hnocrit v hvpos ((bernoulliK_deriv_zero_iff t k a ht0 ht1 hk v hvpos).mpr hval)
  rw [(hasDerivAt_bernoulliK t k a ht0 ht1 hk w hw).deriv]
  apply div_neg_of_neg_of_pos _ (sq_pos_of_pos hw)
  have hscaled := (lt_div_iff₀ hk).mp hF
  nlinarith

theorem bernoulliK_strictAntiOn_of_no_critical {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hnocrit : ∀ w : ℝ, 0 < w → deriv (bernoulliK t k a) w ≠ 0) :
    StrictAntiOn (bernoulliK t k a) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · apply continuousOn_of_forall_continuousAt
    intro w hw
    exact (hasDerivAt_bernoulliK t k a ht0 ht1 hk w hw).continuousAt
  · intro w hw
    have hwpos : 0 < w := by simpa only [interior_Ioi, Set.mem_Ioi] using hw
    exact bernoulliK_deriv_neg_of_no_critical t k a ht0 ht1 hk hnocrit w hwpos

/-- Full critical-point dichotomy for every coefficient vector, including zero. -/
theorem bernoulliK_critical_dichotomy {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    (∃ w : ℝ, 0 < w ∧ deriv (bernoulliK t k a) w = 0 ∧
      (∀ v : ℝ, 0 < v → deriv (bernoulliK t k a) v = 0 → v = w) ∧
      (∀ v : ℝ, 0 < v → bernoulliK t k a w ≤ bernoulliK t k a v)) ∨
    ((∀ w : ℝ, 0 < w → deriv (bernoulliK t k a) w < 0) ∧
      StrictAntiOn (bernoulliK t k a) (Ioi 0)) := by
  by_cases hcrit : ∃ w : ℝ, 0 < w ∧ deriv (bernoulliK t k a) w = 0
  · obtain ⟨w, hw, hdw⟩ := hcrit
    have ha : ∃ i, a i ≠ 0 := by
      by_contra hnot
      push_neg at hnot
      have hsat := (bernoulliK_deriv_zero_iff t k a ht0 ht1 hk w hw).mp hdw
      have hzero : bernoulliProfile t k a w = 0 := by
        simp [bernoulliProfile, hnot, bernoulliMaximizer_zero, bernoulliCost_self]
      rw [hzero] at hsat
      exact (ne_of_gt (one_div_pos.mpr hk)) hsat.symm
    left
    refine ⟨w, hw, hdw, ?_, bernoulliK_critical_minimum t k a ht0 ht1 hk w hw hdw⟩
    intro v hv hdv
    exact bernoulliK_critical_unique t k a ht0 ht1 hk ha hv hw hdv hdw
  · have hnocrit : ∀ w : ℝ, 0 < w → deriv (bernoulliK t k a) w ≠ 0 := by
      intro w hw hdw
      exact hcrit ⟨w, hw, hdw⟩
    right
    exact ⟨bernoulliK_deriv_neg_of_no_critical t k a ht0 ht1 hk hnocrit,
      bernoulliK_strictAntiOn_of_no_critical t k a ht0 ht1 hk hnocrit⟩

end
end ProjectionChannels

