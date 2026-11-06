import RandomCompression.RevisionBernoulliHolomorphic

/-!
Positive support of the Bernoulli free-sum law is a consequence of the proved
right-edge formula, applied to the reflected actual measure. No positive-support
or inverse-moment hypothesis is added to the law definition.
-/

open MeasureTheory Filter Finset
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels

theorem realCauchyTransform_map_neg (μ : Measure ℝ) (x : ℝ) :
    realCauchyTransform (Measure.map (fun s : ℝ => -s) μ) x =
      -realCauchyTransform μ (-x) := by
  unfold realCauchyTransform
  rw [integral_map_of_stronglyMeasurable (by fun_prop)
    (show StronglyMeasurable (fun s : ℝ => (x-s)⁻¹) from
      (by fun_prop : Measurable (fun s : ℝ => (x-s)⁻¹)).stronglyMeasurable),
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards with s
  rw [show -x-s = -(x-(-s)) by ring, inv_neg, neg_neg]

theorem bernoulliFreeSumR_reflection (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (w : ℝ) :
    bernoulliFreeSumR k t (fun i => -a i) (-w) = -bernoulliFreeSumR k t a w := by
  unfold bernoulliFreeSumR
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  rw [show (-a i/(k:ℝ))*(-w)=(a i/(k:ℝ))*w by ring]
  ring

theorem IsBernoulliFreeSumLaw.reflect {k : ℕ} {t : ℝ} {a : Fin k → ℝ}
    {μ : Measure ℝ} (h : IsBernoulliFreeSumLaw k t a μ) :
    IsBernoulliFreeSumLaw k t (fun i => -a i) (Measure.map (fun s : ℝ => -s) μ) := by
  letI := h.probability
  refine ⟨isProbabilityMeasure_map (by fun_prop), ?_, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := h.compactlySupported
    refine ⟨M, (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).mpr ?_⟩
    simpa only [abs_neg] using hM
  · filter_upwards [tendsto_neg_atTop_atBot.eventually h.inverseGermLeft] with x hx
    rw [realCauchyTransform_map_neg, inv_neg, bernoulliFreeSumR_reflection]
    linarith
  · filter_upwards [tendsto_neg_atBot_atTop.eventually h.inverseGerm] with x hx
    rw [realCauchyTransform_map_neg, inv_neg, bernoulliFreeSumR_reflection]
    linarith

theorem bernoulli_feasible_weighted_mass_pos {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (hkt : 1 < (k : ℝ)^2*t)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {u : Fin k → ℝ} (hu : u ∈ bernoulliFeasible t (k:ℝ)) :
    0 < ∑ i, a i*u i := by
  have hn : 0 ≤ ∑ i, a i*u i := sum_nonneg fun i _ => mul_nonneg (ha i).le (hu.1 i)
  by_contra h
  have hs : ∑ i, a i*u i = 0 := le_antisymm (le_of_not_gt h) hn
  have heach := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ univ) =>
    mul_nonneg (ha i).le (hu.1 i))).mp hs
  have hz (i : Fin k) : u i = 0 := (mul_eq_zero.mp (heach i (mem_univ i))).resolve_left (ha i).ne'
  have hb := hu.2.2
  simp only [hz, bernoulliCost_zero ht0.le, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hb
  have hb' := (le_div_iff₀ (Nat.cast_pos.mpr hk : (0:ℝ)<k)).mp hb
  nlinarith only [hb', hkt]

theorem bernoulli_negative_support_value {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    sSup (bernoulliObjectiveValues t (k:ℝ) (fun i => -a i)) < 0 := by
  obtain ⟨M, hmax, _⟩ := bernoulli_full_duality t (k:ℝ) (fun i => -a i)
    ht0 ht1 (Nat.cast_pos.mpr hk)
  rw [hmax.csSup_eq]
  obtain ⟨u, hu, huM⟩ := hmax.1
  have hp := bernoulli_feasible_weighted_mass_pos hk ht0 hkt a ha hu
  rw [← huM]
  simpa only [neg_mul, sum_neg_distrib] using neg_neg_of_pos hp

/-- Every actual Bernoulli free-sum law with strictly positive coefficients
has support uniformly bounded away from zero when k²t>1. -/
theorem IsBernoulliFreeSumLaw.positive_bounds {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (μ : Measure ℝ)
    (hμ : IsBernoulliFreeSumLaw k t a μ) :
    ∃ m M : ℝ, 0 < m ∧ ∀ᵐ s ∂μ, m ≤ s ∧ s ≤ M := by
  let ν := Measure.map (fun s : ℝ => -s) μ
  have hν : IsBernoulliFreeSumLaw k t (fun i => -a i) ν := hμ.reflect
  let r := sSup (realMeasureSupport ν)
  have hr : r < 0 := by
    dsimp [r]
    rw [bernoulli_free_sum_right_edge hk ht0 ht1 (fun i => -a i) ν hν]
    exact bernoulli_negative_support_value hk ht0 ht1 hkt a ha
  have hlo : ∀ᵐ s ∂μ, -r ≤ s := by
    have hh := ae_of_ae_map (by fun_prop : AEMeasurable (fun s : ℝ => -s) μ) hν.right_edge.2
    filter_upwards [hh] with s hs
    change -s ≤ r at hs
    linarith
  obtain ⟨M, hM⟩ := hμ.compactlySupported
  refine ⟨-r, M, neg_pos.mpr hr, ?_⟩
  filter_upwards [hlo, hM] with s hs hsM
  exact ⟨hs, (le_abs_self s).trans hsM⟩

end ProjectionChannels
