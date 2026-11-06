import RandomCompression.BernoulliCalculus
import Dimension182.K182ShapeCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The two-value part of Appendix C.1

This file proves the scalar calculus asserted in Step 4 of Lemma C.1.
For the actual Bernoulli cost, the Lagrange stationarity function
`log v - μ c_t'(v)` takes each value at most twice on `(0,1/4)`.
If it takes a value at two distinct points, its derivatives there have
the strict signs used by the second-variation argument.

The boundary-coordinate exclusion and the existence of a positive
Lagrange multiplier for a constrained entropy minimizer are separate
obligations. No minimizer-shape conclusion is assumed in these proofs.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace ProjectionChannels.RevisionK182

def stationary (t μ v : ℝ) : ℝ :=
  Real.log v - μ * deriv (bernoulliCost t) v

def stationarySlope (t μ v : ℝ) : ℝ :=
  v⁻¹ - μ * (Real.sqrt (t * (1-t)) /
    (2 * Real.sqrt (v * (1-v)) ^ 3))

/-- Positivity of the Lagrange multiplier follows from stationarity and
two unequal positive coordinates; it need not be supplied by a KKT sign
convention. -/
theorem multiplier_pos_of_equal_level {t μ a b : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (ha : a ∈ Ioo 0 (1/4 : ℝ)) (hb : b ∈ Ioo 0 (1/4 : ℝ))
    (hab : a < b) (heq : stationary t μ a = stationary t μ b) : 0 < μ := by
  have hlog : Real.log a < Real.log b := Real.log_lt_log ha.1 hab
  have hcost : deriv (bernoulliCost t) a < deriv (bernoulliCost t) b :=
    strictMonoOn_deriv_bernoulliCost ht0 ht1
      ⟨ha.1, by linarith only [ha.2]⟩
      ⟨hb.1, by linarith only [hb.2]⟩ hab
  unfold stationary at heq
  by_contra hn
  have hm : μ ≤ 0 := le_of_not_gt hn
  have hmul := mul_nonpos_of_nonpos_of_nonneg hm (sub_nonneg.mpr hcost.le)
  nlinarith only [heq, hlog, hmul]

theorem hasDerivAt_stationary {t μ v : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hv : v ∈ Ioo 0 (1/4 : ℝ)) :
    HasDerivAt (stationary t μ) (stationarySlope t μ v) v := by
  exact (Real.hasDerivAt_log (ne_of_gt hv.1)).sub
    ((hasDerivAt_deriv_bernoulliCost ht0.le ht1.le hv.1
      (by linarith only [hv.2])).const_mul μ)

theorem weighted_stationarySlope {t μ v : ℝ}
    (hv : v ∈ Ioo 0 (1/4 : ℝ)) :
    v * stationarySlope t μ v =
      1 - μ * Real.sqrt (t * (1-t)) /
        (2 * Real.sqrt (v * (1-v)^3)) := by
  have hv1 : 0 < 1-v := by linarith only [hv.2]
  have hr : 0 < Real.sqrt (v * (1-v)) := Real.sqrt_pos.mpr (mul_pos hv.1 hv1)
  have hrsq := Real.sq_sqrt (mul_nonneg hv.1.le hv1.le)
  have hid : Real.sqrt (v * (1-v)^3) = (1-v) * Real.sqrt (v * (1-v)) := by
    rw [show v * (1-v)^3 = (1-v)^2 * (v * (1-v)) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hv1]
  rw [hid]
  unfold stationarySlope
  rw [show Real.sqrt (v * (1-v)) ^ 3 = v * ((1-v) * Real.sqrt (v * (1-v))) by
    calc
      _ = Real.sqrt (v * (1-v)) ^ 2 * Real.sqrt (v * (1-v)) := by ring
      _ = v * ((1-v) * Real.sqrt (v * (1-v))) := by rw [hrsq]; ring]
  rw [mul_sub, mul_inv_cancel₀ (ne_of_gt hv.1)]
  congr 1
  rw [← mul_div_assoc, ← mul_div_assoc]
  rw [show 2 * (v * ((1-v) * Real.sqrt (v * (1-v)))) =
      v * (2 * ((1-v) * Real.sqrt (v * (1-v)))) by ring]
  exact mul_div_mul_left _ _ (ne_of_gt hv.1)

/-- The sign of the derivative is controlled by a strictly increasing
function. This is stronger and more precise than merely asserting one
possible change of sign. -/
theorem weighted_stationarySlope_strictMono {t μ : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hμ : 0 < μ) :
    StrictMonoOn (fun v => v * stationarySlope t μ v) (Ioo 0 (1/4 : ℝ)) := by
  intro a ha b hb hab
  change a * stationarySlope t μ a < b * stationarySlope t μ b
  rw [weighted_stationarySlope ha, weighted_stationarySlope hb]
  have hroota : 0 < Real.sqrt (a * (1-a)^3) := by
    apply Real.sqrt_pos.mpr
    have : 0 < 1-a := by linarith only [ha.2]
    exact mul_pos ha.1 (pow_pos this _)
  have hrootb : 0 < Real.sqrt (b * (1-b)^3) := by
    apply Real.sqrt_pos.mpr
    have : 0 < 1-b := by linarith only [hb.2]
    exact mul_pos hb.1 (pow_pos this _)
  have hden := K182ShapeCalculus.denominator_strictMono ha hb hab
  have hnum : 0 < μ * Real.sqrt (t * (1-t)) := by
    have : 0 < 1-t := sub_pos.mpr ht1
    positivity
  have hd : μ * Real.sqrt (t * (1-t)) / (2 * Real.sqrt (b * (1-b)^3)) <
      μ * Real.sqrt (t * (1-t)) / (2 * Real.sqrt (a * (1-a)^3)) := by
    apply div_lt_div_of_pos_left hnum (by positivity)
    linarith only [hden]
  linarith only [hd]

/-- Rolle's theorem places the unique stationary point strictly between
any two equal-level points. Strict monotonicity of the weighted derivative
then gives the signs at both endpoints. -/
theorem stationary_equal_level_derivative_signs {t μ a b : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hμ : 0 < μ)
    (ha : a ∈ Ioo 0 (1/4 : ℝ)) (hb : b ∈ Ioo 0 (1/4 : ℝ))
    (hab : a < b) (heq : stationary t μ a = stationary t μ b) :
    stationarySlope t μ a < 0 ∧ 0 < stationarySlope t μ b := by
  have hsub : Icc a b ⊆ Ioo 0 (1/4 : ℝ) := by
    intro x hx
    exact ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  obtain ⟨c, hc, hzero⟩ := exists_hasDerivAt_eq_zero hab
    (fun x hx => (hasDerivAt_stationary ht0 ht1 (hsub hx)).continuousAt.continuousWithinAt)
    heq (fun x hx => hasDerivAt_stationary ht0 ht1 (hsub ⟨hx.1.le, hx.2.le⟩))
  have hcin : c ∈ Ioo 0 (1/4 : ℝ) := hsub ⟨hc.1.le, hc.2.le⟩
  have hl := weighted_stationarySlope_strictMono ht0 ht1 hμ ha hcin hc.1
  have hr := weighted_stationarySlope_strictMono ht0 ht1 hμ hcin hb hc.2
  dsimp only at hl hr
  rw [hzero, mul_zero] at hl hr
  constructor
  · nlinarith only [hl, ha.1]
  · exact (mul_pos_iff_of_pos_left hb.1).mp hr

/-- The scalar stationarity equation has at most two solutions in the
coordinate interval of Lemma C.1. -/
theorem stationary_no_three_equal_levels {t μ a b c : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hμ : 0 < μ)
    (ha : a ∈ Ioo 0 (1/4 : ℝ)) (hb : b ∈ Ioo 0 (1/4 : ℝ))
    (hc : c ∈ Ioo 0 (1/4 : ℝ)) (hab : a < b) (hbc : b < c)
    (heqab : stationary t μ a = stationary t μ b)
    (heqbc : stationary t μ b = stationary t μ c) : False := by
  have hp := (stationary_equal_level_derivative_signs ht0 ht1 hμ ha hb hab heqab).2
  have hn := (stationary_equal_level_derivative_signs ht0 ht1 hμ hb hc hbc heqbc).1
  exact (not_lt_of_ge hp.le) hn

/-- A nonconstant vector satisfying the actual Lagrange stationarity
equations has exactly two coordinate values. No two-value or one-high
shape is supplied as a hypothesis. -/
theorem stationary_vector_two_values {ι : Type*} {t μ : ℝ} {u : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hμ : 0 < μ)
    (hu : ∀ i, u i ∈ Ioo 0 (1/4 : ℝ))
    (hstationary : ∀ i j, stationary t μ (u i) = stationary t μ (u j))
    (hnonconstant : ∃ i j, u i ≠ u j) :
    ∃ a b : ℝ, a ∈ Ioo 0 (1/4 : ℝ) ∧ b ∈ Ioo 0 (1/4 : ℝ) ∧
      a < b ∧ (∀ i, u i = a ∨ u i = b) ∧
      (∃ i, u i = a) ∧ (∃ i, u i = b) ∧
      stationarySlope t μ a < 0 ∧ 0 < stationarySlope t μ b := by
  obtain ⟨i, j, hij⟩ := hnonconstant
  have pair : ∃ i j, u i < u j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  obtain ⟨i, j, hij⟩ := pair
  refine ⟨u i, u j, hu i, hu j, hij, ?_, ⟨i,rfl⟩, ⟨j,rfl⟩,
    stationary_equal_level_derivative_signs ht0 ht1 hμ (hu i) (hu j) hij
      (hstationary i j)⟩
  intro l
  by_contra h
  push_neg at h
  rcases lt_or_gt_of_ne h.1 with hli | hil
  · exact stationary_no_three_equal_levels ht0 ht1 hμ (hu l) (hu i) (hu j)
      hli hij (hstationary l i) (hstationary i j)
  · rcases lt_or_gt_of_ne h.2 with hlj | hjl
    · exact stationary_no_three_equal_levels ht0 ht1 hμ (hu i) (hu l) (hu j)
        hil hlj (hstationary i l) (hstationary l j)
    · exact stationary_no_three_equal_levels ht0 ht1 hμ (hu i) (hu j) (hu l)
        hij hjl (hstationary i j) (hstationary j l)

#print axioms hasDerivAt_stationary
#print axioms multiplier_pos_of_equal_level
#print axioms weighted_stationarySlope
#print axioms weighted_stationarySlope_strictMono
#print axioms stationary_equal_level_derivative_signs
#print axioms stationary_no_three_equal_levels
#print axioms stationary_vector_two_values

end ProjectionChannels.RevisionK182
