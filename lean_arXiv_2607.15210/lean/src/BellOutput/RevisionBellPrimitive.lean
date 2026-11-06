import BellOutput.RevisionBellNegativeBranch
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The actual Bernoulli R-transform primitive used in (96), and
differentation of the inverse-Cauchy primitive. -/

open MeasureTheory Filter Finset
open scoped Topology BigOperators
noncomputable section
namespace RevisionBell
open ProjectionChannels

lemma bernoulliDual_add_parameter_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    0 < bernoulliDual t y + t := by
  have hsq := bernoulliDelta_sq ht0.le ht1.le y
  have hd := bernoulliDelta_pos ht0 ht1 y
  have hprod : 0 < t*(1-t) := mul_pos ht0 (sub_pos.mpr ht1)
  have haux : -(y+2*t-1) < bernoulliDelta t y := by
    nlinarith
  unfold bernoulliDual
  linarith

lemma bernoulliR_continuous_formula {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    bernoulliR t y = (bernoulliDual t y + t)/(bernoulliDual t y+1) := by
  have hg1 : 0 < bernoulliDual t y+1 := by
    linarith [bernoulliDual_add_parameter_pos ht0 ht1 y]
  by_cases hy : y=0
  · subst y
    have hg : bernoulliDual t 0 = 0 := by
      unfold bernoulliDual bernoulliDelta
      rw [show (0+2*t-1)^2+4*t*(1-t)=1 by ring, Real.sqrt_one]
      ring
    simp [bernoulliR, hg]
  · rw [bernoulliR, if_neg hy]
    apply (div_eq_div_iff hy hg1.ne').2
    nlinarith [bernoulliDual_quadratic ht0.le ht1.le y]

theorem continuous_bernoulliR {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Continuous (bernoulliR t) := by
  have hg : Continuous (bernoulliDual t) :=
    continuous_iff_continuousAt.mpr fun y => (hasDerivAt_bernoulliDual ht0 ht1 y).continuousAt
  have heq : bernoulliR t = fun y => (bernoulliDual t y+t)/(bernoulliDual t y+1) :=
    funext (bernoulliR_continuous_formula ht0 ht1)
  rw [heq]
  apply (hg.add continuous_const).div (hg.add continuous_const)
  intro y
  have := bernoulliDual_add_parameter_pos ht0 ht1 y
  linarith

/-- The primitive appearing in the paper is an actual interval integral. -/
def bernoulliPrimitive (t y : ℝ) : ℝ := ∫ v in (0 : ℝ)..y, bernoulliR t v

theorem hasDerivAt_bernoulliPrimitive {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    HasDerivAt (bernoulliPrimitive t) (bernoulliR t y) y := by
  have hc := continuous_bernoulliR ht0 ht1
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 y)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

@[simp] theorem bernoulliPrimitive_zero (t : ℝ) : bernoulliPrimitive t 0 = 0 := by
  simp [bernoulliPrimitive]

/-- Differentiating the candidate logarithmic potential cancels all terms
containing the derivative of `G`, by the inverse-Cauchy equation. -/
theorem hasDerivAt_inverse_cauchy_primitive
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) (G : ℝ → ℝ) (z d : ℝ)
    (hG : HasDerivAt G d z) (hG0 : G z ≠ 0)
    (hinv : (G z)⁻¹ + bernoulliFreeSumR k t a (G z) = z) :
    HasDerivAt (fun x => -Real.log (-G x)+x*G x-1-
      (k : ℝ)*∑ i, bernoulliPrimitive t (a i*G x/k)) (G z) z := by
  have hlog := (Real.hasDerivAt_log (neg_ne_zero.mpr hG0)).comp z hG.neg
  have hlin := (hasDerivAt_id z).mul hG
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_bernoulliPrimitive ht0 ht1 (a i*G z/k)).comp z
      ((hG.const_mul (a i)).div_const (k : ℝ)))
  have h := ((hlog.neg.add hlin).sub_const 1).sub (hsum.const_mul (k : ℝ))
  convert h using 1
  dsimp
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hs : (k : ℝ)*∑ i, bernoulliR t (a i*G z/k)*(a i*d/k) =
      d*bernoulliFreeSumR k t a (G z) := by
    unfold bernoulliFreeSumR
    simp only [mul_sum]
    apply sum_congr rfl
    intro i hi
    field_simp
    ring
  rw [hs]
  field_simp [hG0] at hinv ⊢
  have hmul := congrArg (fun x => x*d) hinv
  dsimp at hmul
  nlinarith only [hmul]

end RevisionBell
