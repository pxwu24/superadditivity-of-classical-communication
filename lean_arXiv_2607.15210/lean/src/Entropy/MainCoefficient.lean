import Entropy.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Real Set Filter
noncomputable section
namespace AppendixB

/-- Twice-integrated inequality `s^(p-2) ≥ s^(-2)` on `[1,x]`,
proved by monotonicity of derivatives, without an integration hypothesis. -/
theorem power_remainder_lower (p x : ℝ) (hp : 0 < p) (hp1 : p ≠ 1)
    (hx : 1 ≤ x) :
    x - 1 - Real.log x ≤ (x ^ p - 1 - p * (x - 1)) / (p * (p - 1)) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp10 : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  let g : ℝ → ℝ := fun y => (y ^ (p - 1) - 1) / (p - 1) - 1 + y⁻¹
  have hg : ∀ y, 1 ≤ y → HasDerivAt g (y ^ (p - 2) - (y ^ 2)⁻¹) y := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith
    have hpow := Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hy0)
    have h := ((hpow.sub_const 1).div_const (p - 1)).sub_const 1 |>.add (hasDerivAt_inv hy0)
    convert h using 1 <;> dsimp [g]
    rw [show p - 1 - 1 = p - 2 by ring]
    field_simp
    <;> ring
  have hgmono : MonotoneOn g (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun y hy => (hg y hy).continuousAt.continuousWithinAt
    · exact fun y hy => (hg y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy1 : 1 ≤ y := interior_subset hy
      have hy0 : 0 < y := by linarith
      rw [(hg y hy1).deriv]
      have h := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith : (-2 : ℝ) ≤ p - 2)
      have he : y ^ (-2 : ℝ) = (y ^ 2)⁻¹ := by
        rw [Real.rpow_neg hy0.le]
        norm_num
      rw [he] at h
      exact sub_nonneg.mpr h
  have hgpos : ∀ y, 1 ≤ y → 0 ≤ g y := by
    intro y hy
    have := hgmono (by simp) hy hy
    simpa [g] using this
  let f : ℝ → ℝ := fun y =>
    (y ^ p - 1 - p * (y - 1)) / (p * (p - 1)) + Real.log y - y + 1
  have hf : ∀ y, 1 ≤ y → HasDerivAt f (g y) y := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith
    have hpow := Real.hasDerivAt_rpow_const (p := p) (Or.inl hy0)
    have hlin := ((hasDerivAt_id y).sub_const 1).const_mul p
    have h := ((((hpow.sub_const 1).sub hlin).div_const (p * (p - 1))).add
      (Real.hasDerivAt_log hy0)).sub (hasDerivAt_id y) |>.add_const 1
    convert h using 1 <;> dsimp [f, g]
    field_simp
    <;> ring
  have hfmono : MonotoneOn f (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun y hy => (hf y hy).continuousAt.continuousWithinAt
    · exact fun y hy => (hf y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hf y (interior_subset hy)).deriv]
      exact hgpos y (interior_subset hy)
  have := hfmono (by simp) hx hx
  simp only [f, Real.one_rpow, sub_self, mul_zero, zero_sub, zero_div, Real.log_one,
    add_zero, zero_sub, neg_add_cancel] at this
  linarith

/-- A rational Taylor bound certifies the logarithmic constant in the paper. -/
theorem log_sixteen_lt_three : Real.log 16 < 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have he : (16 : ℝ) < Real.exp 3 := by linarith
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr he

/-- A convenient lower bound at the von Neumann order. -/
theorem two_le_log_sixteen : 2 < Real.log 16 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≠ 1)
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
  have hlog : Real.log 16 = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  rw [hlog]
  linarith

/-- The coefficient gap used in the main theorem, including `p=1`.
This is unconditional once `p>0`; no entropy asymptotics are assumptions. -/
theorem main_coefficient_gap (p : ℝ) (hp : 0 < p) :
    25 * p * (3 - Real.log 16) ≤ Bpr p 5 375 - 300 * p := by
  by_cases hp1 : p = 1
  · subst p
    norm_num [Bpr]
    have h := two_le_log_sixteen
    nlinarith only [h]
  · have h := power_remainder_lower p 16 hp hp1 (by norm_num)
    norm_num at h
    have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 25 * p)
    have he : Bpr p 5 375 - 300 * p =
        25 * p * ((16 ^ p - 1 - p * 15) / (p * (p - 1))) - 300 * p := by
      simp only [Bpr, if_neg hp1]
      norm_num
      have hp0 : p ≠ 0 := ne_of_gt hp
      have hp10 : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
      have h1p : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
      field_simp
      <;> ring
    rw [he]
    nlinarith only [hmul]

/-- Strict positivity of the Bell witness coefficient for every positive order. -/
theorem main_coefficient_strict (p : ℝ) (hp : 0 < p) :
    300 * p < Bpr p 5 375 := by
  have h := main_coefficient_gap p hp
  have hpos : 0 < 25 * p * (3 - Real.log 16) :=
    mul_pos (mul_pos (by norm_num) hp) (sub_pos.mpr log_sixteen_lt_three)
  linarith

#print axioms power_remainder_lower
#print axioms log_sixteen_lt_three
#print axioms two_le_log_sixteen
#print axioms main_coefficient_gap
#print axioms main_coefficient_strict

end AppendixB
