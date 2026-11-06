import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positivity and quadratic remainders

The deterministic step in the smooth-test outlier argument: a nonnegative
function vanishing at an interior density has no linear term.  The result is
stated directly in terms of a quadratic remainder, so it also applies to
infinite sums without assuming twice differentiability of their sum.
-/

open Set
open scoped BigOperators

namespace ProjectionChannels.StrongConvergence

/-- Two applications of the mean value inequality give a quadratic Taylor
remainder.  The constant is deliberately non-sharp, avoiding integration. -/
theorem abs_quadratic_remainder_le_of_second_derivative_bound
    {f f' f'' : ℝ → ℝ} {M t s : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' x) x)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |f'' x| ≤ M)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    |f s - f t - f' t * (s - t)| ≤ M * (s - t) ^ 2 := by
  let g : ℝ → ℝ := fun x => f x - f t - f' t * (x - t)
  have hsub : uIcc t s ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc ht hs
  have hdist {u : ℝ} (hu : u ∈ uIcc t s) : |u - t| ≤ |s - t| := by
    rcases mem_uIcc.mp hu with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h.1),
        abs_of_nonneg (sub_nonneg.mpr (h.1.trans h.2))]
      linarith [h.2]
    · rw [abs_of_nonpos (sub_nonpos.mpr h.2),
        abs_of_nonpos (sub_nonpos.mpr (h.1.trans h.2))]
      linarith [h.1]
  have hg : ∀ x ∈ uIcc t s, HasDerivWithinAt g (f' x - f' t) (uIcc t s) x := by
    intro x hx
    have h := ((hf x (hsub hx)).sub_const (f t)).sub
      (((hasDerivAt_id x).sub_const t).const_mul (f' t))
    simpa [g] using h.hasDerivWithinAt (s := uIcc t s)
  have hgb : ∀ x ∈ uIcc t s, ‖f' x - f' t‖ ≤ M * ‖s - t‖ := by
    intro x hx
    have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hf' y hy).hasDerivWithinAt)
      (fun y hy => by simpa only [Real.norm_eq_abs] using hb y hy)
      ht (hsub hx)
    exact h.trans (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hdist hx) hM)
  have h := (convex_uIcc t s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hg hgb left_mem_uIcc right_mem_uIcc
  calc
    |f s - f t - f' t * (s - t)| = ‖g s - g t‖ := by simp [g, Real.norm_eq_abs]
    _ ≤ (M * ‖s - t‖) * ‖s - t‖ := h
    _ = M * (s - t) ^ 2 := by rw [mul_assoc, ← pow_two, Real.norm_eq_abs, sq_abs]

/-- Polynomial version of the two-mean-value quadratic estimate. -/
theorem polynomial_abs_quadratic_remainder_le
    (p : Polynomial ℝ) {M t s : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |p.derivative.derivative.eval x| ≤ M)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    |p.eval s - p.eval t - p.derivative.eval t * (s - t)| ≤ M * (s - t) ^ 2 :=
  abs_quadratic_remainder_le_of_second_derivative_bound hM
    (fun x _ => p.hasDerivAt x) (fun x _ => p.derivative.hasDerivAt x) hb ht hs

/-- Positivity forces the coefficient of the linear term in a quadratic
remainder estimate to vanish at an interior zero. -/
theorem slope_eq_zero_of_nonneg_quadratic_remainder
    {f : ℝ → ℝ} {t L M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 ≤ M)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f s) (hft : f t = 0)
    (hr : ∀ s ∈ Icc (0 : ℝ) 1,
      |f s - f t - L * (s - t)| ≤ M * (s - t) ^ 2) :
    L = 0 := by
  have hMp : 0 < M + 1 := by linarith
  have hnotpos : ¬ 0 < L := by
    intro hL
    let h := min t (L / (M + 1))
    have hh : 0 < h := lt_min ht0 (div_pos hL hMp)
    have hht : h ≤ t := min_le_left _ _
    have hhL : h * (M + 1) ≤ L :=
      (le_div_iff₀ hMp).mp (min_le_right _ _)
    have hs : t - h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hp := hf (t - h) hs
    have he := (le_abs_self (f (t - h) - f t - L * (t - h - t))).trans
      (hr (t - h) hs)
    rw [hft] at he
    have hprod : M * h ^ 2 < L * h := by
      have hMh : M * h < L := by nlinarith
      nlinarith [mul_lt_mul_of_pos_right hMh hh]
    nlinarith
  have hnotneg : ¬ L < 0 := by
    intro hL
    let h := min (1 - t) ((-L) / (M + 1))
    have hh : 0 < h := lt_min (by linarith) (div_pos (by linarith) hMp)
    have hht : h ≤ 1 - t := min_le_left _ _
    have hhL : h * (M + 1) ≤ -L :=
      (le_div_iff₀ hMp).mp (min_le_right _ _)
    have hs : t + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hp := hf (t + h) hs
    have he := (le_abs_self (f (t + h) - f t - L * (t + h - t))).trans
      (hr (t + h) hs)
    rw [hft] at he
    have hprod : M * h ^ 2 < (-L) * h := by
      have hMh : M * h < -L := by nlinarith
      nlinarith [mul_lt_mul_of_pos_right hMh hh]
    nlinarith
  exact le_antisymm (le_of_not_gt hnotpos) (le_of_not_gt hnotneg)

/-- A nonnegative function with an interior zero and a bounded quadratic
remainder is bounded by the quadratic term alone. -/
theorem le_quadratic_of_nonneg_quadratic_remainder
    {f : ℝ → ℝ} {t L M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 ≤ M)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f s) (hft : f t = 0)
    (hr : ∀ s ∈ Icc (0 : ℝ) 1,
      |f s - f t - L * (s - t)| ≤ M * (s - t) ^ 2)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    f s ≤ M * (s - t) ^ 2 := by
  have hL := slope_eq_zero_of_nonneg_quadratic_remainder ht0 ht1 hM hf hft hr
  have h := hr s hs
  simpa [hft, hL, abs_of_nonneg (hf s hs)] using h

/-- Quadratic remainders pass to any summable weighted family.  This only
requires convergence of the values and the linear terms, not differentiability
of their sum. -/
theorem hasSum_abs_quadratic_remainder_le
    {ι : Type*} {c B D : ι → ℝ} {P : ι → ℝ → ℝ}
    {f : ℝ → ℝ} {t s L M : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hvalues : ∀ x ∈ Icc (0 : ℝ) 1, HasSum (fun i => c i * P i x) (f x))
    (hlinear : HasSum (fun i => c i * D i) L)
    (hmajorant : HasSum (fun i => |c i| * B i) M)
    (hr : ∀ i, |P i s - P i t - D i * (s - t)| ≤ B i * (s - t) ^ 2) :
    |f s - f t - L * (s - t)| ≤ M * (s - t) ^ 2 := by
  have hsum : HasSum (fun i => c i * (P i s - P i t - D i * (s - t)))
      (f s - f t - L * (s - t)) := by
    convert ((hvalues s hs).sub (hvalues t ht)).sub (hlinear.mul_right (s - t)) using 1
    ext i
    ring
  have hbound : ∀ i,
      ‖c i * (P i s - P i t - D i * (s - t))‖ ≤ (|c i| * B i) * (s - t) ^ 2 := by
    intro i
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |c i| * (B i * (s - t) ^ 2) := mul_le_mul_of_nonneg_left (hr i) (abs_nonneg _)
      _ = _ := by ring
  simpa only [Real.norm_eq_abs] using
    hsum.norm_le_of_bounded (hmajorant.mul_right ((s - t) ^ 2)) hbound

/-- The positivity step used for smooth spectral tests, stated for an infinite
polynomial expansion.  The second-derivative majorants are summable after
weighting, and the function vanishes at an interior density. -/
theorem polynomial_series_le_quadratic_of_nonneg
    {ι : Type*} {c B : ι → ℝ} {P : ι → Polynomial ℝ}
    {f : ℝ → ℝ} {t L M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hB : ∀ i, 0 ≤ B i)
    (hvalues : ∀ x ∈ Icc (0 : ℝ) 1, HasSum (fun i => c i * (P i).eval x) (f x))
    (hlinear : HasSum (fun i => c i * (P i).derivative.eval t) L)
    (hmajorant : HasSum (fun i => |c i| * B i) M)
    (hbound : ∀ i x, x ∈ Icc (0 : ℝ) 1 → |(P i).derivative.derivative.eval x| ≤ B i)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) (hft : f t = 0)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    f s ≤ M * (s - t) ^ 2 := by
  have hM : 0 ≤ M := HasSum.nonneg (fun i => mul_nonneg (abs_nonneg _) (hB i)) hmajorant
  refine le_quadratic_of_nonneg_quadratic_remainder (L := L) ht0 ht1 hM hf hft ?_ hs
  intro x hx
  apply hasSum_abs_quadratic_remainder_le ⟨ht0.le, ht1.le⟩ hx hvalues hlinear hmajorant
  intro i
  exact polynomial_abs_quadratic_remainder_le (P i) (hB i) (hbound i)
    ⟨ht0.le, ht1.le⟩ hx

/-- The floor-rank error `|s - t| ≤ 1 / N` turns a quadratic density estimate
and an `N⁻²` trace approximation into an `N⁻²` trace bound. -/
theorem trace_le_inverse_sq_of_quadratic_density_bound
    {v E s t M C N : ℝ} (hM : 0 ≤ M) (hN : 0 < N)
    (hdensity : |s - t| ≤ 1 / N)
    (hquad : v ≤ M * (s - t) ^ 2)
    (htrace : E ≤ v + C / N ^ 2) :
    E ≤ (M + C) / N ^ 2 := by
  have hsq : (s - t) ^ 2 ≤ (1 / N) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (s - t)) hdensity
    simpa only [← pow_two, sq_abs] using h
  calc
    E ≤ v + C / N ^ 2 := htrace
    _ ≤ M * (s - t) ^ 2 + C / N ^ 2 := add_le_add_right hquad _
    _ ≤ M * (1 / N) ^ 2 + C / N ^ 2 :=
      add_le_add_right (mul_le_mul_of_nonneg_left hsq hM) _
    _ = (M + C) / N ^ 2 := by field_simp [hN.ne']

open scoped ContDiff

/-- Smooth function detecting an eigenvalue above the proposed upper edge. -/
noncomputable def edgeTest (r ε x : ℝ) : ℝ := Real.smoothTransition ((x - r) / ε)

theorem edgeTest_nonneg (r ε x : ℝ) : 0 ≤ edgeTest r ε x := Real.smoothTransition.nonneg _

theorem edgeTest_le_one (r ε x : ℝ) : edgeTest r ε x ≤ 1 := Real.smoothTransition.le_one _

theorem edgeTest_contDiff (r ε : ℝ) : ContDiff ℝ ∞ (edgeTest r ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε)

theorem edgeTest_of_le {r ε x : ℝ} (hε : 0 < ε) (hx : x ≤ r) : edgeTest r ε x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

theorem edgeTest_of_ge {r ε x : ℝ} (hε : 0 < ε) (hx : r + ε ≤ x) : edgeTest r ε x = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div₀ hε).2 (by linarith))

#print axioms polynomial_series_le_quadratic_of_nonneg
#print axioms trace_le_inverse_sq_of_quadratic_density_bound
#print axioms edgeTest_contDiff

end ProjectionChannels.StrongConvergence
