import Preliminaries.PreliminariesLegendre
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-! Scalar boundary perturbation estimates for Appendix C.1. -/

namespace ProjectionChannels.RevisionK182
open Filter Set
open scoped Topology
noncomputable section

theorem square_log_derivative_zero :
    HasDerivAt (fun x : ℝ => x ^ 2 * Real.log (x ^ 2)) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h := ((Real.continuous_mul_log.continuousAt (x := (0 : ℝ))).tendsto.const_mul 2).mono_left
    (show nhdsWithin 0 {0}ᶜ ≤ nhds (0 : ℝ) from nhdsWithin_le_nhds)
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [slope_def_field, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_mul,
    Real.log_pow]
  field_simp
  <;> ring

theorem scaled_square_log_derivative_zero (M : ℝ) (hM : 0 < M) :
    HasDerivAt (fun x : ℝ => M * x ^ 2 * Real.log (M * x ^ 2)) 0 0 := by
  have heq (x : ℝ) : M * x ^ 2 * Real.log (M * x ^ 2) =
      M * (x ^ 2 * Real.log (x ^ 2)) + (M * Real.log M) * x ^ 2 := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_mul hM.ne' (pow_ne_zero _ hx)]
      ring
  simp_rw [heq]
  convert (square_log_derivative_zero.const_mul M).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (M * Real.log M)) using 1 <;> norm_num

/-- Adding mass `M ε²` in a zero coordinate lowers the Bernoulli cost to
first order in positive `ε`, while its entropy contribution has derivative zero. -/
theorem cost_scaled_square_right_derivative {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M) :
    HasDerivWithinAt (fun x : ℝ => bernoulliCost t (M * x ^ 2))
      (-2 * Real.sqrt (t * (1-t)) * Real.sqrt M) (Ici 0) 0 := by
  let g : ℝ → ℝ := fun x => t + (1-2*t)*M*x^2 -
    2 * Real.sqrt (t*(1-t)) * Real.sqrt M * x * Real.sqrt (1-M*x^2)
  have hp : HasDerivAt (fun x : ℝ => x^2) 0 0 := by
    convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num
  have hq : HasDerivAt (fun x : ℝ => 1-M*x^2) 0 0 := by
    convert (hp.const_mul M).const_sub 1 using 1 <;> norm_num
  have hsq : HasDerivAt (fun x : ℝ => Real.sqrt (1-M*x^2)) 0 0 := by
    convert hq.sqrt (by norm_num : (1-M*(0:ℝ)^2) ≠ 0) using 1 <;> norm_num
  have hg : HasDerivAt g (-2 * Real.sqrt (t*(1-t)) * Real.sqrt M) 0 := by
    have h := ((hp.const_mul ((1-2*t)*M)).const_add t).sub
      (((hasDerivAt_id (0 : ℝ)).const_mul
        (2 * Real.sqrt (t*(1-t)) * Real.sqrt M)).mul hsq)
    convert h using 1 <;> simp [g] <;> ring
  apply hg.hasDerivWithinAt.congr_of_eventuallyEq
  · have hsmall : ∀ᶠ x : ℝ in 𝓝 0, M*x^2 < 1 := by
      exact (show ContinuousAt (fun x : ℝ => M*x^2) 0 by fun_prop).eventually
        (Iio_mem_nhds (by norm_num : M*(0:ℝ)^2 < 1))
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hx0
    have hxnonneg : 0 ≤ x := hx0
    rw [bernoulliCost_expansion ht0.le ht1.le (by positivity) hx.le]
    rw [Real.sqrt_mul (show 0 ≤ M*x^2 by positivity), Real.sqrt_mul hM.le,
      Real.sqrt_sq hxnonneg]
    dsimp [g]
    ring
  · simp [bernoulliCost, g, Real.sq_sqrt ht0.le]

theorem quartic_log_derivative (M : ℝ) (hM : 0 < M) (x : ℝ) :
    HasDerivAt (fun y : ℝ => M*y^4 * Real.log (M*y^4))
      (4*M*x^3 * (Real.log (M*x^4)+1)) x := by
  by_cases hx : x = 0
  · subst x
    have hf : HasDerivAt (fun x : ℝ => M*x^2*Real.log (M*x^2)) 0 ((0:ℝ)^2) := by
      simpa using scaled_square_log_derivative_zero M hM
    have h := hf.comp (h := fun x : ℝ => x^2) 0
      (show HasDerivAt (fun x : ℝ => x^2) 0 0 by
        convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num)
    convert h using 1
    · ext y
      simp only [Function.comp_apply, ← pow_mul]
    · norm_num
  · have hpos : M*x^4 ≠ 0 := mul_ne_zero hM.ne' (pow_ne_zero _ hx)
    have h := (Real.hasDerivAt_mul_log hpos).comp x
      (((hasDerivAt_id x).pow 4).const_mul M)
    convert h using 1 <;> simp only [id_eq, Function.comp_apply] <;> ring

theorem quartic_log_second_derivative_zero (M : ℝ) (hM : 0 < M) :
    HasDerivAt (deriv (fun x : ℝ => M*x^4 * Real.log (M*x^4))) 0 0 := by
  have hd : deriv (fun x : ℝ => M*x^4 * Real.log (M*x^4)) =
      fun x => 4*M*x^3 * (Real.log (M*x^4)+1) := by
    funext x
    exact (quartic_log_derivative M hM x).deriv
  rw [hd, hasDerivAt_iff_tendsto_slope]
  have hc : Continuous (fun x : ℝ =>
      4*M*x^2*(Real.log M+1) + 16*M*x*(x*Real.log x)) := by
    exact ((continuous_const.mul (continuous_id.pow 2)).mul continuous_const).add
      ((continuous_const.mul continuous_id).mul Real.continuous_mul_log)
  have h := hc.continuousAt.tendsto.mono_left
    (show nhdsWithin 0 {0}ᶜ ≤ nhds (0 : ℝ) from nhdsWithin_le_nhds)
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [slope_def_field, sub_zero, zero_pow (by decide : 3 ≠ 0), mul_zero,
    zero_mul, Real.log_mul hM.ne' (pow_ne_zero 4 hx0), Real.log_pow]
  field_simp
  <;> ring

theorem cost_scaled_quartic_second_derivative {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M) :
    HasDerivAt (deriv (fun x : ℝ => bernoulliCost t (M*x^4)))
      (-4 * Real.sqrt (t*(1-t)) * Real.sqrt M) 0 := by
  let A := (1-2*t)*M
  let C := 2*Real.sqrt (t*(1-t))*Real.sqrt M
  let f : ℝ → ℝ := fun x => t+A*x^4-C*x^2*Real.sqrt (1-M*x^4)
  let v : ℝ → ℝ := fun x => (-4*M*x^3)/(2*Real.sqrt (1-M*x^4))
  let f' : ℝ → ℝ := fun x => 4*A*x^3 - C*(2*x*Real.sqrt (1-M*x^4)+x^2*v x)
  have hs (x : ℝ) (hx : 1-M*x^4 ≠ 0) :
      HasDerivAt (fun y : ℝ => Real.sqrt (1-M*y^4)) (v x) x := by
    have h := ((((hasDerivAt_id x).pow 4).const_mul M).const_sub 1).sqrt hx
    convert h using 1 <;> simp only [v, id_eq] <;> ring
  have hf (x : ℝ) (hx : 1-M*x^4 ≠ 0) : HasDerivAt f (f' x) x := by
    have h := ((((hasDerivAt_id x).pow 4).const_mul A).const_add t).sub
      ((((hasDerivAt_id x).pow 2).const_mul C).mul (hs x hx))
    convert h using 1 <;> simp only [f, f', id_eq] <;> ring
  have hs0 : HasDerivAt (fun y : ℝ => Real.sqrt (1-M*y^4)) 0 0 := by
    simpa [v] using hs 0 (by norm_num)
  have hv0 : HasDerivAt v 0 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul (-4*M)).div
      (hs0.const_mul 2) (by norm_num : 2*Real.sqrt (1-M*(0:ℝ)^4) ≠ 0)
    convert h using 1 <;> simp [v]
  have hfp : HasDerivAt f' (-2*C) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul (4*A)).sub
      (((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul hs0).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).mul hv0)).const_mul C)
    convert h using 1 <;> simp [f', v] <;> ring
  have hsmall : ∀ᶠ x : ℝ in 𝓝 0, M*x^4 < 1 :=
    (show ContinuousAt (fun x : ℝ => M*x^4) 0 by fun_prop).eventually
      (Iio_mem_nhds (by norm_num : M*(0:ℝ)^4 < 1))
  have heq : (fun x : ℝ => bernoulliCost t (M*x^4)) =ᶠ[𝓝 0] f := by
    filter_upwards [hsmall] with x hx
    rw [bernoulliCost_expansion ht0.le ht1.le (by positivity) hx.le,
      Real.sqrt_mul (show 0 ≤ M*x^4 by positivity), Real.sqrt_mul hM.le]
    have hx4 : Real.sqrt (x^4) = x^2 := by
      rw [show x^4 = (x^2)^2 by ring, Real.sqrt_sq (sq_nonneg x)]
    rw [hx4]
    dsimp [f, A, C]
    ring
  have hd : deriv f =ᶠ[𝓝 0] f' := by
    filter_upwards [hsmall] with x hx
    exact (hf x (ne_of_gt (sub_pos.mpr hx))).deriv
  have hresult := hfp.congr_of_eventuallyEq (heq.deriv.trans hd)
  convert hresult using 1
  dsimp [C]
  ring

theorem cost_scaled_quartic_derivative_zero {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M) :
    HasDerivAt (fun x : ℝ => bernoulliCost t (M*x^4)) 0 0 := by
  have hp : HasDerivAt (fun x : ℝ => x^2) 0 0 := by
    convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num
  have hc : HasDerivWithinAt (fun x : ℝ => bernoulliCost t (M*x^2))
      (-2*Real.sqrt (t*(1-t))*Real.sqrt M) (Ici 0) ((fun x : ℝ => x^2) 0) := by
    simpa using cost_scaled_square_right_derivative ht0 ht1 hM
  have h := hc.scomp_hasDerivAt (h := fun x : ℝ => x^2) 0 hp
    (fun x : ℝ => (show x^2 ∈ Ici 0 from sq_nonneg x))
  convert h using 1
  · ext x
    simp only [Function.comp_apply, ← pow_mul]
  · simp

end
end ProjectionChannels.RevisionK182
