import Dimension182.RevisionK182BirthCurve
import Dimension182.RevisionK182Descent

/-! Excluding zero coordinates at constrained entropy minima by explicit
birth-and-transfer perturbations. -/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem no_zero_with_distinct_positive {t q : ℝ} {u : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hu : ∀ l, u l ∈ Icc 0 1)
    (hs : 0 < mass u) (hq : costSum t u ≤ q)
    {i j z : ι} (hi : 0 < u i) (hijval : u i < u j) (hj : u j < 1) (hz : u z=0)
    (hmin : IsLocalMinOn normalizedEntropy
      {v | (∀ l, v l ∈ Icc 0 1) ∧ costSum t v ≤ q} u) : False := by
  have hij : i≠j := fun h => (ne_of_lt hijval) (congrArg u h)
  have hiz : i≠z := by intro h; simpa [h,hz] using hi
  have hjz : j≠z := by intro h; have := hi.trans hijval; simpa [h,hz] using this
  let A : ℝ := -deriv (bernoulliCost t) (u i) + deriv (bernoulliCost t) (u j)
  let c : ℝ := Real.sqrt (t*(1-t))
  have hc : 0 < c := Real.sqrt_pos.mpr (mul_pos ht0 (sub_pos.mpr ht1))
  let R : ℝ := (|A|+1)/(2*c)
  have hR : 0 < R := by dsimp [R]; positivity
  let M : ℝ := R^2
  have hM : 0 < M := sq_pos_of_pos hR
  have hsqrt : Real.sqrt M = R := Real.sqrt_sq hR.le
  let g := birthCurve u i j z M 2
  have hg0 : g 0 = u := birthCurve_zero u i j z M 2 (by norm_num) hz
  have hmass : HasDerivAt (fun x => mass (g x)) 0 0 := by
    have hh := (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul M).const_add (mass u)
    convert hh using 1
    · funext x
      exact mass_birthCurve u hij hiz hjz hz M x 2
    · norm_num
  have hlog : HasDerivAt (fun x => logMoment (g x))
      (Real.log (u j)-Real.log (u i)) 0 := by
    have hh := hasDerivAt_sum_birthCurve (fun v => v*Real.log v) u hij hiz hjz hz M 2
      (Real.hasDerivAt_mul_log (ne_of_gt hi))
      (Real.hasDerivAt_mul_log (ne_of_gt (hi.trans hijval)))
      (scaled_square_log_derivative_zero M hM)
    convert hh using 1 <;> ring
  have hmassne : mass (g 0) ≠ 0 := by simpa only [hg0] using ne_of_gt hs
  have hF : HasDerivAt (fun x => normalizedEntropy (g x))
      (-(Real.log (u j)-Real.log (u i))/mass u) 0 := by
    convert (hmass.log hmassne).sub (hlog.div hmass hmassne) using 1
    simp only [hg0,zero_div,mul_zero,sub_zero]
    field_simp
    ring
  have hFneg : -(Real.log (u j)-Real.log (u i))/mass u < 0 := by
    apply div_neg_of_neg_of_pos _ hs
    have hl := Real.log_lt_log hi hijval
    linarith only [hl]
  have hC : HasDerivWithinAt (fun x => costSum t (g x))
      (A-2*c*Real.sqrt M) (Ici 0) 0 := by
    have hh := hasDerivWithinAt_sum_birthCurve (bernoulliCost t) u hij hiz hjz hz M 2
      (hasStrictDerivAt_cost ht0 ht1 hi (hijval.trans hj)).hasDerivAt
      (hasStrictDerivAt_cost ht0 ht1 (hi.trans hijval) hj).hasDerivAt
      (cost_scaled_square_right_derivative ht0 ht1 hM)
    convert hh using 1 <;> dsimp [A,c] <;> ring
  have hCneg : A-2*c*Real.sqrt M < 0 := by
    rw [hsqrt]
    have heq : 2*c*R = |A|+1 := by dsimp [R]; field_simp
    rw [heq]
    linarith only [le_abs_self A]
  have hbox := birthCurve_in_box_eventually u hu ⟨hi,hijval.trans hj⟩
    ⟨hi.trans hijval,hj⟩ M hM 2 (by norm_num) (z:=z)
  have hn := not_sublevel_localMin_of_right_descent
    (g:=g) (B:={v : ι → ℝ | ∀ l, v l ∈ Icc (0:ℝ) 1}) (budget:=q)
    (continuous_birthCurve u i j z M 2).continuousAt hbox
    (by simpa only [hg0] using hq)
    (strict_descent_right_of_derivative_neg hF.hasDerivWithinAt hFneg)
    (strict_descent_right_of_derivative_neg hC hCneg)
  exact hn (by simpa only [hg0] using hmin)

#print axioms no_zero_with_distinct_positive
end ProjectionChannels.RevisionK182
