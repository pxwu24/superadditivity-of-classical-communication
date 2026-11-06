import Dimension182.RevisionK182BirthCurve
import Dimension182.RevisionK182Descent
import Dimension182.RevisionK182Curve

/-! The equal-positive-coordinate case of the boundary exclusion in C.1.
The new zero coordinate has mass M ε⁴. Both the actual cost and entropy
have strictly negative second derivatives along the explicit curve.
-/
open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasDerivAt_sum_birthCurve_at (f : ℝ → ℝ) (u : ι → ℝ) {i j z : ι}
    (hij : i≠j) (hiz : i≠z) (hjz : j≠z) (hz : u z=0)
    (M x : ℝ) (r : ℕ) {fi fj fz : ℝ}
    (hi : HasDerivAt f fi (u i-x)) (hj : HasDerivAt f fj (u j+x))
    (hborn : HasDerivAt (fun x : ℝ => f (M*x^r)) fz x) :
    HasDerivAt (fun x => ∑ l, f (birthCurve u i j z M r x l)) (-fi+fj+fz) x := by
  have hei := hi.comp x ((hasDerivAt_id x).const_sub (u i))
  have hej := hj.comp x ((hasDerivAt_id x).const_add (u j))
  have hh := (((hei.sub_const (f (u i))).const_add (∑ l, f (u l))).add
    (hej.sub_const (f (u j)))).add (hborn.sub_const (f 0))
  convert hh using 1
  · funext y
    exact sum_birthCurve f u hij hiz hjz hz M y r
  · simp only [neg_mul,one_mul,mul_neg_one,mul_one]

theorem no_zero_with_equal_positive {t q : ℝ} {u : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hu : ∀ l, u l ∈ Icc 0 1)
    (hs : 0 < mass u) (hq : costSum t u ≤ q)
    {i j z : ι} (hij : i≠j) (hi : 0 < u i) (hijval : u i = u j)
    (hj : u j < 1) (hz : u z=0)
    (hmin : IsLocalMinOn normalizedEntropy
      {v | (∀ l, v l ∈ Icc 0 1) ∧ costSum t v ≤ q} u) : False := by
  have hiz : i≠z := by intro h; simpa [h,hz] using hi
  have hjz : j≠z := by intro h; have hh : 0<u j := hijval ▸ hi; simpa [h,hz] using hh
  have hi1 : u i < 1 := hijval.trans_lt hj
  let a := u i
  let c := Real.sqrt (t*(1-t))
  have hc : 0 < c := Real.sqrt_pos.mpr (mul_pos ht0 (sub_pos.mpr ht1))
  let R := (|costCurvature t a|+1)/(2*c)
  have hR : 0 < R := by dsimp [R]; positivity
  let M := R^2
  have hM : 0 < M := sq_pos_of_pos hR
  have hsqrt : Real.sqrt M = R := Real.sqrt_sq hR.le
  let g := birthCurve u i j z M 4
  have hg0 : g 0 = u := birthCurve_zero u i j z M 4 (by norm_num) hz
  let bornL : ℝ → ℝ := fun x => M*x^4*Real.log (M*x^4)
  let bornC : ℝ → ℝ := fun x => bernoulliCost t (M*x^4)
  let lp : ℝ → ℝ := fun x => Real.log (a+x)-Real.log (a-x)+deriv bornL x
  let cp : ℝ → ℝ := fun x => deriv (bernoulliCost t) (a+x) -
    deriv (bernoulliCost t) (a-x)+deriv bornC x
  let mp : ℝ → ℝ := fun x => 4*M*x^3
  have hmp (x : ℝ) : HasDerivAt (fun y => mass (g y)) (mp x) x := by
    have hh := (((hasDerivAt_id x).pow 4).const_mul M).const_add (mass u)
    convert hh using 1
    · funext y
      exact mass_birthCurve u hij hiz hjz hz M y 4
    · simp [mp]; ring
  have hmp0 : mp 0 = 0 := by simp [mp]
  have hmp2 : HasDerivAt mp 0 0 := by
    convert ((hasDerivAt_id (0:ℝ)).pow 3).const_mul (4*M) using 1 <;> norm_num [mp]
  have hmass0 : mass (g 0) ≠ 0 := by simpa [hg0] using hs.ne'
  have hL0 : deriv bornL 0 = 0 := by
    simpa [bornL] using (quartic_log_derivative M hM 0).deriv
  have hC0 : deriv bornC 0 = 0 := (cost_scaled_quartic_derivative_zero ht0 ht1 hM).deriv
  have hlp0 : lp 0 = 0 := by simp [lp,hL0]
  have hcp0 : cp 0 = 0 := by simp [cp,hC0]
  have hlp2 : HasDerivAt lp (2/a) 0 := by
    have hp := (Real.hasDerivAt_log (show a ≠ 0 from hi.ne')).comp_of_eq 0
      ((hasDerivAt_id (0:ℝ)).const_add a) (by simp)
    have hn := (Real.hasDerivAt_log (show a ≠ 0 from hi.ne')).comp_of_eq 0
      ((hasDerivAt_id (0:ℝ)).const_sub a) (by simp)
    convert (hp.sub hn).add (quartic_log_second_derivative_zero M hM) using 1 <;>
      dsimp only [lp,bornL,Function.comp_apply] <;> ring
  have hcp2 : HasDerivAt cp (2*costCurvature t a-4*c*Real.sqrt M) 0 := by
    have hc2 := hasDerivAt_deriv_bernoulliCost ht0.le ht1.le hi hi1
    have hp := hc2.comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).const_add a) (by simp [a])
    have hn := hc2.comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).const_sub a) (by simp [a])
    convert (hp.sub hn).add (cost_scaled_quartic_second_derivative ht0 ht1 hM) using 1 <;>
      simp only [cp,bornC,Function.comp_apply,costCurvature,c,a] <;> ring
  have hnear : ∀ᶠ x in 𝓝 (0:ℝ), (a-x ∈ Ioo 0 1) ∧ (a+x ∈ Ioo 0 1) ∧ M*x^4<1 := by
    have hm := (show ContinuousAt (fun x:ℝ => a-x) 0 by fun_prop).eventually
      (by simpa [a] using Ioo_mem_nhds hi hi1)
    have hp := (show ContinuousAt (fun x:ℝ => a+x) 0 by fun_prop).eventually
      (by simpa [a] using Ioo_mem_nhds hi hi1)
    have hb := (show ContinuousAt (fun x:ℝ => M*x^4) 0 by fun_prop).eventually
      (Iio_mem_nhds (by norm_num : M*(0:ℝ)^4<1))
    exact hm.and (hp.and hb)
  have hlog : ∀ᶠ x in 𝓝 (0:ℝ), HasDerivAt (fun y => logMoment (g y)) (lp x) x := by
    filter_upwards [hnear] with x hx
    have hborn := (quartic_log_derivative M hM x)
    have hborn' : HasDerivAt bornL (deriv bornL x) x := hborn.differentiableAt.hasDerivAt
    have hh := hasDerivAt_sum_birthCurve_at (fun v => v*Real.log v) u hij hiz hjz hz M x 4
      (Real.hasDerivAt_mul_log (ne_of_gt hx.1.1))
      (by simpa only [← hijval] using Real.hasDerivAt_mul_log (ne_of_gt hx.2.1.1)) hborn'
    convert hh using 1 <;> dsimp [lp,logMoment,g,a] <;> try rw [← hijval]
    all_goals ring
  have hcost : ∀ᶠ x in 𝓝 (0:ℝ), HasDerivAt (fun y => costSum t (g y)) (cp x) x := by
    filter_upwards [hnear] with x hx
    have hborn : DifferentiableAt ℝ bornC x := by
      by_cases hzero : x=0
      · subst x; exact (cost_scaled_quartic_derivative_zero ht0 ht1 hM).differentiableAt
      · have hp : 0<x^4 := by nlinarith only [sq_pos_of_ne_zero (pow_ne_zero 2 hzero)]
        have hpos : 0<M*x^4 := mul_pos hM hp
        change DifferentiableAt ℝ ((bernoulliCost t) ∘ (fun y : ℝ => M*y^4)) x
        exact (hasStrictDerivAt_cost ht0 ht1 hpos hx.2.2).hasDerivAt.differentiableAt.comp x
          (show DifferentiableAt ℝ (fun y : ℝ => M*y^4) x by fun_prop)
    have hh := hasDerivAt_sum_birthCurve_at (bernoulliCost t) u hij hiz hjz hz M x 4
      (hasStrictDerivAt_cost ht0 ht1 hx.1.1 hx.1.2).hasDerivAt
      (by simpa only [← hijval] using (hasStrictDerivAt_cost ht0 ht1 hx.2.1.1 hx.2.1.2).hasDerivAt)
      hborn.hasDerivAt
    convert hh using 1 <;> dsimp [cp,costSum,g,a] <;> try rw [← hijval]
    all_goals ring
  have hlog0 : HasDerivAt (fun y => logMoment (g y)) 0 0 := by
    simpa only [hlp0] using hlog.self_of_nhds
  let fp : ℝ → ℝ := fun x => mp x / mass (g x) - lp x / mass (g x) +
    logMoment (g x) * mp x / (mass (g x))^2
  have hfp0 : fp 0=0 := by simp [fp,hmp0,hlp0]
  have hfp2 : HasDerivAt fp (-(2/a)/mass u) 0 := by
    have hm0 : HasDerivAt (fun y => mass (g y)) 0 0 := by simpa [hmp0] using hmp 0
    have h := ((hmp2.div hm0 hmass0).sub (hlp2.div hm0 hmass0)).add
      ((hlog0.mul hmp2).div (hm0.pow 2) (pow_ne_zero _ hmass0))
    convert h using 1 <;> simp only [fp,hg0,hmp0,hlp0,mul_zero,zero_mul,
      sub_zero,zero_sub,add_zero,zero_div,zero_add] <;> field_simp <;> ring
  have hentropy : ∀ᶠ x in 𝓝 (0:ℝ), HasDerivAt (fun y => normalizedEntropy (g y)) (fp x) x := by
    have hmassnear : ∀ᶠ x in 𝓝 (0:ℝ), mass (g x) ≠ 0 := (hmp 0).continuousAt.eventually_ne hmass0
    filter_upwards [hlog,hmassnear] with x hx hmx
    have hh := ((hmp x).log hmx).sub (hx.div (hmp x) hmx)
    convert hh using 1
    dsimp [fp]
    field_simp
    ring
  have hFneg : -(2/a)/mass u < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos (by norm_num) hi)) hs
  have hCneg : 2*costCurvature t a-4*c*Real.sqrt M < 0 := by
    rw [hsqrt]
    have hr : 2*c*R=|costCurvature t a|+1 := by dsimp [R]; field_simp
    nlinarith only [hr,le_abs_self (costCurvature t a)]
  have hbox := birthCurve_in_box_eventually u hu ⟨hi,hi1⟩
    ⟨hijval ▸ hi,hj⟩ M hM 4 (by norm_num) (z:=z)
  have hn := not_sublevel_localMin_of_right_descent
    (g:=g) (B:={v : ι → ℝ | ∀ l, v l ∈ Icc (0:ℝ) 1}) (budget:=q)
    (continuous_birthCurve u i j z M 4).continuousAt hbox
    (by simpa only [hg0] using hq)
    (strict_descent_right_of_second_derivative_neg hentropy hfp0 hfp2 hFneg)
    (strict_descent_right_of_second_derivative_neg hcost hcp0 hcp2 hCneg)
  exact hn (by simpa only [hg0] using hmin)

end ProjectionChannels.RevisionK182
