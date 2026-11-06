import BellOutput.RevisionBellLogIdentity
import Entropy.BellLimitCoefficients

open MeasureTheory Filter Finset
open scoped Topology BigOperators
noncomputable section
namespace RevisionBell
open ProjectionChannels

/-- The scalar root equation along a Hermitian eigenvalue direction. -/
def rootEquation (k : ℕ) (t : ℝ) (h : Fin k → ℝ) (ε w : ℝ) : ℝ :=
  1 + (k : ℝ) * ∑ i, bernoulliDual t ((1+ε*h i)*w/k)

/-- The logarithmic-potential expression along a root curve. -/
def rootLogExpression {k : ℕ} (t : ℝ) (h : Fin k → ℝ) (w : ℝ → ℝ) (ε : ℝ) : ℝ :=
  -Real.log (-w ε)-1-(k : ℝ)*∑ i, bernoulliPrimitive t ((1+ε*h i)*w ε/k)

/-- The explicit Bernoulli branch is smooth of every order on the real line. -/
theorem contDiff_bernoulliDual {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (q : WithTop ℕ∞) : ContDiff ℝ q (bernoulliDual t) := by
  have hpos (y : ℝ) : 0 < (y+2*t-1)^2+4*t*(1-t) := by
    have ht := sub_pos.mpr ht1
    positivity
  have hd : ContDiff ℝ q (bernoulliDelta t) := by
    exact (show ContDiff ℝ q (fun y : ℝ => (y+2*t-1)^2+4*t*(1-t)) by fun_prop).sqrt
      (fun y => (hpos y).ne')
  unfold bernoulliDual
  exact ((contDiff_id.sub contDiff_const).add hd).div_const 2

/-- Off zero, differentiating the genuine Bernoulli R-transform gives the
quotient-rule expression used in the Hessian computation. -/
theorem hasDerivAt_bernoulliR_ne_zero {t y : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hy : y ≠ 0) :
    HasDerivAt (bernoulliR t)
      ((bernoulliMaximizer t y*y-bernoulliDual t y)/y^2) y := by
  have h := (hasDerivAt_bernoulliDual ht0 ht1 y).div (hasDerivAt_id y) hy
  have heq : bernoulliR t =ᶠ[𝓝 y] (fun x => bernoulliDual t x/x) := by
    filter_upwards [eventually_ne_nhds hy] with x hx
    simp [bernoulliR, hx]
  simpa only [mul_one] using h.congr_of_eventuallyEq heq

/-- At a root, all terms containing the root derivative cancel. -/
theorem hasDerivAt_rootLogExpression {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : Fin k → ℝ) (w : ℝ → ℝ)
    (ε d : ℝ) (hw : HasDerivAt w d ε) (hw0 : w ε ≠ 0)
    (hroot : rootEquation k t h ε (w ε) = 0) :
    HasDerivAt (rootLogExpression t h w)
      (-w ε * ∑ i, h i * bernoulliR t ((1+ε*h i)*w ε/k)) ε := by
  have hlog := (Real.hasDerivAt_log (neg_ne_zero.mpr hw0)).comp ε hw.neg
  have hargs (i : Fin k) : HasDerivAt (fun x => (1+x*h i)*w x/k)
      ((h i*w ε+(1+ε*h i)*d)/k) ε := by
    convert ((((hasDerivAt_id ε).mul_const (h i)).const_add 1).mul hw).div_const (k : ℝ) using 1 <;> dsimp <;> ring
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_bernoulliPrimitive ht0 ht1 _).comp ε (hargs i))
  have hder := (hlog.neg.sub_const 1).sub (hsum.const_mul (k : ℝ))
  convert hder using 1
  dsimp
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hRsum : w ε * (∑ i, (1+ε*h i)*bernoulliR t ((1+ε*h i)*w ε/k)) = -1 := by
    have heach (i : Fin k) :
        w ε*((1+ε*h i)*bernoulliR t ((1+ε*h i)*w ε/k)) =
          (k : ℝ)*bernoulliDual t ((1+ε*h i)*w ε/k) := by
      have hr := bernoulliR_mul t ((1+ε*h i)*w ε/k)
      calc
        _ = (k : ℝ) * (((1+ε*h i)*w ε/k) * bernoulliR t ((1+ε*h i)*w ε/k)) := by
          field_simp
          <;> ring
        _ = _ := congrArg (fun v : ℝ => (k : ℝ)*v) hr
    rw [mul_sum]
    simp_rw [heach]
    rw [← mul_sum]
    unfold rootEquation at hroot
    linarith
  have hsplit : (k : ℝ) * (∑ i, bernoulliR t ((1+ε*h i)*w ε/k) *
      ((h i*w ε+(1+ε*h i)*d)/k)) =
      w ε*(∑ i, h i*bernoulliR t ((1+ε*h i)*w ε/k)) +
        d*(∑ i, (1+ε*h i)*bernoulliR t ((1+ε*h i)*w ε/k)) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    field_simp
    <;> ring
  rw [hsplit]
  field_simp [hw0]
  have hm := congrArg (fun x : ℝ => d*x) hRsum
  dsimp at hm
  nlinarith only [hm]

/-- The implicit root has zero first variation in a traceless direction. -/
theorem root_derivative_zero {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : Fin k → ℝ) (hs : ∑ i, h i = 0)
    (w : ℝ → ℝ) (d : ℝ) (hwd : HasDerivAt w d 0)
    (hroot : ∀ᶠ ε in 𝓝 (0 : ℝ), rootEquation k t h ε (w ε) = 0) : d = 0 := by
  have hargs (i : Fin k) : HasDerivAt (fun x => (1+x*h i)*w x/k)
      ((h i*w 0+d)/k) 0 := by
    convert ((((hasDerivAt_id' (0 : ℝ)).mul_const (h i)).const_add 1).mul hwd).div_const (k : ℝ) using 1 <;> simp <;> ring
  have hterms (i : Fin k) : HasDerivAt
      (fun x => bernoulliDual t ((1+x*h i)*w x/k))
      (bernoulliMaximizer t (w 0/k)*((h i*w 0+d)/k)) (0 : ℝ) := by
    simpa only [zero_mul, add_zero, one_mul, Function.comp_def] using
      (hasDerivAt_bernoulliDual ht0 ht1 ((1+(0:ℝ)*h i)*w 0/k)).comp (0 : ℝ) (hargs i)
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => hterms i)
  have hD := (hsum.const_mul (k : ℝ)).const_add 1
  have heq : (fun x : ℝ => (0 : ℝ)) =ᶠ[𝓝 0]
      (fun ε => 1+(k : ℝ)*∑ i, bernoulliDual t ((1+ε*h i)*w ε/k)) := by
    filter_upwards [hroot] with ε hε
    exact hε.symm
  have hz := (hD.congr_of_eventuallyEq heq).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsumid : (k : ℝ) * ∑ i, bernoulliMaximizer t (w 0/k)*((h i*w 0+d)/k) =
      (k : ℝ)*bernoulliMaximizer t (w 0/k)*d := by
    rw [mul_sum]
    have heach (i : Fin k) : (k : ℝ)*(bernoulliMaximizer t (w 0/k)*((h i*w 0+d)/k)) =
        bernoulliMaximizer t (w 0/k)*w 0*h i + bernoulliMaximizer t (w 0/k)*d := by
      field_simp
      <;> ring
    simp_rw [heach]
    rw [sum_add_distrib, ← mul_sum, hs]
    simp
    <;> ring
  rw [hsumid] at hz
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hk0
    (bernoulliMaximizer_mem_Ioo ht0 ht1 (w 0/k)).1.ne')

/-- The traceless Hessian of the root expression, before evaluating its scalar
Bernoulli derivative at the symmetric root. -/
theorem hasDerivAt_deriv_rootLogExpression {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : Fin k → ℝ) (hs : ∑ i, h i = 0)
    (w : ℝ → ℝ) (hw : ContDiffAt ℝ 2 w 0) (hw0 : w 0 ≠ 0)
    (hroot : ∀ᶠ ε in 𝓝 (0 : ℝ), rootEquation k t h ε (w ε) = 0) :
    HasDerivAt (deriv (rootLogExpression t h w))
      (-(w 0)^2/(k : ℝ) *
        ((bernoulliMaximizer t (w 0/k)*(w 0/k)-bernoulliDual t (w 0/k))/(w 0/k)^2) *
          ∑ i, (h i)^2) 0 := by
  have hwd := (hw.differentiableAt (by norm_num)).hasDerivAt
  have hd0 := root_derivative_zero hk ht0 ht1 h hs w _ hwd hroot
  rw [hd0] at hwd
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  let R' := (bernoulliMaximizer t (w 0/k)*(w 0/k)-bernoulliDual t (w 0/k))/(w 0/k)^2
  have hargs (i : Fin k) : HasDerivAt (fun x => (1+x*h i)*w x/k) (h i*w 0/k) 0 := by
    convert ((((hasDerivAt_id' (0 : ℝ)).mul_const (h i)).const_add 1).mul hwd).div_const (k : ℝ) using 1 <;> simp <;> ring
  have hterms (i : Fin k) : HasDerivAt
      (fun ε => h i*bernoulliR t ((1+ε*h i)*w ε/k))
      (h i*(R'*(h i*w 0/k))) 0 := by
    have hb := hasDerivAt_bernoulliR_ne_zero (y := (1+(0:ℝ)*h i)*w 0/k) ht0 ht1
      (by simpa using div_ne_zero hw0 hk0)
    simpa only [zero_mul, add_zero, one_mul, Function.comp_def, R'] using
      (hb.comp (0 : ℝ) (hargs i)).const_mul (h i)
  have hD := hwd.neg.mul (HasDerivAt.sum (u := Finset.univ) (fun i _ => hterms i))
  have hval : -w 0*(∑ i, h i*(R'*(h i*w 0/k))) =
      -(w 0)^2/(k : ℝ)*R'*(∑ i, (h i)^2) := by
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hD' : HasDerivAt (fun ε => -w ε*∑ i, h i*bernoulliR t ((1+ε*h i)*w ε/k))
      (-(w 0)^2/(k : ℝ)*R'*(∑ i, (h i)^2)) 0 := by
    simpa only [neg_zero, zero_mul, zero_add, hval] using hD
  have heq : deriv (rootLogExpression t h w) =ᶠ[𝓝 0]
      (fun ε => -w ε*∑ i, h i*bernoulliR t ((1+ε*h i)*w ε/k)) := by
    filter_upwards [hw.eventually (by norm_num), hroot,
      hw.continuousAt.eventually_ne hw0] with ε hε hrootε hneε
    exact (hasDerivAt_rootLogExpression hk ht0 ht1 h w ε _
      (hε.differentiableAt (by norm_num)).hasDerivAt hneε hrootε).deriv
  exact hD'.congr_of_eventuallyEq heq

/-- An algebraic identity for the derivative of the explicit Bernoulli branch. -/
theorem bernoulliMaximizer_quadratic_derivative {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    bernoulliMaximizer t y*(2*bernoulliDual t y+1-y) = bernoulliDual t y+t := by
  have hd := (bernoulliDelta_pos ht0 ht1 y).ne'
  unfold bernoulliMaximizer bernoulliDual
  field_simp
  <;> ring

/-- Evaluate the Hessian coefficient at the symmetric negative root. -/
theorem root_hessian_coefficient {k t y : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < k^2*t)
    (hroot : bernoulliDual t y = -1/k^2) :
    -k*(bernoulliMaximizer t y*y-bernoulliDual t y) =
      BellLimitVerification.hessianC1 k t := by
  have hk0 : k ≠ 0 := hk.ne'
  have hkt0 : k^2*t-1 ≠ 0 := (sub_pos.mpr hkt).ne'
  have hd := (BellLimitVerification.denominator_pos (k := k) ht0 ht1).ne'
  have hq := bernoulliDual_quadratic ht0.le ht1.le y
  rw [hroot] at hq
  have hy : y = -(k^2-1)/(k^2*(k^2*t-1)) := by
    apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ hk0) hkt0)).2
    have hq' : 1+(y-1)*k^2-t*y*k^4 = 0 := by
      calc
        _ = k^4*((-1/k^2)^2+(1-y)*(-1/k^2)-t*y) := by field_simp <;> ring
        _ = 0 := by rw [hq]; ring
    nlinarith only [hq']
  have hδ : 2*bernoulliDual t y+1-y =
      BellLimitVerification.denominator k t/(k^2*(k^2*t-1)) := by
    rw [hroot, hy]
    unfold BellLimitVerification.denominator
    field_simp
    <;> ring
  have hu := bernoulliMaximizer_quadratic_derivative ht0 ht1 y
  rw [hδ, hroot] at hu
  have huval : bernoulliMaximizer t y =
      (k^2*t-1)^2/BellLimitVerification.denominator k t := by
    field_simp at hu ⊢
    apply mul_right_cancel₀ (pow_ne_zero 2 hk0)
    nlinarith only [hu]
  rw [huval, hroot, hy]
  unfold BellLimitVerification.hessianC1
  field_simp
  unfold BellLimitVerification.denominator
  ring

/-- The coefficient in Lemma A.2 for every C² root curve. The implicit-function
construction supplies such a curve separately; no Hessian value is assumed. -/
theorem rootLogExpression_traceless_hessian {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t)
    (h : Fin k → ℝ) (hs : ∑ i, h i = 0)
    (w : ℝ → ℝ) (hw : ContDiffAt ℝ 2 w 0) (hw0 : w 0 ≠ 0)
    (hroot : ∀ᶠ ε in 𝓝 (0 : ℝ), rootEquation k t h ε (w ε) = 0) :
    HasDerivAt (deriv (rootLogExpression t h w))
      (BellLimitVerification.hessianC1 k t * ∑ i, (h i)^2) 0 := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk0 := hkR.ne'
  have hroot0 : rootEquation k t h 0 (w 0) = 0 := hroot.self_of_nhds
  have hg : bernoulliDual t (w 0/k) = -1/(k : ℝ)^2 := by
    simp only [rootEquation, zero_mul, add_zero, one_mul, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hroot0
    apply (eq_div_iff (pow_ne_zero _ hk0)).2
    nlinarith only [hroot0]
  have hcoeff := root_hessian_coefficient hkR ht0 ht1 hkt hg
  have hmul : -(w 0)^2/(k : ℝ)*
      ((bernoulliMaximizer t (w 0/k)*(w 0/k)-bernoulliDual t (w 0/k))/(w 0/k)^2) =
      -(k : ℝ)*(bernoulliMaximizer t (w 0/k)*(w 0/k)-bernoulliDual t (w 0/k)) := by
    field_simp
    <;> ring
  have hd := hasDerivAt_deriv_rootLogExpression hk ht0 ht1 h hs w hw hw0 hroot
  rwa [hmul, hcoeff] at hd

/-- The root derivative in an arbitrary direction, including its scalar part. -/
theorem root_derivative {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : Fin k → ℝ)
    (w : ℝ → ℝ) (d : ℝ) (hwd : HasDerivAt w d 0)
    (hroot : ∀ᶠ ε in 𝓝 (0 : ℝ), rootEquation k t h ε (w ε) = 0) :
    d = -w 0*(∑ i, h i)/(k : ℝ) := by
  have hargs (i : Fin k) : HasDerivAt (fun x => (1+x*h i)*w x/k)
      ((h i*w 0+d)/k) 0 := by
    convert ((((hasDerivAt_id' (0 : ℝ)).mul_const (h i)).const_add 1).mul hwd).div_const (k : ℝ) using 1 <;> simp <;> ring
  have hterms (i : Fin k) : HasDerivAt
      (fun x => bernoulliDual t ((1+x*h i)*w x/k))
      (bernoulliMaximizer t (w 0/k)*((h i*w 0+d)/k)) (0 : ℝ) := by
    simpa only [zero_mul, add_zero, one_mul, Function.comp_def] using
      (hasDerivAt_bernoulliDual ht0 ht1 ((1+(0:ℝ)*h i)*w 0/k)).comp (0 : ℝ) (hargs i)
  have hD := ((HasDerivAt.sum (u := Finset.univ) (fun i _ => hterms i)).const_mul
    (k : ℝ)).const_add 1
  have heq : (fun x : ℝ => (0 : ℝ)) =ᶠ[𝓝 0]
      (fun ε => 1+(k : ℝ)*∑ i, bernoulliDual t ((1+ε*h i)*w ε/k)) := by
    filter_upwards [hroot] with ε hε
    exact hε.symm
  have hz := (hD.congr_of_eventuallyEq heq).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsumid : (k : ℝ) * ∑ i, bernoulliMaximizer t (w 0/k)*((h i*w 0+d)/k) =
      bernoulliMaximizer t (w 0/k)*(w 0*(∑ i, h i)+(k : ℝ)*d) := by
    rw [mul_sum]
    have heach (i : Fin k) : (k : ℝ)*(bernoulliMaximizer t (w 0/k)*((h i*w 0+d)/k)) =
        bernoulliMaximizer t (w 0/k)*w 0*h i + bernoulliMaximizer t (w 0/k)*d := by
      field_simp
      <;> ring
    simp_rw [heach]
    rw [sum_add_distrib, ← mul_sum]
    simp
    <;> ring
  rw [hsumid] at hz
  have hh := (mul_eq_zero.mp hz).resolve_left
    (bernoulliMaximizer_mem_Ioo ht0 ht1 (w 0/k)).1.ne'
  apply (eq_div_iff hk0).2
  linarith

/-- Full scalar form of Lemma A.2: the Hessian of the logarithmic root
expression, with both trace and traceless contributions. -/
theorem rootLogExpression_hessian {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t)
    (h : Fin k → ℝ) (w : ℝ → ℝ) (hw : ContDiffAt ℝ 2 w 0) (hw0 : w 0 ≠ 0)
    (hroot : ∀ᶠ ε in 𝓝 (0 : ℝ), rootEquation k t h ε (w ε) = 0) :
    HasDerivAt (deriv (rootLogExpression t h w))
      (BellLimitVerification.hessianC0 k t * (∑ i, h i)^2 +
        BellLimitVerification.hessianC1 k t * ∑ i, (h i)^2) 0 := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk0 := hkR.ne'
  let d := -w 0*(∑ i, h i)/(k : ℝ)
  have hwd : HasDerivAt w d 0 := by
    have hd := (hw.differentiableAt (by norm_num)).hasDerivAt
    rw [root_derivative hk ht0 ht1 h w _ hd hroot] at hd
    exact hd
  let R' := (bernoulliMaximizer t (w 0/k)*(w 0/k)-bernoulliDual t (w 0/k))/(w 0/k)^2
  have hargs (i : Fin k) : HasDerivAt (fun x => (1+x*h i)*w x/k) ((h i*w 0+d)/k) 0 := by
    convert ((((hasDerivAt_id' (0 : ℝ)).mul_const (h i)).const_add 1).mul hwd).div_const (k : ℝ) using 1 <;> simp <;> ring
  have hterms (i : Fin k) : HasDerivAt
      (fun ε => h i*bernoulliR t ((1+ε*h i)*w ε/k))
      (h i*(R'*((h i*w 0+d)/k))) 0 := by
    have hb := hasDerivAt_bernoulliR_ne_zero (y := (1+(0:ℝ)*h i)*w 0/k) ht0 ht1
      (by simpa using div_ne_zero hw0 hk0)
    simpa only [zero_mul, add_zero, one_mul, Function.comp_def, R'] using
      (hb.comp (0 : ℝ) (hargs i)).const_mul (h i)
  have hD := hwd.neg.mul (HasDerivAt.sum (u := Finset.univ) (fun i _ => hterms i))
  have hroot0 : rootEquation k t h 0 (w 0) = 0 := hroot.self_of_nhds
  have hg : bernoulliDual t (w 0/k) = -1/(k : ℝ)^2 := by
    simp only [rootEquation, zero_mul, add_zero, one_mul, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hroot0
    apply (eq_div_iff (pow_ne_zero _ hk0)).2
    nlinarith only [hroot0]
  have hcoef : -(w 0)^2/(k : ℝ)*R' = BellLimitVerification.hessianC1 k t := by
    have hh := root_hessian_coefficient hkR ht0 ht1 hkt hg
    convert hh using 1
    dsimp [R']
    field_simp
    <;> ring
  have hR : w 0*bernoulliR t (w 0/k) = -1/(k : ℝ) := by
    have hh := bernoulliR_mul t (w 0/k)
    rw [hg] at hh
    calc
      _ = (k : ℝ)*((w 0/k)*bernoulliR t (w 0/k)) := by field_simp <;> ring
      _ = (k : ℝ)*(-1/(k : ℝ)^2) := congrArg (fun v : ℝ => (k : ℝ)*v) hh
      _ = _ := by field_simp <;> ring
  have hsumid : (∑ i, h i*(R'*((h i*w 0+d)/k))) =
      w 0*R'/(k : ℝ)*(∑ i, (h i)^2) + d*R'/(k : ℝ)*(∑ i, h i) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hsum0 : (∑ i, h i*bernoulliR t (w 0/k)) =
      bernoulliR t (w 0/k)*(∑ i, h i) := by rw [mul_sum]; apply sum_congr rfl; intro i _; ring
  have hvalue : -d*(∑ i, h i*bernoulliR t ((1+(0:ℝ)*h i)*w 0/k)) +
      -w 0*(∑ i, h i*(R'*((h i*w 0+d)/k))) =
      BellLimitVerification.hessianC0 k t * (∑ i, h i)^2 +
        BellLimitVerification.hessianC1 k t * ∑ i, (h i)^2 := by
    simp only [zero_mul, add_zero, one_mul]
    rw [hsumid, hsum0]
    calc
      _ = (w 0*bernoulliR t (w 0/k)/(k : ℝ)+(w 0)^2*R'/(k : ℝ)^2)*(∑ i, h i)^2 +
          (-(w 0)^2/(k : ℝ)*R')*(∑ i, (h i)^2) := by dsimp [d]; ring
      _ = _ := by
        rw [hR, hcoef]
        have hcoeff2 : (w 0)^2*R'/(k : ℝ)^2 = -BellLimitVerification.hessianC1 k t/(k : ℝ) := by
          rw [← hcoef]
          ring
        rw [hcoeff2]
        unfold BellLimitVerification.hessianC0
        congr 1
        field_simp
        <;> ring
  rw [hvalue] at hD
  have heq : deriv (rootLogExpression t h w) =ᶠ[𝓝 0]
      (fun ε => -w ε*∑ i, h i*bernoulliR t ((1+ε*h i)*w ε/k)) := by
    filter_upwards [hw.eventually (by norm_num), hroot,
      hw.continuousAt.eventually_ne hw0] with ε hε hrootε hneε
    exact (hasDerivAt_rootLogExpression hk ht0 ht1 h w ε _
      (hε.differentiableAt (by norm_num)).hasDerivAt hneε hrootε).deriv
  exact hD.congr_of_eventuallyEq heq

end RevisionBell



