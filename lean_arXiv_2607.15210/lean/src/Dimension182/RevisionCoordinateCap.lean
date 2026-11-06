import Preliminaries.PreliminariesLegendre

/-! The exact coordinate bound for a Bernoulli-cost sublevel set.
The proof uses the supporting line to the unit circle after an orthogonal
change of coordinates; no minimizer-shape assumption is used. -/

namespace ProjectionChannels
noncomputable section

private theorem unit_circle_coordinate_bound
    (A B C D x y : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 < C) (hD : 0 ≤ D)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hAB : A^2+B^2=1) (hCD : C^2+D^2=1) (hxy : x^2+y^2=1)
    (hrot : A*D ≤ B*C) (hcost : (B*x-A*y)^2 ≤ D^2) :
    x ≤ A*C+B*D := by
  let c := A*x+B*y
  let d := B*x-A*y
  have hcd : c^2+d^2=1 := by
    dsimp [c,d]
    nlinarith [congrArg (fun z : ℝ => z*(A^2+B^2)) hxy]
  have hxrot : x=A*c+B*d := by
    dsimp [c,d]
    nlinarith [congrArg (fun z : ℝ => z*x) hAB]
  have hd : d ≤ D := by
    dsimp [d]
    nlinarith
  have hsupport : c*C+d*D ≤ 1 := by
    nlinarith [sq_nonneg (c-C),sq_nonneg (d-D)]
  have hcoef : 0 ≤ B*C-A*D := sub_nonneg.mpr hrot
  have hmul := mul_le_mul_of_nonneg_left hd hcoef
  have hsupp := mul_le_mul_of_nonneg_left hsupport hA
  have hCx : C*x ≤ C*(A*C+B*D) := by
    nlinarith [congrArg (fun z : ℝ => z*A) hCD, congrArg (fun z : ℝ => C*z) hxrot]
  nlinarith

/-- The sharp scalar coordinate cap from Appendix C.1. -/
theorem bernoulliCost_coordinate_cap {t q u : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (htq : t+q < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hcost : bernoulliCost t u ≤ q) :
    u ≤ (Real.sqrt (t*(1-q))+Real.sqrt ((1-t)*q))^2 := by
  let A := Real.sqrt t
  let B := Real.sqrt (1-t)
  let C := Real.sqrt (1-q)
  let D := Real.sqrt q
  let x := Real.sqrt u
  let y := Real.sqrt (1-u)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hC : 0 < C := Real.sqrt_pos.mpr (sub_pos.mpr hq1)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hAsq : A^2=t := Real.sq_sqrt ht0.le
  have hBsq : B^2=1-t := Real.sq_sqrt (sub_nonneg.mpr ht1.le)
  have hCsq : C^2=1-q := Real.sq_sqrt (sub_nonneg.mpr hq1.le)
  have hDsq : D^2=q := Real.sq_sqrt hq0.le
  have hxsq : x^2=u := Real.sq_sqrt hu0
  have hysq : y^2=1-u := Real.sq_sqrt (sub_nonneg.mpr hu1)
  have hrot : A*D ≤ B*C := by
    have h1 : (A*D)^2=t*q := by rw [mul_pow,hAsq,hDsq]
    have h2 : (B*C)^2=(1-t)*(1-q) := by rw [mul_pow,hBsq,hCsq]
    nlinarith [mul_nonneg hA hD,mul_nonneg hB hC.le]
  have hcost' : (B*x-A*y)^2 ≤ D^2 := by
    have hid : bernoulliCost t u = (B*x-A*y)^2 := by
      rw [bernoulliCost, Real.sqrt_mul ht0.le,
        Real.sqrt_mul (sub_nonneg.mpr ht1.le)]
      dsimp [A,B,x,y]
      ring
    rw [← hid,hDsq]
    exact hcost
  have hcap := unit_circle_coordinate_bound A B C D x y hA hB hC hD hx hy
    (by linarith) (by linarith) (by linarith) hrot hcost'
  have hnonneg : 0 ≤ A*C+B*D := by positivity
  have hsq : x^2 ≤ (A*C+B*D)^2 := by nlinarith
  rw [hxsq] at hsq
  simpa only [A,B,C,D,Real.sqrt_mul ht0.le,
    Real.sqrt_mul (sub_nonneg.mpr ht1.le)] using hsq

end
end ProjectionChannels
