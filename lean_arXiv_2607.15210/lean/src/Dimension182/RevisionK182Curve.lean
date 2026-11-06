import Dimension182.RevisionK182Multiplier
import Dimension182.K182SecondVariation

/-!
Parabolic perturbations for the second-order argument in Appendix C.1.
The curve and its derivatives are concrete polynomial expressions.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def parabola (u d w : ι → ℝ) (x : ℝ) (i : ι) : ℝ :=
  u i + x * d i + x^2 * w i

def parabolaSlope (d w : ι → ℝ) (x : ℝ) (i : ι) : ℝ := d i + 2*x*w i

@[simp] theorem parabola_zero (u d w : ι → ℝ) : parabola u d w 0 = u := by
  ext i
  simp [parabola]

@[simp] theorem parabolaSlope_zero (d w : ι → ℝ) : parabolaSlope d w 0 = d := by
  ext i
  simp [parabolaSlope]

theorem hasDerivAt_parabola (u d w : ι → ℝ) (x : ℝ) (i : ι) :
    HasDerivAt (fun x => parabola u d w x i) (parabolaSlope d w x i) x := by
  convert (((hasDerivAt_id x).mul_const (d i)).const_add (u i)).add
    (((hasDerivAt_id x).pow 2).mul_const (w i)) using 1 <;>
    simp [parabola,parabolaSlope] <;> ring

theorem hasDerivAt_parabolaSlope (d w : ι → ℝ) (x : ℝ) (i : ι) :
    HasDerivAt (fun x => parabolaSlope d w x i) (2*w i) x := by
  convert (((hasDerivAt_id x).const_mul 2).mul_const (w i)).const_add (d i) using 1 <;>
    simp [parabolaSlope]

theorem continuous_parabola (u d w : ι → ℝ) : Continuous (parabola u d w) := by
  apply continuous_pi
  intro i
  exact continuous_iff_continuousAt.mpr fun x => (hasDerivAt_parabola u d w x i).continuousAt

def costCurvature (t v : ℝ) : ℝ :=
  Real.sqrt (t*(1-t)) / (2 * Real.sqrt (v*(1-v))^3)

def curveCostSlope (t : ℝ) (u d w : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, deriv (bernoulliCost t) (parabola u d w x i) * parabolaSlope d w x i

theorem hasDerivAt_curveCost (t : ℝ) (u d w : ι → ℝ) (x : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hx : ∀ i, parabola u d w x i ∈ Ioo 0 1) :
    HasDerivAt (fun x => costSum t (parabola u d w x))
      (curveCostSlope t u d w x) x := by
  unfold costSum curveCostSlope
  apply HasDerivAt.sum
  intro i _
  exact ((hasStrictDerivAt_cost ht0 ht1 (hx i).1 (hx i).2).hasDerivAt).comp x
    (hasDerivAt_parabola u d w x i)

theorem hasDerivAt_curveCostSlope_zero (t : ℝ) (u d w : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hu : ∀ i, u i ∈ Ioo 0 1) :
    HasDerivAt (curveCostSlope t u d w)
      (∑ i, (costCurvature t (u i) * (d i)^2 +
        deriv (bernoulliCost t) (u i) * (2*w i))) 0 := by
  unfold curveCostSlope
  apply HasDerivAt.sum
  intro i _
  have hcost := hasDerivAt_deriv_bernoulliCost ht0.le ht1.le (hu i).1 (hu i).2
  have hcost' : HasDerivAt (deriv (bernoulliCost t))
      (costCurvature t (u i)) (parabola u d w 0 i) := by simpa [costCurvature] using hcost
  have hi := (hcost'.comp 0 (hasDerivAt_parabola u d w 0 i)).mul
    (hasDerivAt_parabolaSlope d w 0 i)
  convert hi using 1 <;> simp only [Function.comp_apply,parabola_zero,parabolaSlope_zero,costCurvature] <;> ring

def curveLogSlope (u d w : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, parabolaSlope d w x i * Real.log (parabola u d w x i)

theorem hasDerivAt_curveLogSlope_zero (u d w : ι → ℝ) (hu : ∀ i, 0 < u i) :
    HasDerivAt (curveLogSlope u d w)
      (∑ i, ((2*w i) * Real.log (u i) + (d i)^2 / u i)) 0 := by
  unfold curveLogSlope
  apply HasDerivAt.sum
  intro i _
  have hi := (hasDerivAt_parabolaSlope d w 0 i).mul
    ((hasDerivAt_parabola u d w 0 i).log (by simpa using ne_of_gt (hu i)))
  convert hi using 1 <;> simp only [parabola_zero,parabolaSlope_zero] <;> ring

def curveEntropySlope (u d w : ι → ℝ) (x : ℝ) : ℝ :=
  -(curveLogSlope u d w x) / mass (parabola u d w x) +
    logMoment (parabola u d w x) / mass (parabola u d w x)^2 * mass (parabolaSlope d w x)

theorem hasDerivAt_curveMass (u d w : ι → ℝ) (x : ℝ) :
    HasDerivAt (fun x => mass (parabola u d w x)) (mass (parabolaSlope d w x)) x := by
  unfold mass
  exact HasDerivAt.sum fun i _ => hasDerivAt_parabola u d w x i

theorem hasDerivAt_curveMassSlope (d w : ι → ℝ) (x : ℝ) :
    HasDerivAt (fun x => mass (parabolaSlope d w x)) (2 * mass w) x := by
  unfold mass
  rw [Finset.mul_sum]
  exact HasDerivAt.sum fun i _ => hasDerivAt_parabolaSlope d w x i

theorem hasDerivAt_curveLogMoment (u d w : ι → ℝ) (x : ℝ)
    (hx : ∀ i, 0 < parabola u d w x i) :
    HasDerivAt (fun x => logMoment (parabola u d w x))
      (curveLogSlope u d w x + mass (parabolaSlope d w x)) x := by
  unfold logMoment curveLogSlope mass
  rw [← Finset.sum_add_distrib]
  apply HasDerivAt.sum
  intro i _
  have hi := hasDerivAt_parabola u d w x i
  convert hi.mul (hi.log (ne_of_gt (hx i))) using 1
  field_simp [ne_of_gt (hx i)]
  <;> ring

theorem hasDerivAt_curveEntropy (u d w : ι → ℝ) (x : ℝ)
    (hx : ∀ i, 0 < parabola u d w x i) (hs : mass (parabola u d w x) ≠ 0) :
    HasDerivAt (fun x => normalizedEntropy (parabola u d w x))
      (curveEntropySlope u d w x) x := by
  have hm := hasDerivAt_curveMass u d w x
  have hl := hasDerivAt_curveLogMoment u d w x hx
  convert (hm.log hs).sub (hl.div hm hs) using 1
  unfold curveEntropySlope
  field_simp
  ring

theorem hasDerivAt_curveEntropySlope_zero (u d w : ι → ℝ)
    (hu : ∀ i, 0 < u i) (hs : mass u ≠ 0)
    (hd : mass d = 0) (hdlog : ∑ i, d i * Real.log (u i) = 0) :
    HasDerivAt (curveEntropySlope u d w)
      (2 * weightedSum (fun i => -(Real.log (u i) - logMoment u / mass u) / mass u) w
        - (∑ i, (d i)^2 / u i) / mass u) 0 := by
  have hm := hasDerivAt_curveMass u d w 0
  have hl := hasDerivAt_curveLogMoment u d w 0 (by simpa using hu)
  have hms := hasDerivAt_curveMassSlope d w 0
  have hls := hasDerivAt_curveLogSlope_zero u d w hu
  have hs' : mass (parabola u d w 0) ≠ 0 := by simpa using hs
  have hh := ((hls.neg.div hm hs').add
    ((hl.div (hm.pow 2) (pow_ne_zero 2 hs')).mul hms))
  convert hh using 1
  simp only [parabola_zero,parabolaSlope_zero,curveLogSlope,hdlog,hd,zero_add,zero_mul,
    add_zero,mul_zero,sub_zero,neg_zero,zero_div] 
  have hweight : weightedSum
      (fun i => -(Real.log (u i) - logMoment u / mass u) / mass u) w =
      -(∑ i, w i * Real.log (u i)) / mass u + logMoment u / mass u^2 * mass w := by
    rw [weightedSum_apply]
    change (∑ i, _) = -(∑ i, w i * Real.log (u i)) / mass u +
      logMoment u / mass u^2 * ∑ i, w i
    rw [neg_div,Finset.sum_div,← Finset.sum_neg_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hs]
    ring
  have hsum : (∑ i, (2*w i*Real.log (u i) + (d i)^2/u i)) =
      2*(∑ i, w i*Real.log (u i)) + ∑ i, (d i)^2/u i := by
    rw [Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hweight,hsum]
  field_simp [hs]
  ring

end ProjectionChannels.RevisionK182
