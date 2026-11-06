import Entropy.BellLimitTransfer
import Mathlib.Analysis.Calculus.LHopital

/-! A genuine second derivative implies convergence of the central differences
used in Proposition A.3; this limit is not an additional analytic hypothesis. -/

open Filter Set
open scoped Topology
noncomputable section
namespace RevisionBell

theorem centralDifference_tendsto_second_derivative
    (F F' : ℝ → ℝ) (L : ℝ)
    (hF : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt F (F' x) x)
    (hF' : HasDerivAt F' L 0) :
    Tendsto (BellLimitVerification.centralDifference F) (𝓝[≠] (0 : ℝ)) (𝓝 L) := by
  have hnlim : Tendsto (fun x : ℝ => -x) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using (continuousAt_id.neg.tendsto : Tendsto (fun x : ℝ => -x) (𝓝 0) (𝓝 (-0)))
  have hfnear : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      HasDerivAt (fun y => F y+F (-y)-2*F 0) (F' x-F' (-x)) x := by
    have he : ∀ᶠ x in 𝓝 (0 : ℝ),
        HasDerivAt (fun y => F y+F (-y)-2*F 0) (F' x-F' (-x)) x := by
      filter_upwards [hF, hnlim.eventually hF] with x hx hnx
      have h := (hx.add (hnx.comp x (hasDerivAt_id x).neg)).sub_const (2*F 0)
      simpa only [Function.comp_def, mul_neg, mul_one, sub_eq_add_neg] using h
    exact he.filter_mono nhdsWithin_le_nhds
  have hgnear : ∀ᶠ x in 𝓝[≠] (0 : ℝ), HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
    apply Eventually.of_forall
    intro x
    simpa using (hasDerivAt_id x).pow 2
  have hg0 : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 2*x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    exact mul_ne_zero (by norm_num) hx0
  have hFc : ContinuousAt F 0 := hF.self_of_nhds.continuousAt
  have hfa : Tendsto (fun y => F y+F (-y)-2*F 0) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun x => F x+F (-x)-2*F 0) (𝓝[≠] (0 : ℝ))
        (𝓝 (F 0+F 0-2*F 0)) :=
      ((hFc.tendsto.add (hFc.tendsto.comp hnlim)).sub_const (2*F 0)).mono_left nhdsWithin_le_nhds
    convert h using 1 <;> ring
  have hga : Tendsto (fun y : ℝ => y^2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using ((continuousAt_id.pow 2).tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun y : ℝ => y^2) (𝓝[≠] 0) (𝓝 ((0 : ℝ)^2)))
  have hFpNeg : HasDerivAt (fun y => F' (-y)) (-L) 0 := by
    have hh : HasDerivAt F' L (- (0 : ℝ)) := by simpa using hF'
    have h := hh.comp 0 (hasDerivAt_id (0 : ℝ)).neg
    simpa only [neg_zero, Function.comp_def, mul_neg, mul_one] using h
  have hnum : HasDerivAt (fun y => F' y-F' (-y)) (2*L) 0 := by
    convert hF'.sub hFpNeg using 1 <;> ring
  have hquot : Tendsto (fun x => (F' x-F' (-x))/(2*x)) (𝓝[≠] (0 : ℝ)) (𝓝 L) := by
    have h := hnum.tendsto_slope_zero.div_const 2
    convert h using 1
    · funext x
      simp only [zero_add, neg_zero, sub_self, sub_zero, smul_eq_mul]
      ring
    · congr 1
      ring
  exact HasDerivAt.lhopital_zero_nhdsNE hfnear hgnear hg0 hfa hga hquot

theorem centralDifference_sequence_tendsto
    (F F' : ℝ → ℝ) (L : ℝ)
    (hF : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt F (F' x) x)
    (hF' : HasDerivAt F' L 0)
    (step : ℕ → ℝ) (hs : Tendsto step atTop (𝓝 0)) (hs0 : ∀ n, step n ≠ 0) :
    Tendsto (fun n => BellLimitVerification.centralDifference F (step n)) atTop (𝓝 L) := by
  apply (centralDifference_tendsto_second_derivative F F' L hF hF').comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hs, Eventually.of_forall hs0⟩

end RevisionBell
