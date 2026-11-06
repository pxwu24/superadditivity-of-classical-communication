import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
Second-order necessary condition along a feasible curve.

This supplies a genuine calculus ingredient of the repeated-high-coordinate
exclusion. The existence and second derivative of the appropriate curve
in the Bernoulli constraint surface remain to be proved separately.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace ProjectionChannels.K182SecondVariation

/-- A differentiable real function with a twice differentiable germ at zero
cannot have a local minimum there if its second derivative is negative.
The first derivative is only required on a right interval. -/
theorem not_localMin_of_second_derivative_neg
    {f f' : ℝ → ℝ} {q ε : ℝ} (hε : 0 < ε)
    (hf : ∀ x ∈ Icc 0 ε, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' q 0) (hq : q < 0) :
    ¬ IsLocalMin f 0 := by
  intro hmin
  have hfzero : f' 0 = 0 := hmin.hasDerivAt_eq_zero (hf 0 ⟨le_rfl, hε.le⟩)
  have hslope : Tendsto (fun x : ℝ => x⁻¹ * f' x) (𝓝[≠] 0) (𝓝 q) := by
    simpa only [zero_add, hfzero, sub_zero, smul_eq_mul] using hf'.tendsto_slope_zero
  have hsneg : ∀ᶠ x : ℝ in 𝓝[≠] 0, x⁻¹ * f' x < 0 :=
    hslope.eventually (gt_mem_nhds hq)
  rw [eventually_nhdsWithin_iff] at hsneg
  obtain ⟨η, hη, hsη⟩ := Metric.eventually_nhds_iff.mp hsneg
  change ∀ᶠ x in 𝓝 (0 : ℝ), f 0 ≤ f x at hmin
  obtain ⟨δ, hδ, hminδ⟩ := Metric.eventually_nhds_iff.mp hmin
  let b : ℝ := min ε (min η δ) / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbε : b < ε := by
    have hh := min_le_left ε (min η δ)
    dsimp [b]
    linarith
  have hbη : b < η := by
    have hh := (min_le_right ε (min η δ)).trans (min_le_left η δ)
    dsimp [b]
    linarith
  have hbδ : b < δ := by
    have hh := (min_le_right ε (min η δ)).trans (min_le_right η δ)
    dsimp [b]
    linarith
  have hcont : ContinuousOn f (Icc 0 b) := by
    intro x hx
    exact (hf x ⟨hx.1, hx.2.trans hbε.le⟩).continuousAt.continuousWithinAt
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope f f' hb hcont
    (fun x hx => hf x ⟨hx.1.le, hx.2.le.trans hbε.le⟩)
  have hcη : dist c 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hc.1]
    exact hc.2.trans hbη
  have hcne : c ∈ ({0}ᶜ : Set ℝ) := by simpa using hc.1.ne'
  have hcf : f' c < 0 := by
    have h := hsη hcη hcne
    have hic : 0 < c⁻¹ := inv_pos.mpr hc.1
    by_contra hnonneg
    have hp := mul_nonneg hic.le (le_of_not_gt hnonneg)
    linarith only [h, hp]
  have hfb : f b < f 0 := by
    rw [heq, sub_zero] at hcf
    have h := (div_lt_iff₀ hb).mp hcf
    linarith only [h]
  have hbδ' : dist b 0 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hb] using hbδ
  exact (not_lt_of_ge (hminδ hbδ')) hfb

/-- A local minimum over a set cannot have a feasible continuous curve
whose objective has strictly negative second derivative at the base point.
The hypotheses are local continuity, feasibility and actual derivatives;
no minimizer-shape conclusion is assumed. -/
theorem not_constrained_localMin_of_feasible_negative_curvature
    {α : Type*} [TopologicalSpace α] {F : α → ℝ} {C : Set α}
    {g : ℝ → α} {f' : ℝ → ℝ} {q ε : ℝ}
    (hg : ContinuousAt g 0) (hfeasible : ∀ᶠ x in 𝓝 (0 : ℝ), g x ∈ C)
    (hε : 0 < ε)
    (hf : ∀ x ∈ Icc 0 ε, HasDerivAt (fun x => F (g x)) (f' x) x)
    (hf' : HasDerivAt f' q 0) (hq : q < 0) :
    ¬ IsLocalMinOn F C (g 0) := by
  intro hmin
  have hwithin : Tendsto g (𝓝 (0 : ℝ)) (𝓝[C] (g 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hg, hfeasible⟩
  have hlocal : IsLocalMin (fun x => F (g x)) 0 := hwithin.eventually hmin
  exact not_localMin_of_second_derivative_neg hε hf hf' hq hlocal

#print axioms not_localMin_of_second_derivative_neg
#print axioms not_constrained_localMin_of_feasible_negative_curvature

end ProjectionChannels.K182SecondVariation
end
