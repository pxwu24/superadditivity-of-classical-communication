import Dimension182.K182SecondVariation

/-! Strict second-order descent on a right neighborhood, and simultaneous
objective/constraint descent along a continuous curve. -/

open Set Filter
open scoped Topology
noncomputable section
namespace ProjectionChannels.RevisionK182

theorem strict_descent_right_of_derivative_neg {f : ℝ → ℝ} {q : ℝ}
    (hf : HasDerivWithinAt f q (Ici 0) 0) (hq : q < 0) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), f x < f 0 := by
  have hi := hf.mono (show Ioi (0 : ℝ) ⊆ Ici 0 from Ioi_subset_Ici_self)
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp hi
  have hn := hlim.eventually (gt_mem_nhds hq)
  filter_upwards [hn,self_mem_nhdsWithin] with x hx hxp
  simp only [slope_def_field,sub_zero] at hx
  have h := (div_lt_iff₀ (show 0 < x from hxp)).mp hx
  linarith only [h]

theorem not_sublevel_localMin_of_right_descent
    {α : Type*} [TopologicalSpace α] {F C : α → ℝ} {B : Set α}
    {g : ℝ → α} {budget : ℝ}
    (hg : ContinuousAt g 0) (hbox : ∀ᶠ x in 𝓝[>] (0 : ℝ), g x ∈ B)
    (hbudget : C (g 0) ≤ budget)
    (hF : ∀ᶠ x in 𝓝[>] (0 : ℝ), F (g x) < F (g 0))
    (hC : ∀ᶠ x in 𝓝[>] (0 : ℝ), C (g x) < C (g 0)) :
    ¬ IsLocalMinOn F {v | v ∈ B ∧ C v ≤ budget} (g 0) := by
  intro hmin
  change ∀ᶠ v in 𝓝[{v | v ∈ B ∧ C v ≤ budget}] (g 0), F (g 0) ≤ F v at hmin
  rw [eventually_nhdsWithin_iff] at hmin
  have hlocal : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      g x ∈ {v | v ∈ B ∧ C v ≤ budget} → F (g 0) ≤ F (g x) :=
    nhdsWithin_le_nhds (hg.eventually hmin)
  have hfalse : ∀ᶠ x in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hF,hC,hbox,hlocal] with x hF hC hbox hmin
    exact (not_lt_of_ge (hmin ⟨hbox,hC.le.trans hbudget⟩)) hF
  obtain ⟨x,hx⟩ := hfalse.exists
  exact hx

theorem strict_descent_right_of_second_derivative_neg
    {f f' : ℝ → ℝ} {q : ℝ}
    (hf : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt f (f' x) x)
    (hzero : f' 0 = 0) (hf' : HasDerivAt f' q 0) (hq : q < 0) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), f x < f 0 := by
  have hslope : Tendsto (fun x : ℝ => x⁻¹ * f' x) (𝓝[≠] 0) (𝓝 q) := by
    simpa only [zero_add,hzero,sub_zero,smul_eq_mul] using hf'.tendsto_slope_zero
  have hsneg : ∀ᶠ x : ℝ in 𝓝[≠] 0, x⁻¹ * f' x < 0 :=
    hslope.eventually (gt_mem_nhds hq)
  rw [eventually_nhdsWithin_iff] at hsneg
  obtain ⟨η,hη,hsη⟩ := Metric.eventually_nhds_iff.mp hsneg
  obtain ⟨ε,hε,hfε⟩ := Metric.eventually_nhds_iff.mp hf
  filter_upwards [Ioo_mem_nhdsGT (lt_min hη hε)] with b hb
  have hbη : b < η := hb.2.trans_le (min_le_left _ _)
  have hbε : b < ε := hb.2.trans_le (min_le_right _ _)
  have hder (x : ℝ) (hx : x ∈ Icc 0 b) : HasDerivAt f (f' x) x := by
    apply hfε
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hx.1] using hx.2.trans_lt hbε
  obtain ⟨c,hc,heq⟩ := exists_hasDerivAt_eq_slope f f' hb.1
    (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
    (fun x hx => hder x ⟨hx.1.le,hx.2.le⟩)
  have hcη : dist c 0 < η := by
    simpa only [Real.dist_eq,sub_zero,abs_of_pos hc.1] using hc.2.trans hbη
  have hcf : f' c < 0 := by
    have hn := hsη hcη (by simpa using hc.1.ne')
    by_contra h
    have hp := mul_nonneg (inv_pos.mpr hc.1).le (le_of_not_gt h)
    linarith only [hn,hp]
  rw [heq,sub_zero] at hcf
  have h := (div_lt_iff₀ hb.1).mp hcf
  linarith only [h]

/-- A single concrete curve decreasing both constraint and objective
contradicts a constrained local minimum. -/
theorem not_sublevel_localMin_of_negative_curvatures
    {α : Type*} [TopologicalSpace α] {F C : α → ℝ} {B : Set α}
    {g : ℝ → α} {f' c' : ℝ → ℝ} {fq cq budget : ℝ}
    (hg : ContinuousAt g 0) (hbox : ∀ᶠ x in 𝓝 (0 : ℝ), g x ∈ B)
    (hbudget : C (g 0) ≤ budget)
    (hf : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt (fun y => F (g y)) (f' x) x)
    (hc : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt (fun y => C (g y)) (c' x) x)
    (hfzero : f' 0 = 0) (hczero : c' 0 = 0)
    (hf' : HasDerivAt f' fq 0) (hc' : HasDerivAt c' cq 0)
    (hfq : fq < 0) (hcq : cq < 0) :
    ¬ IsLocalMinOn F {v | v ∈ B ∧ C v ≤ budget} (g 0) := by
  intro hmin
  change ∀ᶠ v in 𝓝[{v | v ∈ B ∧ C v ≤ budget}] (g 0), F (g 0) ≤ F v at hmin
  rw [eventually_nhdsWithin_iff] at hmin
  have hlocal := hg.eventually hmin
  have hdF := strict_descent_right_of_second_derivative_neg hf hfzero hf' hfq
  have hdC := strict_descent_right_of_second_derivative_neg hc hczero hc' hcq
  have hbox' : ∀ᶠ x in 𝓝[>] (0 : ℝ), g x ∈ B := nhdsWithin_le_nhds hbox
  have hlocal' : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      g x ∈ {v | v ∈ B ∧ C v ≤ budget} → F (g 0) ≤ F (g x) :=
    nhdsWithin_le_nhds hlocal
  have hfalse : ∀ᶠ x in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hdF,hdC,hbox',hlocal'] with x hF hC hB hmin
    exact (not_lt_of_ge (hmin ⟨hB,hC.le.trans hbudget⟩)) hF
  obtain ⟨x,hx⟩ := hfalse.exists
  exact hx

#print axioms strict_descent_right_of_second_derivative_neg
#print axioms not_sublevel_localMin_of_negative_curvatures
end ProjectionChannels.RevisionK182
