import StrongConvergence.StrongConvergenceNormLower
import StrongConvergence.StrongConvergenceEdgeSandwich
import RandomCompression.RevisionBernoulliLaw

/-! Support endpoints, reflection, and the affine lower norm bound. -/
open MeasureTheory Filter Set Matrix ProjectionChannels
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergence

lemma support_le_of_ae_le (ν : Measure ℝ) {r : ℝ} (h : ∀ᵐ x ∂ν, x ≤ r) :
    ∀ x ∈ realMeasureSupport ν, x ≤ r := by
  intro x hx
  by_contra hn
  have hz : ν (Ioi r) = 0 := by simpa only [ae_iff, not_le, Ioi] using h
  exact hx (Ioi r) isOpen_Ioi (lt_of_not_ge hn) hz

lemma support_ge_of_ae_ge (ν : Measure ℝ) {l : ℝ} (h : ∀ᵐ x ∂ν, l ≤ x) :
    ∀ x ∈ realMeasureSupport ν, l ≤ x := by
  intro x hx
  by_contra hn
  have hz : ν (Iio l) = 0 := by simpa only [ae_iff, not_le, Iio] using h
  exact hx (Iio l) isOpen_Iio (lt_of_not_ge hn) hz

lemma neg_mem_support_map_neg (ν : Measure ℝ) {x : ℝ} (hx : x ∈ realMeasureSupport ν) :
    -x ∈ realMeasureSupport (ν.map (fun y => -y)) := by
  intro U hU hxU hz
  apply hx ((fun y : ℝ => -y) ⁻¹' U) (hU.preimage continuous_neg) hxU
  rw [← Measure.map_apply measurable_neg hU.measurableSet]
  exact hz

lemma mem_realMeasureSupport_map_neg (ν : Measure ℝ) (x : ℝ) :
    x ∈ realMeasureSupport (ν.map (fun y => -y)) ↔ -x ∈ realMeasureSupport ν := by
  constructor
  · intro hx
    have h := neg_mem_support_map_neg (ν.map (fun y => -y)) hx
    rw [Measure.map_map measurable_neg measurable_neg] at h
    simp only [Function.comp_def, neg_neg] at h
    change -x ∈ realMeasureSupport (ν.map id) at h
    rw [Measure.map_id] at h
    exact h
  · intro hx
    simpa only [neg_neg] using neg_mem_support_map_neg ν hx

/-- Compact probability laws have attained left and right support endpoints,
with almost-everywhere bounds as well as pointwise support bounds. -/
theorem compact_probability_endpoints (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcompact : ∃ K : ℝ, ∀ᵐ x ∂ν, |x| ≤ K) :
    ∃ l u : ℝ, IsLeast (realMeasureSupport ν) l ∧ IsGreatest (realMeasureSupport ν) u ∧
      (∀ᵐ x ∂ν, l ≤ x) ∧ (∀ᵐ x ∂ν, x ≤ u) ∧
      u = sSup (realMeasureSupport ν) ∧
      -l = sSup (realMeasureSupport (ν.map (fun y => -y))) := by
  let νneg := ν.map (fun y : ℝ => -y)
  haveI : IsProbabilityMeasure νneg := isProbabilityMeasure_map measurable_neg.aemeasurable
  obtain ⟨K,hK⟩ := hcompact
  have hKneg : ∀ᵐ x ∂νneg, |x| ≤ K := by
    change ∀ᵐ x ∂ν.map (fun y : ℝ => -y), |x| ≤ K
    exact (ae_map_iff (μ := ν) (f := fun y : ℝ => -y) measurable_neg.aemeasurable
      (isClosed_le continuous_abs continuous_const).measurableSet).mpr
      (by simpa only [abs_neg] using hK)
  obtain ⟨u,hu,hup,hueq⟩ := compact_probability_right_edge ν ⟨K,hK⟩
  obtain ⟨v,hv,hvp,hveq⟩ := compact_probability_right_edge νneg ⟨K,hKneg⟩
  have hl : -v ∈ realMeasureSupport ν := (mem_realMeasureSupport_map_neg ν v).mp hv
  have hlo : ∀ᵐ x ∂ν, -v ≤ x := by
    have h := (ae_map_iff (μ := ν) (f := fun y : ℝ => -y) measurable_neg.aemeasurable
      (measurableSet_Iic (a := v))).mp hvp
    exact h.mono fun x hx => by change -x ≤ v at hx; linarith
  refine ⟨-v,u,⟨hl,support_ge_of_ae_ge ν hlo⟩,⟨hu,support_le_of_ae_le ν hup⟩,
    hlo,hup,hueq,?_⟩
  simpa only [neg_neg] using hveq

lemma shifted_normLowerTest_integral_pos (ν : Measure ℝ) [IsFiniteMeasure ν]
    (c : ℝ) {x r : ℝ} (hx : x ∈ realMeasureSupport ν) (hr : r < |c+x|) :
    0 < ∫ y, normLowerTest r (c+y) ∂ν := by
  have hc : Continuous (fun y => normLowerTest r (c+y)) :=
    (normLowerTest_continuous r).comp (continuous_const.add continuous_id)
  have hi : Integrable (fun y => normLowerTest r (c+y)) ν := by
    apply (integrable_const (1:ℝ)).mono' hc.aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using normLowerTest_abs_le_one r (c+y)
  apply (integral_pos_iff_support_of_nonneg (fun y => normLowerTest_nonneg r (c+y)) hi).mpr
  apply pos_iff_ne_zero.mpr
  exact hx (Function.support (fun y => normLowerTest r (c+y)))
    (isOpen_ne_fun hc continuous_const) (normLowerTest_pos hr).ne'

lemma shifted_eigenvalue_abs_le_norm {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (c : ℝ) (i : ι) :
    |c+hM.eigenvalues i| ≤ ‖(c:ℂ) • (1 : Matrix ι ι ℂ) + M‖ := by
  have h := (spectrum.add_mem_add_iff (R := ℝ) (s := c) (r := hM.eigenvalues i)).mpr
    (hM.eigenvalues_mem_spectrum_real i)
  have hn := spectrum.norm_le_norm_of_mem h
  simpa only [Algebra.algebraMap_eq_smul_one, Complex.real_smul, Real.norm_eq_abs, add_comm] using hn

/-- Every support point supplies the affine norm lower bound through a bounded
continuous spectral test. -/
theorem eventually_lt_norm_shift_of_support
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (M : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hM : ∀ n, (M n).IsHermitian) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM n).eigenvalues i))
        atTop (𝓝 (∫ x, f x ∂ν)))
    (c : ℝ) {x r : ℝ} (hx : x ∈ realMeasureSupport ν) (hr : r < |c+x|) :
    ∀ᶠ n in atTop, r < ‖(c:ℂ) • (1 : Matrix (Fin (d n)) (Fin (d n)) ℂ) + M n‖ := by
  letI (n : ℕ) : NeZero (d n) := ⟨(hd n).ne'⟩
  have hpos := shifted_normLowerTest_integral_pos ν c hx hr
  have hlim := hweak (fun y => normLowerTest r (c+y))
    ((normLowerTest_continuous r).comp (continuous_const.add continuous_id))
    ⟨1,fun y => normLowerTest_abs_le_one r (c+y)⟩
  filter_upwards [hlim.eventually (lt_mem_nhds hpos)] with n hn
  by_contra hnot
  have hle := le_of_not_gt hnot
  have hz (i : Fin (d n)) : normLowerTest r (c+(hM n).eigenvalues i) = 0 :=
    normLowerTest_eq_zero ((shifted_eigenvalue_abs_le_norm (hM n) c i).trans hle)
  simp only [hz, Finset.sum_const_zero, mul_zero] at hn
  exact (lt_irrefl 0) hn


/-- Weak spectral convergence and the two upper-edge bounds yield every affine
operator-norm limit with the support of the same probability measure. -/
theorem tendsto_norm_shift_of_weak_and_edges
    (d : ℕ → ℕ) [∀ n, NeZero (d n)] (hd : ∀ n, 0 < d n)
    (M : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hM : ∀ n, (M n).IsHermitian) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcompact : ∃ K : ℝ, ∀ᵐ x ∂ν, |x| ≤ K)
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM n).eigenvalues i))
        atTop (𝓝 (∫ x, f x ∂ν)))
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      largestEigenvalue (hM n) ≤ sSup (realMeasureSupport ν) + ε)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      largestEigenvalue (hM n).neg ≤
        sSup (realMeasureSupport (ν.map (fun y => -y))) + ε)
    (c : ℝ) :
    Tendsto (fun n => ‖(c:ℂ) • (1 : Matrix (Fin (d n)) (Fin (d n)) ℂ) + M n‖)
      atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν))) := by
  letI (n : ℕ) : NeZero (d n) := ⟨(hd n).ne'⟩
  obtain ⟨l,u,hleast,hgreatest,hlo,hup,hueq,hleq⟩ := compact_probability_endpoints ν hcompact
  rw [sSup_abs_add_eq_max_of_endpoints hleast hgreatest]
  apply tendsto_norm_shift_of_edges_and_lower (fun n => Fin (d n)) M hM c l u
  · simpa only [hueq] using hu
  · simpa only [hleq] using hl
  · intro ε hε
    rcases le_total |c+l| |c+u| with h | h
    · rw [max_eq_right h]
      exact eventually_lt_norm_shift_of_support d hd M hM ν hweak c hgreatest.1 (by linarith)
    · rw [max_eq_left h]
      exact eventually_lt_norm_shift_of_support d hd M hM ν hweak c hleast.1 (by linarith)

#print axioms tendsto_norm_shift_of_weak_and_edges
#print axioms compact_probability_endpoints
#print axioms eventually_lt_norm_shift_of_support
end StrongConvergence
