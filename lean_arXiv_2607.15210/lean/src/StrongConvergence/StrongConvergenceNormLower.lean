import StrongConvergence.StrongConvergenceMomentMatrices
import RandomCompression.SpectralEdge
import Mathlib.Order.LiminfLimsup

/-!
# Weak spectral convergence gives the lower operator-norm bound

A bounded continuous nonnegative test vanishes on `[-r,r]` and is positive
at every real point of absolute value greater than `r`. A point in the
actual measure support makes its limiting integral positive. Consequently,
the empirical spectra must eventually contain a point outside `[-r,r]`.
No lower operator-norm estimate is assumed.
-/

open MeasureTheory Filter Set Matrix ProjectionChannels
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergence

/-- A bounded continuous test supported in `{x | r < |x|}`. -/
def normLowerTest (r x : ℝ) : ℝ := max 0 (min 1 (|x|-r))

lemma normLowerTest_continuous (r : ℝ) : Continuous (normLowerTest r) := by
  unfold normLowerTest
  fun_prop

lemma normLowerTest_nonneg (r x : ℝ) : 0 ≤ normLowerTest r x := le_max_left _ _

lemma normLowerTest_le_one (r x : ℝ) : normLowerTest r x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma normLowerTest_abs_le_one (r x : ℝ) : |normLowerTest r x| ≤ 1 := by
  rw [abs_of_nonneg (normLowerTest_nonneg r x)]
  exact normLowerTest_le_one r x

lemma normLowerTest_pos {r x : ℝ} (h : r < |x|) : 0 < normLowerTest r x := by
  exact lt_max_of_lt_right (lt_min zero_lt_one (sub_pos.mpr h))

lemma normLowerTest_eq_zero {r x : ℝ} (h : |x| ≤ r) : normLowerTest r x = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (sub_nonpos.mpr h)

lemma normLowerTest_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] (r : ℝ) :
    Integrable (normLowerTest r) ν := by
  apply (integrable_const (1:ℝ)).mono' (normLowerTest_continuous r).aestronglyMeasurable
  exact ae_of_all ν (fun x => by simpa only [Real.norm_eq_abs] using normLowerTest_abs_le_one r x)

/-- A point of the actual topological support forces the detecting test
to have a strictly positive integral. -/
theorem normLowerTest_integral_pos (ν : Measure ℝ) [IsFiniteMeasure ν]
    {x r : ℝ} (hx : x ∈ realMeasureSupport ν) (hr : r < |x|) :
    0 < ∫ u, normLowerTest r u ∂ν := by
  apply (integral_pos_iff_support_of_nonneg
    (fun u => normLowerTest_nonneg r u) (normLowerTest_integrable ν r)).mpr
  apply pos_iff_ne_zero.mpr
  exact hx (Function.support (normLowerTest r))
    (isOpen_ne_fun (normLowerTest_continuous r) continuous_const)
    (normLowerTest_pos hr).ne'

/-- Weak spectral tests force the operator norms eventually above every
strict lower bound for the absolute value of a support point. -/
theorem eventually_lt_norm_of_support
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (M : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hM : ∀ n, (M n).IsHermitian)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM n).eigenvalues i))
        atTop (𝓝 (∫ x, f x ∂ν)))
    {x r : ℝ} (hx : x ∈ realMeasureSupport ν) (hr : r < |x|) :
    ∀ᶠ n in atTop, r < ‖M n‖ := by
  letI (n : ℕ) : NeZero (d n) := ⟨(hd n).ne'⟩
  have hpos := normLowerTest_integral_pos ν hx hr
  have hlim := hweak (normLowerTest r) (normLowerTest_continuous r)
    ⟨1, normLowerTest_abs_le_one r⟩
  have he := hlim.eventually (lt_mem_nhds hpos)
  filter_upwards [he] with n hn
  by_contra hnot
  have hnle : ‖M n‖ ≤ r := le_of_not_gt hnot
  have hz (i : Fin (d n)) : normLowerTest r ((hM n).eigenvalues i) = 0 := by
    apply normLowerTest_eq_zero
    have hi : |(hM n).eigenvalues i| ≤ ‖M n‖ := by
      simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem
        ((hM n).eigenvalues_mem_spectrum_real i)
    exact hi.trans hnle
  simp only [hz, Finset.sum_const_zero, mul_zero] at hn
  exact (lt_irrefl 0) hn

/-- A compact nonempty support has an actual maximal absolute value.
The weak limit therefore gives the full eventual lower-edge estimate. -/
theorem eventually_lt_norm_of_lt_supportNorm
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (M : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hM : ∀ n, (M n).IsHermitian)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hc : IsCompact (realMeasureSupport ν)) (hne : (realMeasureSupport ν).Nonempty)
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM n).eigenvalues i))
        atTop (𝓝 (∫ x, f x ∂ν)))
    {r : ℝ} (hr : r < sSup (abs '' realMeasureSupport ν)) :
    ∀ᶠ n in atTop, r < ‖M n‖ := by
  have hm := (hc.image continuous_abs).isGreatest_sSup (hne.image abs)
  obtain ⟨x,hx,he⟩ := hm.1
  apply eventually_lt_norm_of_support d hd M hM ν hweak hx
  rwa [he]

/-- With any coarse upper norm bound, the real-valued liminf is defined
in the expected way and is at least the norm of the limiting support.
The bound need not approach the support edge. -/
theorem supportNorm_le_liminf_norm
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (M : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hM : ∀ n, (M n).IsHermitian)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hc : IsCompact (realMeasureSupport ν)) (hne : (realMeasureSupport ν).Nonempty)
    (hweak : ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM n).eigenvalues i))
        atTop (𝓝 (∫ x, f x ∂ν)))
    (hupper : ∃ C : ℝ, ∀ n, ‖M n‖ ≤ C) :
    sSup (abs '' realMeasureSupport ν) ≤ liminf (fun n => ‖M n‖) atTop := by
  have hb : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) (fun n => ‖M n‖) := by
    obtain ⟨C,hC⟩ := hupper
    exact isBoundedUnder_of ⟨C, hC⟩
  have hl : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) (fun n => ‖M n‖) :=
    isBoundedUnder_of ⟨0, fun n => norm_nonneg (M n)⟩
  apply (le_liminf_iff hb.isCoboundedUnder_ge hl).mpr
  intro r hr
  exact eventually_lt_norm_of_lt_supportNorm d hd M hM ν hc hne hweak hr

#print axioms normLowerTest_integral_pos
#print axioms eventually_lt_norm_of_support
#print axioms eventually_lt_norm_of_lt_supportNorm
#print axioms supportNorm_le_liminf_norm

end StrongConvergence
