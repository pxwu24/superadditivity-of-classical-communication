import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# Compact spectral support: moments imply continuous-test convergence

This deterministic approximation theorem is an intermediate step towards
the trace part of block-modified strong convergence. Its hypotheses are
ordinary convergence of all moments and a common compact support. It does
not assume weak convergence or any random-matrix theorem.
-/

open MeasureTheory Filter Set Polynomial
open scoped Topology BigOperators
noncomputable section
namespace StrongConvergenceMoments

lemma integrable_of_continuousOn_of_ae_mem_Icc
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : Integrable f μ := by
  have hi := hf.integrableOn_Icc (μ := μ)
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at hi
  exact hi

lemma integral_polynomial_eq_moments
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) (P : ℝ[X]) :
    (∫ x, P.eval x ∂μ) =
      ∑ j ∈ Finset.range (P.natDegree+1), P.coeff j * ∫ x, x^j ∂μ := by
  have hi (j : ℕ) : Integrable (fun x : ℝ => P.coeff j * x^j) μ :=
    integrable_of_continuousOn_of_ae_mem_Icc hs (by fun_prop)
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [integral_finset_sum _ (fun j _ => hi j)]
  simp_rw [integral_const_mul]

theorem polynomial_integral_tendsto_of_moments
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    {a b : ℝ} (hμ : ∀ n, ∀ᵐ x ∂μ n, x ∈ Icc a b)
    (hν : ∀ᵐ x ∂ν, x ∈ Icc a b)
    (hmom : ∀ j : ℕ, Tendsto (fun n => ∫ x, x^j ∂μ n) atTop (𝓝 (∫ x, x^j ∂ν)))
    (P : ℝ[X]) :
    Tendsto (fun n => ∫ x, P.eval x ∂μ n) atTop (𝓝 (∫ x, P.eval x ∂ν)) := by
  simp_rw [integral_polynomial_eq_moments (hμ _), integral_polynomial_eq_moments hν]
  exact tendsto_finset_sum _ (fun j _ => tendsto_const_nhds.mul (hmom j))

lemma integral_difference_le_of_uniform_Icc
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b ε : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, |f x-g x| ≤ ε) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ ε := by
  rw [← integral_sub (integrable_of_continuousOn_of_ae_mem_Icc hs hf)
    (integrable_of_continuousOn_of_ae_mem_Icc hs hg)]
  have hh : ∀ᵐ x ∂μ, ‖f x-g x‖ ≤ ε := hs.mono fun x hx => by
    simpa only [Real.norm_eq_abs] using hfg x hx
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const hh

/-- All moments and a common compact support imply convergence against
every function continuous on that support. Global boundedness is unnecessary. -/
theorem continuous_integral_tendsto_of_moments
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {a b : ℝ} (hμ : ∀ n, ∀ᵐ x ∂μ n, x ∈ Icc a b)
    (hν : ∀ᵐ x ∂ν, x ∈ Icc a b)
    (hmom : ∀ j : ℕ, Tendsto (fun n => ∫ x, x^j ∂μ n) atTop (𝓝 (∫ x, x^j ∂ν)))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨P,hP⟩ := exists_polynomial_near_of_continuousOn a b f hf (ε/3) (by positivity)
  have hlim := polynomial_integral_tendsto_of_moments μ ν hμ hν hmom P
  have he := (Metric.tendsto_nhds.mp hlim) (ε/3) (by positivity)
  filter_upwards [he] with n hn
  have hpcont : ContinuousOn (fun x => P.eval x) (Icc a b) := P.continuous.continuousOn
  have hleft := integral_difference_le_of_uniform_Icc (hμ n) hf hpcont
    (fun x hx => by simpa only [abs_sub_comm] using (hP x hx).le)
  have hright := integral_difference_le_of_uniform_Icc hν hpcont hf
    (fun x hx => (hP x hx).le)
  rw [Real.dist_eq] at hn ⊢
  have htriangle := abs_add ((∫ x, f x ∂μ n)-(∫ x, P.eval x ∂μ n))
    ((∫ x, P.eval x ∂μ n)-(∫ x, P.eval x ∂ν))
  have htriangle' := abs_add
    (((∫ x, f x ∂μ n)-(∫ x, P.eval x ∂μ n))+
      ((∫ x, P.eval x ∂μ n)-(∫ x, P.eval x ∂ν)))
    ((∫ x, P.eval x ∂ν)-(∫ x, f x ∂ν))
  simp only [sub_add_sub_cancel] at htriangle htriangle'
  linarith

/-- In particular this proves the usual bounded-continuous test formulation
of weak convergence, rather than assuming it. -/
theorem bounded_continuous_integral_tendsto_of_moments
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {a b : ℝ} (hμ : ∀ n, ∀ᵐ x ∂μ n, x ∈ Icc a b)
    (hν : ∀ᵐ x ∂ν, x ∈ Icc a b)
    (hmom : ∀ j : ℕ, Tendsto (fun n => ∫ x, x^j ∂μ n) atTop (𝓝 (∫ x, x^j ∂ν)))
    (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) :=
  continuous_integral_tendsto_of_moments μ ν hμ hν hmom f hf.continuousOn

end StrongConvergenceMoments
