import StrongConvergence.StrongConvergenceNormLower
import StrongConvergence.StrongConvergenceNormProbability

/-!
# A quantitative moment criterion for norm and spectral-test convergence

Normalized trace moments determine continuous spectral tests. Summable
expected high even trace moments exclude outliers. The two proved mechanisms
combine here into norm convergence to the actual support norm, on the same
probability-one event as every continuous spectral test. The quantitative
moment hypotheses still have to be proved for the intended Haar ensemble.
-/

open MeasureTheory Filter Set Matrix ProjectionChannels
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergence

/-- Convergence of fixed normalized moments, together with summable high
even trace-moment ratios, implies norm convergence and convergence of every
continuous empirical spectral test. Strong convergence of all polynomials
requires applying the criterion to those polynomials as well.
No weak-convergence or operator-norm-convergence conclusion is assumed. -/
theorem ae_norm_and_spectral_tests_of_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (M : Ω → (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hM : ∀ ω n, (M ω n).IsHermitian)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : IsCompact (realMeasureSupport ν)) (hne : (realMeasureSupport ν).Nonempty)
    (hcompact : ∃ R : ℝ, ∀ᵐ x ∂ν, x ∈ Icc (-R) R)
    (hmom : ∀ j : ℕ, ∀ᵐ ω ∂μ, Tendsto
      (fun n => (1/(d n:ℝ))*(Matrix.trace ((M ω n)^j)).re)
        atTop (𝓝 (∫ x, x^j ∂ν)))
    (q : ℕ → ℕ → ℕ)
    (hInt : ∀ m n, Integrable (fun ω => (Matrix.trace ((M ω n)^(2*q m n))).re) μ)
    (hSum : ∀ m : ℕ, Summable (fun n : ℕ =>
      (∫ ω, (Matrix.trace ((M ω n)^(2*q m n))).re ∂μ) /
        (sSup (abs '' realMeasureSupport ν)+1/((m:ℝ)+1))^(2*q m n))) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => ‖M ω n‖) atTop (𝓝 (sSup (abs '' realMeasureSupport ν))) ∧
      ∀ f : ℝ → ℝ, Continuous f →
        Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM ω n).eigenvalues i))
          atTop (𝓝 (∫ x, f x ∂ν)) := by
  letI (n : ℕ) : NeZero (d n) := ⟨(hd n).ne'⟩
  let L : ℝ := sSup (abs '' realMeasureSupport ν)
  have hL : 0 ≤ L := by
    obtain ⟨x,hx⟩ := hne
    exact (abs_nonneg x).trans (le_csSup (hc.image continuous_abs).bddAbove ⟨x,hx,rfl⟩)
  have hupper := StrongConvergenceProbability.ae_countable_norm_upper_of_summable_high_moments
    (ι := Unit) μ (fun n => Fin (d n)) (fun ω n _ => M ω n) (fun ω n _ => hM ω n)
    (fun _ => L) (fun _ => hL) (fun _ => q) (fun _ => hInt) (fun _ => hSum)
  have hcommon : ∀ᵐ ω ∂μ, ∀ j : ℕ, Tendsto
      (fun n => (1/(d n:ℝ))*(Matrix.trace ((M ω n)^j)).re)
        atTop (𝓝 (∫ x, x^j ∂ν)) := ae_all_iff.mpr hmom
  obtain ⟨R,hR⟩ := hcompact
  filter_upwards [hupper,hcommon] with ω hωupper hωmom
  have hevent : ∀ᶠ n in atTop, ‖M ω n‖ ≤ L+1 :=
    (hωupper () 1 zero_lt_one).mono fun _ h => h.le
  have hb := (isBoundedUnder_of_eventually_le hevent).bddAbove_range
  obtain ⟨C,hC⟩ := hb
  have hbAll (n : ℕ) : ‖M ω n‖ ≤ max R C := (hC ⟨n,rfl⟩).trans (le_max_right _ _)
  have hνAll : ∀ᵐ x ∂ν, x ∈ Icc (-(max R C)) (max R C) :=
    hR.mono fun x hx => ⟨(neg_le_neg (le_max_left _ _)).trans hx.1, hx.2.trans (le_max_left _ _)⟩
  have htests : ∀ f : ℝ → ℝ, Continuous f →
      Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM ω n).eigenvalues i))
        atTop (𝓝 (∫ x, f x ∂ν)) := fun f hf =>
    StrongConvergenceMoments.matrix_spectral_tests_tendsto_of_trace_moments d hd
      (M ω) (hM ω) ν hbAll hνAll hωmom f hf.continuousOn
  refine ⟨?_,htests⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlower := eventually_lt_norm_of_lt_supportNorm d hd (M ω) (hM ω) ν hc hne
    (fun f hf _ => htests f hf) (show L-ε < L by linarith)
  have hu := hωupper () ε hε
  filter_upwards [hlower,hu] with n hnlo hnhi
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

#print axioms ae_norm_and_spectral_tests_of_moments

end StrongConvergence
