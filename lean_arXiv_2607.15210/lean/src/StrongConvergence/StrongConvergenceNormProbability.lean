import StrongConvergence.StrongConvergenceNorm
import StrongConvergence.StrongConvergenceProbability
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# High trace moments imply almost-sure upper spectral-norm bounds

This is an actual matrix-sequence consequence of Markov and Borel--Cantelli.
The order of the even moment may grow with the matrix dimension and depend on
the test and tolerance. Summable expected-moment ratios are quantitative
inputs, not an assumed norm-convergence conclusion. Establishing those ratios
for Haar block polynomials remains a separate random-matrix problem.
-/

open Matrix MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Matrix.L2OpNorm
noncomputable section
namespace StrongConvergenceProbability

/-- The high-moment tail estimate in the extended-real form used by
Borel--Cantelli. -/
theorem norm_tail_le_ofReal_expected_trace
    {Ω N : Type*} [MeasurableSpace Ω] [Fintype N] [DecidableEq N] [Nonempty N]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : Ω → Matrix N N ℂ) (hM : ∀ω, (M ω).IsHermitian)
    (q : ℕ) (R : ℝ) (hR : 0<R)
    (hInt : Integrable (fun ω=>(Matrix.trace ((M ω)^(2*q))).re) μ) :
    μ {ω | R≤‖M ω‖} ≤
      ENNReal.ofReal ((∫ ω, (Matrix.trace ((M ω)^(2*q))).re ∂μ)/R^(2*q)) := by
  have h := StrongConvergence.norm_tail_le_expected_trace μ M hM q R hR hInt
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | R≤‖M ω‖})]
  exact ENNReal.ofReal_le_ofReal h

/-- A countable family of genuine Hermitian random matrix sequences has
one almost-sure upper-norm event whenever its high even trace-moment ratios
are summable. Independence is not required. -/
theorem ae_countable_norm_upper_of_summable_high_moments
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (N : ℕ → Type) [∀n, Fintype (N n)] [∀n, DecidableEq (N n)] [∀n, Nonempty (N n)]
    (M : Ω → (n : ℕ) → ι → Matrix (N n) (N n) ℂ)
    (hM : ∀ω n i, (M ω n i).IsHermitian)
    (L : ι → ℝ) (hL : ∀i, 0≤L i) (q : ι → ℕ → ℕ → ℕ)
    (hInt : ∀i m n, Integrable
      (fun ω=>(Matrix.trace ((M ω n i)^(2*q i m n))).re) μ)
    (hSum : ∀i (m : ℕ), Summable (fun n : ℕ =>
      (∫ ω, (Matrix.trace ((M ω n i)^(2*q i m n))).re ∂μ)/
        (L i+1/((m:ℝ)+1))^(2*q i m n))) :
    ∀ᵐ ω ∂μ, ∀i, ∀ε>0, ∀ᶠ n in atTop, ‖M ω n i‖<L i+ε := by
  have hprob (i : ι) (m : ℕ) :
      (∑' n, μ {ω | L i+1/((m:ℝ)+1)≤‖M ω n i‖}) ≠ ∞ := by
    have hR : 0<L i+1/((m:ℝ)+1) := add_pos_of_nonneg_of_pos (hL i) (by positivity)
    have hnonneg (n : ℕ) : 0≤
        (∫ ω, (Matrix.trace ((M ω n i)^(2*q i m n))).re ∂μ)/
          (L i+1/((m:ℝ)+1))^(2*q i m n) := by
      apply div_nonneg _ (pow_nonneg hR.le _)
      apply integral_nonneg
      intro ω
      exact (pow_nonneg (norm_nonneg _) _).trans
        (StrongConvergence.norm_pow_le_trace_even (M ω n i) (hM ω n i) (q i m n))
    have hfinite : (∑' n, ENNReal.ofReal
        ((∫ ω, (Matrix.trace ((M ω n i)^(2*q i m n))).re ∂μ)/
          (L i+1/((m:ℝ)+1))^(2*q i m n))) ≠ ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg (hSum i m)]
      exact ENNReal.ofReal_ne_top
    apply ne_top_of_le_ne_top hfinite
    apply ENNReal.tsum_le_tsum
    intro n
    exact norm_tail_le_ofReal_expected_trace μ (fun ω=>M ω n i) (fun ω=>hM ω n i)
      (q i m n) _ hR (hInt i m n)
  have hevent : ∀ᵐ ω ∂μ, ∀i, ∀m : ℕ, ∀ᶠ n in atTop,
      ‖M ω n i‖<L i+1/((m:ℝ)+1) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro m
    simpa only [mem_setOf_eq,not_le] using ae_eventually_not_mem (hprob i m)
  filter_upwards [hevent] with ω hω
  intro i ε hε
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω i m] with n hn
  exact hn.trans (add_lt_add_left hm (L i))

/-- In particular the limsup of the actual operator norm is at most the
proposed limiting spectral edge. Norm nonnegativity supplies the required
conditional-completeness bound for the real-valued limsup. -/
theorem ae_countable_norm_limsup_le_of_summable_high_moments
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (N : ℕ → Type) [∀n, Fintype (N n)] [∀n, DecidableEq (N n)] [∀n, Nonempty (N n)]
    (M : Ω → (n : ℕ) → ι → Matrix (N n) (N n) ℂ)
    (hM : ∀ω n i, (M ω n i).IsHermitian)
    (L : ι → ℝ) (hL : ∀i, 0≤L i) (q : ι → ℕ → ℕ → ℕ)
    (hInt : ∀i m n, Integrable
      (fun ω=>(Matrix.trace ((M ω n i)^(2*q i m n))).re) μ)
    (hSum : ∀i (m : ℕ), Summable (fun n : ℕ =>
      (∫ ω, (Matrix.trace ((M ω n i)^(2*q i m n))).re ∂μ)/
        (L i+1/((m:ℝ)+1))^(2*q i m n))) :
    ∀ᵐ ω ∂μ, ∀i, Filter.limsup (fun n=>‖M ω n i‖) atTop≤L i := by
  filter_upwards [ae_countable_norm_upper_of_summable_high_moments μ N M hM L hL q hInt hSum]
    with ω hω
  intro i
  have hc : atTop.IsCoboundedUnder (·≤·) (fun n=>‖M ω n i‖) :=
    Filter.IsCoboundedUnder.of_frequently_ge (Filter.Eventually.of_forall (fun n=>norm_nonneg (M ω n i))).frequently
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  have he := hω i (b-L i) (sub_pos.mpr hb)
  apply limsup_le_of_le hc
  filter_upwards [he] with n hn
  linarith

#print axioms norm_tail_le_ofReal_expected_trace
#print axioms ae_countable_norm_limsup_le_of_summable_high_moments
end StrongConvergenceProbability
