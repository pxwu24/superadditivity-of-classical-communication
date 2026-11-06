import RandomCompression.RevisionBernoulliCompression
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Matrix MeasureTheory Filter Set
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergence

variable {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]

local instance matrixCStarAlgebra : CStarAlgebra (Matrix N N ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance
  norm_mul_self_le := CStarRing.norm_mul_self_le

/-- A Hermitian operator norm is attained at an actual eigenvalue. -/
theorem norm_eq_abs_eigenvalue (M : Matrix N N ℂ) (hM : M.IsHermitian) :
    ∃ i, ‖M‖ = |hM.eigenvalues i| := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := N))
    (fun i => |hM.eigenvalues i|)
  refine ⟨i, le_antisymm ?_ ?_⟩
  · have h := norm_cfc_le (a:=M) (f:=fun x : ℝ => x) (abs_nonneg (hM.eigenvalues i)) ?_
    · change ‖cfc (id : ℝ → ℝ) M‖ ≤ _ at h
      rwa [cfc_id ℝ M hM.isSelfAdjoint] at h
    · intro x hx
      obtain ⟨j, rfl⟩ := hM.eigenvalues_eq_spectrum_real ▸ hx
      rw [Real.norm_eq_abs, ← hmax]
      exact Finset.le_sup' (fun i => |hM.eigenvalues i|) (Finset.mem_univ j)
  · exact spectrum.norm_le_norm_of_mem (hM.eigenvalues_mem_spectrum_real i)

/-- The ordinary trace of an integer power equals the corresponding spectral moment. -/
theorem trace_pow_re (M : Matrix N N ℂ) (hM : M.IsHermitian) (q : ℕ) :
    (Matrix.trace (M^q)).re = ∑ i, hM.eigenvalues i ^ q := by
  rw [← cfc_pow_id (R:=ℝ) M q hM.isSelfAdjoint, hM.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Matrix.trace_mul_cycle]
  have hU := hM.eigenvectorUnitary.prop.1
  change star (hM.eigenvectorUnitary : Matrix N N ℂ) *
    (hM.eigenvectorUnitary : Matrix N N ℂ) = 1 at hU
  rw [hU, one_mul, Matrix.trace_diagonal]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The unnormalized even moment controls the largest singular value. -/
theorem norm_pow_le_trace_even (M : Matrix N N ℂ) (hM : M.IsHermitian) (q : ℕ) :
    ‖M‖^(2*q) ≤ (Matrix.trace (M^(2*q))).re := by
  classical
  obtain ⟨i,hi⟩ := norm_eq_abs_eigenvalue M hM
  rw [trace_pow_re M hM, hi, (even_two_mul q).pow_abs]
  exact Finset.single_le_sum (fun j _ => (even_two_mul q).pow_nonneg _) (Finset.mem_univ i)

/-- Markov's high-moment bound for a Hermitian random matrix. The hypothesis
is an integrable even trace moment, not spectral-norm convergence. -/
theorem norm_tail_le_expected_trace
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : Ω → Matrix N N ℂ) (hM : ∀ ω, (M ω).IsHermitian)
    (q : ℕ) (R : ℝ) (hR : 0<R)
    (hInt : Integrable (fun ω => (Matrix.trace ((M ω)^(2*q))).re) μ) :
    μ.real {ω | R ≤ ‖M ω‖} ≤
      (∫ ω, (Matrix.trace ((M ω)^(2*q))).re ∂μ) / R^(2*q) := by
  have hpos : 0<R^(2*q) := pow_pos hR _
  apply (le_div_iff₀ hpos).mpr
  have hsub : {ω | R ≤ ‖M ω‖} ⊆
      {ω | R^(2*q) ≤ (Matrix.trace ((M ω)^(2*q))).re} := by
    intro ω hω
    exact (pow_le_pow_left₀ hR.le hω _).trans (norm_pow_le_trace_even (M ω) (hM ω) q)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => (pow_nonneg (norm_nonneg (M ω)) _).trans
      (norm_pow_le_trace_even (M ω) (hM ω) q))) hInt (R^(2*q))
  calc
    _ = R^(2*q)*μ.real {ω | R ≤ ‖M ω‖} := mul_comm _ _
    _ ≤ R^(2*q)*μ.real {ω | R^(2*q) ≤ (Matrix.trace ((M ω)^(2*q))).re} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) hpos.le
    _ ≤ _ := hmark

#print axioms norm_eq_abs_eigenvalue
#print axioms trace_pow_re
#print axioms norm_pow_le_trace_even
#print axioms norm_tail_le_expected_trace
end StrongConvergence
