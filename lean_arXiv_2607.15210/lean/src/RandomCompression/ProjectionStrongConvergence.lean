import Preliminaries.PreliminariesMatrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Strong convergence of deterministic orthogonal projections

The norm throughout this file is explicitly the matrix norm induced by the
Euclidean norm (`Matrix.L2OpNorm`), not the entrywise matrix norm. Polynomial
evaluation and normalized traces are the actual matrix operations.
-/

open scoped BigOperators Matrix.L2OpNorm Polynomial Topology
open Matrix Polynomial Filter Classical

noncomputable section

namespace ProjectionStrongConvergence

variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance matrixCStarAlgebra : CStarAlgebra (Matrix ι ι ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance
  norm_mul_self_le := CStarRing.norm_mul_self_le

/-- Every complex polynomial on an idempotent depends only on its values at 0 and 1. -/
theorem polynomial_projection (P : Matrix ι ι ℂ) (hP : P * P = P) (q : ℂ[X]) :
    aeval P q = q.eval 0 • (1 - P) + q.eval 1 • P := by
  have hId : IsIdempotentElem P := hP
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    simp only [map_add, Polynomial.eval_add, hq, hr, add_smul]
    abel
  | monomial n a =>
    cases n with
    | zero =>
      simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial,
        pow_zero, mul_one, Algebra.algebraMap_eq_smul_one]
      rw [smul_sub]
      abel
    | succ n =>
      simp [Polynomial.aeval_monomial, Polynomial.eval_monomial,
        hId.pow_succ_eq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc]

/-- The trace of an idempotent is the dimension of its range. -/
theorem trace_projection_eq_rank (P : Matrix ι ι ℂ) (hP : P * P = P) :
    Matrix.trace P = (P.rank : ℂ) := by
  have hProj : LinearMap.IsProj (LinearMap.range P.mulVecLin) P.mulVecLin := by
    constructor
    · intro x
      exact LinearMap.mem_range_self P.mulVecLin x
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      change P *ᵥ (P *ᵥ y) = P *ᵥ y
      rw [Matrix.mulVec_mulVec, hP]
  have h := hProj.trace
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ ι),
    LinearMap.toMatrix_eq_toMatrix'] at h
  change Matrix.trace (LinearMap.toMatrix' (Matrix.toLin' P)) = _ at h
  rw [LinearMap.toMatrix'_toLin'] at h
  exact h

/-- Normalized trace on the actual matrix algebra. -/
def normalizedTrace (M : Matrix ι ι ℂ) : ℂ :=
  Matrix.trace M / (Fintype.card ι : ℂ)

theorem normalizedTrace_polynomial_projection [Nonempty ι]
    (P : Matrix ι ι ℂ) (hP : P * P = P) (q : ℂ[X]) :
    normalizedTrace (aeval P q) =
      (1 - ((P.rank : ℝ) / Fintype.card ι : ℝ)) * q.eval 0 +
        (((P.rank : ℝ) / Fintype.card ι : ℝ) : ℂ) * q.eval 1 := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [polynomial_projection P hP]
  simp only [normalizedTrace, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_one, trace_projection_eq_rank P hP, smul_eq_mul,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp
  ring

/-- The spectrum of an idempotent is contained in `{0,1}`. -/
theorem spectrum_projection_subset [Nonempty ι]
    (P : Matrix ι ι ℂ) (hP : P * P = P) (z : ℂ) (hz : z ∈ spectrum ℂ P) :
    z = 0 ∨ z = 1 := by
  have hm : (Polynomial.eval z (X ^ 2 - X : ℂ[X])) ∈
      spectrum ℂ (aeval P (X ^ 2 - X : ℂ[X])) := by
    rw [spectrum.map_polynomial_aeval]
    exact ⟨z, hz, rfl⟩
  have heq : z ^ 2 - z = 0 := by
    simpa [pow_two, hP] using hm
  have hmul : z * (z - 1) = 0 := by
    linear_combination heq
  exact (mul_eq_zero.mp hmul).imp_right (fun h => sub_eq_zero.mp h)

/-- Both spectral points occur for a nonzero, nonidentity idempotent. -/
theorem spectrum_projection_endpoints (P : Matrix ι ι ℂ) (hP : P * P = P)
    (h0 : P ≠ 0) (h1 : P ≠ 1) :
    (0 : ℂ) ∈ spectrum ℂ P ∧ (1 : ℂ) ∈ spectrum ℂ P := by
  constructor
  · rw [spectrum.zero_mem_iff]
    intro hu
    exact h1 ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp hP)
  · rw [spectrum.mem_iff]
    simp only [map_one]
    intro hu
    have hId : IsIdempotentElem (1 - P) := by
      change (1 - P) * (1 - P) = 1 - P
      noncomm_ring [hP]
    have heq := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp hId
    apply h0
    have : 1 - P - 1 = 0 := sub_eq_zero.mpr heq
    simpa using this

/-- The exact Euclidean operator norm of a polynomial in a proper orthogonal projection. -/
theorem norm_polynomial_projection [Nonempty ι]
    (P : Matrix ι ι ℂ) (hH : P.IsHermitian) (hP : P * P = P)
    (h0 : P ≠ 0) (h1 : P ≠ 1) (q : ℂ[X]) :
    ‖aeval P q‖ = max ‖q.eval 0‖ ‖q.eval 1‖ := by
  have hSA : IsSelfAdjoint P := hH
  have hN : IsStarNormal P := hSA.isStarNormal
  rw [← cfc_polynomial q P hN]
  apply le_antisymm
  · apply norm_cfc_le ((norm_nonneg _).trans (le_max_left _ _))
    intro z hz
    rcases spectrum_projection_subset P hP z hz with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · apply max_le
    · exact norm_apply_le_norm_cfc q.eval P (spectrum_projection_endpoints P hP h0 h1).1
        q.continuous.continuousOn hN
    · exact norm_apply_le_norm_cfc q.eval P (spectrum_projection_endpoints P hP h0 h1).2
        q.continuous.continuousOn hN

variable {κ : ℕ → Type} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
  [∀ n, Nonempty (κ n)]

/-- Convergence of rank ratios to an interior value makes the projections eventually proper. -/
theorem eventually_proper_projection
    (P : ∀ n, Matrix (κ n) (κ n) ℂ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hr : Tendsto (fun n => ((P n).rank : ℝ) / Fintype.card (κ n)) atTop (𝓝 t)) :
    ∀ᶠ n in atTop, P n ≠ 0 ∧ P n ≠ 1 := by
  have hpos : ∀ᶠ n in atTop, 0 < ((P n).rank : ℝ) / Fintype.card (κ n) :=
    hr.eventually (eventually_gt_nhds ht0)
  have hlt : ∀ᶠ n in atTop, ((P n).rank : ℝ) / Fintype.card (κ n) < 1 :=
    hr.eventually (eventually_lt_nhds ht1)
  filter_upwards [hpos, hlt] with n hn0 hn1
  constructor
  · intro h
    simp [h] at hn0
  · intro h
    have hcard : (Fintype.card (κ n) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [h, Matrix.rank_one, hcard] at hn1

/-- Moment convergence to the Bernoulli law `(1-t) δ₀ + t δ₁`. -/
theorem projection_polynomial_trace_tendsto
    (P : ∀ n, Matrix (κ n) (κ n) ℂ) (hP : ∀ n, P n * P n = P n)
    (t : ℝ)
    (hr : Tendsto (fun n => ((P n).rank : ℝ) / Fintype.card (κ n)) atTop (𝓝 t))
    (q : ℂ[X]) :
    Tendsto (fun n => normalizedTrace (aeval (P n) q)) atTop
      (𝓝 ((1 - (t : ℂ)) * q.eval 0 + (t : ℂ) * q.eval 1)) := by
  have hc : Tendsto (fun n => (((P n).rank : ℝ) / Fintype.card (κ n) : ℝ) : ℕ → ℝ)
      atTop (𝓝 t) := hr
  have hc' : Tendsto (fun n => (((P n).rank : ℝ) / Fintype.card (κ n) : ℂ))
      atTop (𝓝 (t : ℂ)) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hc
  have h := (((tendsto_const_nhds (x := (1 : ℂ))).sub hc').mul_const (q.eval 0)).add
    (hc'.mul_const (q.eval 1))
  convert h using 1
  ext n
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using
    normalizedTrace_polynomial_projection (P n) (hP n) q

/-- For every polynomial the operator norm is eventually exactly its Bernoulli-limit norm. -/
theorem projection_polynomial_norm_eventually
    (P : ∀ n, Matrix (κ n) (κ n) ℂ)
    (hH : ∀ n, (P n).IsHermitian) (hP : ∀ n, P n * P n = P n)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hr : Tendsto (fun n => ((P n).rank : ℝ) / Fintype.card (κ n)) atTop (𝓝 t))
    (q : ℂ[X]) :
    ∀ᶠ n in atTop, ‖aeval (P n) q‖ = max ‖q.eval 0‖ ‖q.eval 1‖ := by
  filter_upwards [eventually_proper_projection P t ht0 ht1 hr] with n hn
  exact norm_polynomial_projection (P n) (hH n) (hP n) hn.1 hn.2 q

/-- The elementary strong-convergence input: moments and Euclidean operator norms
converge for every complex polynomial, solely from the interior rank ratio. -/
theorem projections_strongly_converge_to_bernoulli
    (P : ∀ n, Matrix (κ n) (κ n) ℂ)
    (hH : ∀ n, (P n).IsHermitian) (hP : ∀ n, P n * P n = P n)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hr : Tendsto (fun n => ((P n).rank : ℝ) / Fintype.card (κ n)) atTop (𝓝 t)) :
    ∀ q : ℂ[X],
      Tendsto (fun n => normalizedTrace (aeval (P n) q)) atTop
        (𝓝 ((1 - (t : ℂ)) * q.eval 0 + (t : ℂ) * q.eval 1)) ∧
      Tendsto (fun n => ‖aeval (P n) q‖) atTop
        (𝓝 (max ‖q.eval 0‖ ‖q.eval 1‖)) := by
  intro q
  constructor
  · exact projection_polynomial_trace_tendsto P hP t hr q
  · apply tendsto_const_nhds.congr'
    filter_upwards [projection_polynomial_norm_eventually P hH hP t ht0 ht1 hr q] with n hn
    exact hn.symm

end ProjectionStrongConvergence

