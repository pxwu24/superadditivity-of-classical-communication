import StrongConvergence.StrongConvergencePolyChebyshev
import StrongConvergence.StrongConvergencePolyOrthogonality
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

/-! A polynomial-degree Markov bound derived from Chebyshev orthogonality. -/

open Polynomial Set
open scoped BigOperators

namespace ProjectionChannels.PolyChebyshev

theorem abs_eval_derivative_le_on_unit_interval (p : Polynomial ℝ) (D : ℕ) {M : ℝ}
    (hD : p.natDegree ≤ D) (hb : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |p.derivative.eval x| ≤ 2 * (D : ℝ) ^ 3 * M := by
  have hM : 0 ≤ M := (abs_nonneg (p.eval 0)).trans (hb 0 (by constructor <;> norm_num))
  obtain ⟨c, hc⟩ := exists_chebyshev_expansion p D hD
  have hd : p.derivative.eval x =
      ∑ i, c i * (Polynomial.Chebyshev.T ℝ (i.val : ℤ)).derivative.eval x := by
    have h := congrArg (fun q : Polynomial ℝ => q.derivative.eval x) hc
    simpa [Polynomial.derivative_sum, Polynomial.derivative_smul,
      Polynomial.eval_finset_sum, Polynomial.eval_smul] using h.symm
  rw [hd]
  calc
    _ ≤ ∑ i, |c i * (Polynomial.Chebyshev.T ℝ (i.val : ℤ)).derivative.eval x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (D + 1), 2 * M * (i.val : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul
        (ProjectionChannels.StrongConvergence.abs_chebyshev_expansion_coeff_le_two p c hc hb i)
        (abs_eval_derivative_T_le i.val hx) (abs_nonneg _) (by positivity)
    _ = ∑ i : Fin D, 2 * M * ((i.val : ℝ) + 1) ^ 2 := by
      rw [Fin.sum_univ_succ]
      simp
    _ ≤ ∑ _i : Fin D, 2 * M * (D : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (i.val : ℝ) + 1 ≤ D := by exact_mod_cast (show i.val + 1 ≤ D by omega)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi 2) (by positivity)
    _ = 2 * (D : ℝ) ^ 3 * M := by simp; ring

/-- Crude Markov inequality on `[0,a]`, with the polynomial dependence needed
by the moment-expansion interpolation argument. -/
theorem polynomial_markov_bound (p : Polynomial ℝ) (D : ℕ) {a M : ℝ}
    (ha : 0 < a) (hD : p.natDegree ≤ D)
    (hb : ∀ x ∈ Icc (0 : ℝ) a, |p.eval x| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) a) :
    |p.derivative.eval x| ≤ (4 * (D : ℝ) ^ 3 / a) * M := by
  let A : Polynomial ℝ := C (a / 2) * (X + 1)
  let q : Polynomial ℝ := p.comp A
  have hA : A.natDegree ≤ 1 := by
    have h₁ := (natDegree_mul_le (p := C (a / 2)) (q := (X + 1 : Polynomial ℝ)))
    have h₂ := natDegree_add_le (X : Polynomial ℝ) 1
    simp only [natDegree_C, natDegree_X, natDegree_one, max_eq_left (by omega : 0 ≤ 1),
      zero_add] at h₁ h₂
    exact h₁.trans h₂
  have hq : q.natDegree ≤ D := by
    have h := (natDegree_comp_le (p := p) (q := A))
    exact h.trans ((Nat.mul_le_mul_left _ hA).trans (by simpa using hD))
  have hqb : ∀ z ∈ Icc (-1 : ℝ) 1, |q.eval z| ≤ M := by
    intro z hz
    change |(p.comp A).eval z| ≤ M
    rw [eval_comp]
    apply hb
    simp only [A, eval_mul, eval_C, eval_add, eval_X, eval_one]
    constructor <;> nlinarith [hz.1, hz.2]
  let y : ℝ := 2 * x / a - 1
  have hy : y ∈ Icc (-1 : ℝ) 1 := by
    have h₁ : 0 ≤ 2 * x / a := div_nonneg (by nlinarith [hx.1]) ha.le
    have h₂ : 2 * x / a ≤ 2 := (div_le_iff₀ ha).mpr (by nlinarith [hx.2])
    constructor <;> dsimp [y] <;> linarith
  have harg : A.eval y = x := by
    simp only [A, y, eval_mul, eval_C, eval_add, eval_X, eval_one]
    field_simp
    ring
  have hd : q.derivative.eval y = p.derivative.eval x * (a / 2) := by
    simp only [q, derivative_comp, eval_mul, eval_comp, harg]
    simp [A, derivative_mul, derivative_add, mul_comm]
  have h := abs_eval_derivative_le_on_unit_interval q D hq hqb hy
  rw [hd, abs_mul, abs_of_pos (half_pos ha)] at h
  calc
    |p.derivative.eval x| ≤ (2 * (D : ℝ) ^ 3 * M) / (a / 2) :=
      (le_div_iff₀ (half_pos ha)).mpr h
    _ = (4 * (D : ℝ) ^ 3 / a) * M := by ring

#print axioms polynomial_markov_bound

/-- Bounds on a sufficiently fine set of samples control a polynomial on an
entire interval. The mesh size is tied to its degree through Markov's bound. -/
theorem polynomial_bound_of_dense_samples (p : Polynomial ℝ) (D : ℕ)
    {a δ B : ℝ} {I : Set ℝ}
    (ha : 0 < a) (hD : p.natDegree ≤ D)
    (hI : I ⊆ Icc (0 : ℝ) a)
    (hmesh : ∀ x ∈ Icc (0 : ℝ) a, ∃ y ∈ I, |x - y| ≤ δ)
    (hsmall : 8 * (D : ℝ) ^ 3 * δ ≤ a)
    (hb : ∀ y ∈ I, |p.eval y| ≤ B) :
    ∀ x ∈ Icc (0 : ℝ) a, |p.eval x| ≤ 2 * B := by
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr ha.le) p.continuous.abs.continuousOn
  have hmax' : ∀ x ∈ Icc (0 : ℝ) a, |p.eval x| ≤ |p.eval z| := isMaxOn_iff.mp hmax
  obtain ⟨y, hy, hdist⟩ := hmesh z hz
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hdist
  have hC : 0 ≤ (4 * (D : ℝ) ^ 3 / a) * |p.eval z| := by positivity
  have hdiff := (convex_Icc (0 : ℝ) a).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (p.hasDerivAt u).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using polynomial_markov_bound p D ha hD hmax' hu)
    (hI hy) hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hdiff
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left hdist hC)
  have hfac : (4 * (D : ℝ) ^ 3 / a) * δ ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ ha]
    nlinarith
  have hhalf : ((4 * (D : ℝ) ^ 3 / a) * |p.eval z|) * δ ≤ |p.eval z| / 2 := by
    have h := mul_le_mul_of_nonneg_right hfac (abs_nonneg (p.eval z))
    nlinarith
  have htri : |p.eval z| ≤ |p.eval z - p.eval y| + |p.eval y| := by
    have h := abs_add (p.eval z - p.eval y) (p.eval y)
    simpa using h
  have hB := hb y hy
  have hzbound : |p.eval z| ≤ 2 * B := by linarith
  intro x hx
  exact (hmax' x hx).trans hzbound

#print axioms polynomial_bound_of_dense_samples

end ProjectionChannels.PolyChebyshev
