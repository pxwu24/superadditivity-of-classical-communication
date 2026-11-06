import StrongConvergence.StrongConvergenceTensorInverseAsymptotics
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# A quadratic radius for the Haar Gram expansion

Scalar estimates for the product of the normalized Haar-Gram row sums.
These estimates are uniform in the moment order and do not assume any
random-matrix convergence theorem.
-/

open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

/-- A finite-product bound requiring only nonnegative factors. -/
theorem prod_one_add_mul_one_sub_sum_le_one
    (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j) (m : ℕ) :
    (∏ j ∈ Finset.range m, (1 + x j)) *
      (1 - ∑ j ∈ Finset.range m, x j) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hprod : 0 ≤ ∏ j ∈ Finset.range m, (1 + x j) := by
      exact Finset.prod_nonneg fun j _ => by linarith [hx j]
    have hsum : 0 ≤ ∑ j ∈ Finset.range m, x j :=
      Finset.sum_nonneg fun j _ => hx j
    have ha := hx m
    have he : 0 ≤ (∏ j ∈ Finset.range m, (1 + x j)) *
        (x m * (∑ j ∈ Finset.range m, x j) + x m ^ 2) := by positivity
    nlinarith

/-- When the sum is below one, the product is bounded by a geometric resolvent. -/
theorem prod_one_add_le_inv_one_sub_sum
    (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j) (m : ℕ)
    (hs : (∑ j ∈ Finset.range m, x j) < 1) :
    (∏ j ∈ Finset.range m, (1 + x j)) ≤
      1 / (1 - ∑ j ∈ Finset.range m, x j) := by
  exact (le_div_iff₀ (sub_pos.mpr hs)).mpr
    (prod_one_add_mul_one_sub_sum_le_one x hx m)

/-- Scalar row error at inverse dimension `x`. -/
def genusRowError (m : ℕ) (x : ℝ) : ℝ :=
  (∏ j ∈ Finset.range m, (1 + (j : ℝ) * x)) - 1

/-- The expansion radius is quadratic, rather than factorial, in the degree. -/
def genusRadius (m : ℕ) : ℝ := 1 / (2 * (m : ℝ) ^ 2)

lemma genusRadius_pos {m : ℕ} (hm : 0 < m) : 0 < genusRadius m := by
  unfold genusRadius
  positivity

lemma genusRowError_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ genusRowError m x := by
  unfold genusRowError
  have h : (1 : ℝ) ≤ ∏ j ∈ Finset.range m, (1 + (j : ℝ) * x) := by
    simpa using (Finset.prod_le_prod
      (s := Finset.range m) (f := fun _ : ℕ => (1 : ℝ))
      (fun _ _ => by norm_num) (fun j _ => by
        dsimp only
        have hj : 0 ≤ (j : ℝ) * x := mul_nonneg (Nat.cast_nonneg j) hx
        linarith) :
      (∏ _j ∈ Finset.range m, (1 : ℝ)) ≤
        ∏ j ∈ Finset.range m, (1 + (j : ℝ) * x))
  linarith

/-- The sum of the factors at the chosen radius is strictly below one quarter. -/
lemma sum_mul_genusRadius_lt_quarter {m : ℕ} (hm : 0 < m) :
    (∑ j ∈ Finset.range m, (j : ℝ) * genusRadius m) < 1 / 4 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : 2 * (∑ j ∈ Finset.range m, (j : ℝ)) =
      (m : ℝ) * ((m : ℝ) - 1) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Finset.sum_range_id_mul_two m)
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] at h
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h
    nlinarith
  rw [← Finset.sum_mul]
  unfold genusRadius
  have hden : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  rw [mul_one_div, div_lt_iff₀ hden]
  nlinarith

/-- At the quadratic radius the normalized Gram row error is below `1/3`. -/
theorem genusRowError_radius_lt_third {m : ℕ} (hm : 0 < m) :
    genusRowError m (genusRadius m) < 1 / 3 := by
  have hx : ∀ j : ℕ, 0 ≤ (j : ℝ) * genusRadius m := fun j => by
    exact mul_nonneg (Nat.cast_nonneg j) (genusRadius_pos hm).le
  have hsum := sum_mul_genusRadius_lt_quarter hm
  have hprod := prod_one_add_mul_one_sub_sum_le_one
    (fun j : ℕ => (j : ℝ) * genusRadius m) hx m
  have hp : (1 : ℝ) ≤ ∏ j ∈ Finset.range m, (1 + (j : ℝ) * genusRadius m) := by
    simpa using (Finset.prod_le_prod
      (s := Finset.range m) (f := fun _ : ℕ => (1 : ℝ))
      (fun _ _ => by norm_num) (fun j _ => by dsimp only; linarith [hx j]) :
      (∏ _j ∈ Finset.range m, (1 : ℝ)) ≤
        ∏ j ∈ Finset.range m, (1 + (j : ℝ) * genusRadius m))
  have hgap := mul_pos (show 0 < ∏ j ∈ Finset.range m,
      (1 + (j : ℝ) * genusRadius m) by linarith)
    (sub_pos.mpr hsum)
  unfold genusRowError
  nlinarith

/-- The prefactor in the finite Neumann/coefficient tail is at most two. -/
theorem genusRowError_radius_prefactor_le_two {m : ℕ} (hm : 0 < m) :
    (1 + genusRowError m (genusRadius m)) /
      (1 - genusRowError m (genusRadius m)) ≤ 2 := by
  have he := genusRowError_radius_lt_third hm
  apply (div_le_iff₀ (by linarith :
    0 < 1 - genusRowError m (genusRadius m))).mpr
  linarith

lemma genusRowError_succ (m : ℕ) (x : ℝ) :
    genusRowError (m + 1) x = genusRowError m x +
      (m : ℝ) * x + (m : ℝ) * x * genusRowError m x := by
  simp only [genusRowError, Finset.prod_range_succ]
  ring

lemma genusRowError_mono (m : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    genusRowError m x ≤ genusRowError m y := by
  unfold genusRowError
  apply sub_le_sub_right
  apply Finset.prod_le_prod
  · intro j _
    positivity
  · intro j _
    gcongr

/-- The row error scales at most linearly below any positive reference radius. -/
theorem genusRowError_le_scaled (m : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    genusRowError m x ≤ (x / y) * genusRowError m y := by
  have hscaled : y * genusRowError m x ≤ x * genusRowError m y := by
    induction m with
    | zero => simp [genusRowError]
    | succ m ih =>
      have hmono := genusRowError_mono m hx hxy
      have hmul := mul_le_mul_of_nonneg_left hmono
        (show 0 ≤ (m : ℝ) * x * y by positivity)
      simp only [genusRowError_succ]
      nlinarith
  calc
    genusRowError m x = (y * genusRowError m x) / y := by field_simp [hy.ne']
    _ ≤ (x * genusRowError m y) / y := div_le_div_of_nonneg_right hscaled hy.le
    _ = (x / y) * genusRowError m y := by ring

/-- Uniform control throughout the quadratic-radius interval. -/
theorem genusRowError_le_third_mul_ratio {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ genusRadius m) :
    genusRowError m x ≤ (x / genusRadius m) / 3 := by
  calc
    genusRowError m x ≤ (x / genusRadius m) * genusRowError m (genusRadius m) :=
      genusRowError_le_scaled m hx hxy (genusRadius_pos hm)
    _ ≤ (x / genusRadius m) * (1 / 3) := by
      exact mul_le_mul_of_nonneg_left (genusRowError_radius_lt_third hm).le
        (div_nonneg hx (genusRadius_pos hm).le)
    _ = (x / genusRadius m) / 3 := by ring

/-- A scalar Neumann-tail bound at every truncation order. -/
theorem genusRowError_neumann_tail_le {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ genusRadius m) (q : ℕ) :
    genusRowError m x ^ q / (1 - genusRowError m x) ≤
      2 * ((x / genusRadius m) / 3) ^ q := by
  have he0 := genusRowError_nonneg m hx
  have hratio0 : 0 ≤ x / genusRadius m := div_nonneg hx (genusRadius_pos hm).le
  have he : genusRowError m x < 1 / 3 :=
    lt_of_le_of_lt (genusRowError_mono m hx hxy) (genusRowError_radius_lt_third hm)
  have hden : 0 < 1 - genusRowError m x := by linarith
  have hpow : genusRowError m x ^ q ≤ ((x / genusRadius m) / 3) ^ q := by
    exact pow_le_pow_left₀ he0 (genusRowError_le_third_mul_ratio hm hx hxy) q
  have hinv : 1 / (1 - genusRowError m x) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  calc
    genusRowError m x ^ q / (1 - genusRowError m x) =
        genusRowError m x ^ q * (1 / (1 - genusRowError m x)) := by ring
    _ ≤ ((x / genusRadius m) / 3) ^ q * 2 := by
      exact mul_le_mul hpow hinv (by positivity) (by positivity)
    _ = 2 * ((x / genusRadius m) / 3) ^ q := by ring

/-- Increasing the moment order only adds nonnegative factors. -/
lemma genusRowError_monotone_order {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun m => genusRowError m x) := by
  apply monotone_nat_of_le_succ
  intro m
  rw [genusRowError_succ]
  have hnonneg := genusRowError_nonneg m hx
  have h1 : 0 ≤ (m : ℝ) * x := by positivity
  have h2 : 0 ≤ (m : ℝ) * x * genusRowError m x := by positivity
  linarith

/-- One quadratic radius works simultaneously for all orders at most `q`. -/
theorem genusRowError_uniform_radius_lt_third {m q : ℕ}
    (hq : 0 < q) (hmq : m ≤ q) :
    genusRowError m (genusRadius q) < 1 / 3 :=
  lt_of_le_of_lt (genusRowError_monotone_order (genusRadius_pos hq).le hmq)
    (genusRowError_radius_lt_third hq)

/-- The reciprocal ambient dimension is within the quadratic convergence radius. -/
lemma inv_dimension_le_genusRadius {m : ℕ} (hm : 0 < m) {N : ℝ}
    (hN : 2 * (m : ℝ) ^ 2 ≤ N) : 1 / N ≤ genusRadius m := by
  unfold genusRadius
  exact one_div_le_one_div_of_le (by positivity) hN

/-- Explicit dimension form of the scalar finite Neumann-tail bound. -/
theorem genusRowError_inv_dimension_neumann_tail_le {m : ℕ} (hm : 0 < m)
    {N : ℝ} (hN : 2 * (m : ℝ) ^ 2 ≤ N) (q : ℕ) :
    genusRowError m (1 / N) ^ q / (1 - genusRowError m (1 / N)) ≤
      2 * ((2 * (m : ℝ) ^ 2) / (3 * N)) ^ q := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hbound := genusRowError_neumann_tail_le hm (by positivity : 0 ≤ 1 / N)
    (inv_dimension_le_genusRadius hm hN) q
  have heq : ((1 / N) / genusRadius m) / 3 = (2 * (m : ℝ) ^ 2) / (3 * N) := by
    unfold genusRadius
    field_simp [hmR.ne', hNpos.ne']; ring
  simpa only [heq] using hbound

/-- Every nonnegative coefficient tail gains a prescribed power of the radius ratio. -/
theorem nonnegative_power_tail_le (S : Finset ℕ) (c : ℕ → ℝ) (r : ℕ)
    (hc : ∀ i ∈ S, 0 ≤ c i) (hr : ∀ i ∈ S, r ≤ i)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    (∑ i ∈ S, c i * x ^ i) ≤ (x / y) ^ r * ∑ i ∈ S, c i * y ^ i := by
  have hu0 : 0 ≤ x / y := div_nonneg hx hy.le
  have hu1 : x / y ≤ 1 := (div_le_one hy).mpr hxy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hp : x ^ i ≤ (x / y) ^ r * y ^ i := by
    calc
      x ^ i = ((x / y) * y) ^ i := by rw [div_mul_cancel₀ _ hy.ne']
      _ = (x / y) ^ i * y ^ i := mul_pow _ _ _
      _ ≤ (x / y) ^ r * y ^ i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hu0 hu1 (hr i hi))
          (pow_nonneg hy.le i)
  calc
    c i * x ^ i ≤ c i * ((x / y) ^ r * y ^ i) :=
      mul_le_mul_of_nonneg_left hp (hc i hi)
    _ = (x / y) ^ r * (c i * y ^ i) := by ring

/-- Polynomial form of the coefficient-tail estimate used after x-degree truncation. -/
theorem nonnegative_polynomial_tail_le (p : Polynomial ℝ) (r : ℕ)
    (hp : ∀ i, 0 ≤ p.coeff i) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    (∑ i ∈ p.support.filter (fun i => r ≤ i), p.coeff i * x ^ i) ≤
      (x / y) ^ r * p.eval y := by
  calc
    _ ≤ (x / y) ^ r *
        ∑ i ∈ p.support.filter (fun i => r ≤ i), p.coeff i * y ^ i :=
      nonnegative_power_tail_le _ _ r (fun i _ => hp i)
        (fun i hi => (Finset.mem_filter.mp hi).2) hx hxy hy
    _ ≤ (x / y) ^ r * ∑ i ∈ p.support, p.coeff i * y ^ i := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => mul_nonneg (hp i) (pow_nonneg hy.le i))
    _ = (x / y) ^ r * p.eval y := by rw [Polynomial.eval_eq_sum, Polynomial.sum_def]

/-- Combining the Neumann remainder and the coefficient tail gives the factor two
in the x-degree truncation bound. -/
theorem finite_expansion_tail_bound (Exact Middle Truncated C u ε : ℝ) (r q : ℕ)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 3)
    (hq : 0 < q)
    (hNeumann : |Exact - Middle| ≤ C * u ^ r * ε ^ q / (1 - ε))
    (hCoeff : |Middle - Truncated| ≤ C * u ^ r / (1 - ε)) :
    |Exact - Truncated| ≤ 2 * C * u ^ r := by
  have hden : 0 < 1 - ε := by linarith
  have hε1 : ε ≤ 1 := by linarith
  have hp : ε ^ q ≤ ε := pow_le_of_le_one hε0 hε1 (Nat.ne_of_gt hq)
  have hfactor : (ε ^ q + 1) / (1 - ε) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  calc
    |Exact - Truncated| = |(Exact - Middle) + (Middle - Truncated)| := by
      congr 1
      ring
    _ ≤ |Exact - Middle| + |Middle - Truncated| := abs_add _ _
    _ ≤ C * u ^ r * ε ^ q / (1 - ε) + C * u ^ r / (1 - ε) :=
      add_le_add hNeumann hCoeff
    _ = (C * u ^ r) * ((ε ^ q + 1) / (1 - ε)) := by ring
    _ ≤ (C * u ^ r) * 2 :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = 2 * C * u ^ r := by ring

private lemma genus_tail_constant_identity (Q : ℝ) (hQ : Q ≠ 0) (q : ℕ) :
    2 * Q ^ q * (2 * Q ^ 2) ^ (3 * q + 1) / (8 * Q ^ 4) ^ (2 * q) =
      4 * Q ^ 2 / ((8 : ℝ) ^ q * Q ^ q) := by
  rw [pow_succ, pow_mul (2 * Q ^ 2) 3 q, pow_mul (8 * Q ^ 4) 2 q]
  calc
    _ = 4 * Q ^ 2 * ((Q * (2 * Q ^ 2) ^ 3) / (8 * Q ^ 4) ^ 2) ^ q := by
      rw [div_pow, mul_pow]
      ring
    _ = 4 * Q ^ 2 * (1 / (8 * Q)) ^ q := by
      congr 1
      congr 1
      field_simp
      ring
    _ = _ := by rw [div_pow, mul_pow]; ring

/-- The factorial coefficient in the degree-uniform tail is absorbed into an
explicit factor decaying like `8⁻ᵠ q⁻ᵠ`. -/
theorem genus_tail_uniform_constant {q : ℕ} (hq : 0 < q) :
    2 * (q.factorial : ℝ) * (2 * (q : ℝ) ^ 2) ^ (3 * q + 1) /
        (8 * (q : ℝ) ^ 4) ^ (2 * q) ≤
      4 * (q : ℝ) ^ 2 / ((8 : ℝ) ^ q * (q : ℝ) ^ q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfac : (q.factorial : ℝ) ≤ (q : ℝ) ^ q := by
    exact_mod_cast Nat.factorial_le_pow q
  calc
    _ ≤ 2 * (q : ℝ) ^ q * (2 * (q : ℝ) ^ 2) ^ (3 * q + 1) /
        (8 * (q : ℝ) ^ 4) ^ (2 * q) := by gcongr
    _ = _ := genus_tail_constant_identity (q : ℝ) hqR.ne' q

private lemma genus_scaled_power_identity (F A N : ℝ) (hN : N ≠ 0) (p q : ℕ) :
    N ^ 2 * (2 * F * A ^ p * (A / N) ^ (2 * q + 2)) =
      2 * F * A ^ (p + (2 * q + 2)) / N ^ (2 * q) := by
  rw [div_pow, pow_add N (2 * q) 2, pow_add A p (2 * q + 2)]
  field_simp
  ring

/-- Dimension-uniform scalar estimate underlying the polynomial-method bound.
The right hand side is `4 * 8⁻ᵠ * q^(2-q)`, written without negative exponents. -/
theorem genus_tail_uniform_scaled {m q : ℕ} (hm : 0 < m) (hmq : m ≤ q)
    {N : ℝ} (hN : 8 * (q : ℝ) ^ 4 ≤ N) :
    N ^ 2 * (2 * (m.factorial : ℝ) * (2 * (m : ℝ) ^ 2) ^ (m - 1) *
      ((2 * (m : ℝ) ^ 2) / N) ^ (2 * q + 2)) ≤
      4 * (q : ℝ) ^ 2 / ((8 : ℝ) ^ q * (q : ℝ) ^ q) := by
  have hq : 0 < q := lt_of_lt_of_le hm hmq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmqR : (m : ℝ) ≤ q := by exact_mod_cast hmq
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hfac : (m.factorial : ℝ) ≤ (q.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hmq
  have hbase : 2 * (m : ℝ) ^ 2 ≤ 2 * (q : ℝ) ^ 2 := by gcongr
  have hbase1 : 1 ≤ 2 * (q : ℝ) ^ 2 := by nlinarith
  have hp : (2 * (m : ℝ) ^ 2) ^ ((m - 1) + (2 * q + 2)) ≤
      (2 * (q : ℝ) ^ 2) ^ (3 * q + 1) := by
    calc
      _ ≤ (2 * (q : ℝ) ^ 2) ^ ((m - 1) + (2 * q + 2)) := by gcongr
      _ ≤ _ := pow_le_pow_right₀ hbase1 (by omega)
  rw [genus_scaled_power_identity _ _ _ hNpos.ne']
  calc
    _ ≤ 2 * (q.factorial : ℝ) * (2 * (q : ℝ) ^ 2) ^ (3 * q + 1) /
        (8 * (q : ℝ) ^ 4) ^ (2 * q) := by gcongr
    _ ≤ _ := genus_tail_uniform_constant hq

/-- Applying the uniform scalar bound to any moment error satisfying the
x-degree tail estimate yields the explicit inverse-square dimension rate. -/
theorem genus_tail_degree_uniform_error_of_bound {m q : ℕ}
    (hm : 0 < m) (hmq : m ≤ q) {N K Exact Truncated : ℝ}
    (hK : 0 ≤ K) (hN : 8 * (q : ℝ) ^ 4 ≤ N)
    (herror : |Exact - Truncated| ≤ K ^ m *
      (2 * (m.factorial : ℝ) * (2 * (m : ℝ) ^ 2) ^ (m - 1) *
        ((2 * (m : ℝ) ^ 2) / N) ^ (2 * q + 2))) :
    |Exact - Truncated| ≤ 4 * (q : ℝ) ^ 2 * K ^ m /
      ((8 : ℝ) ^ q * (q : ℝ) ^ q * N ^ 2) := by
  have hq : 0 < q := lt_of_lt_of_le hm hmq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hscaled : N ^ 2 * |Exact - Truncated| ≤
      K ^ m * (4 * (q : ℝ) ^ 2 / ((8 : ℝ) ^ q * (q : ℝ) ^ q)) := by
    calc
      _ ≤ N ^ 2 * (K ^ m *
          (2 * (m.factorial : ℝ) * (2 * (m : ℝ) ^ 2) ^ (m - 1) *
            ((2 * (m : ℝ) ^ 2) / N) ^ (2 * q + 2))) :=
        mul_le_mul_of_nonneg_left herror (sq_nonneg N)
      _ = K ^ m * (N ^ 2 *
          (2 * (m.factorial : ℝ) * (2 * (m : ℝ) ^ 2) ^ (m - 1) *
            ((2 * (m : ℝ) ^ 2) / N) ^ (2 * q + 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (genus_tail_uniform_scaled hm hmq hN)
        (pow_nonneg hK m)
  calc
    _ ≤ (K ^ m * (4 * (q : ℝ) ^ 2 / ((8 : ℝ) ^ q * (q : ℝ) ^ q))) / N ^ 2 := by
      apply (le_div_iff₀ (by positivity : 0 < N ^ 2)).mpr
      simpa only [mul_comm] using hscaled
    _ = _ := by ring

/-- A quadratic ambient-dimension threshold suffices for an arbitrary-order
inverse-Gram approximation. The constant does not contain a factorial. -/
theorem scaled_inverse_permutationGram_neumann_row_bound_quadratic
    {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}
    (e : Fin m ↪ E) (hm : 0 < m) (hN : 2 * m ^ 2 ≤ Fintype.card E)
    (q : ℕ) (σ : Equiv.Perm (Fin m)) :
    (∑ τ : Equiv.Perm (Fin m),
      ‖((Fintype.card E : ℂ) ^ m • (permutationGram E m)⁻¹ -
        ∑ l ∈ Finset.range q,
          (1 - ((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m) ^ l) σ τ‖) ≤
      2 * ((2 * (m : ℝ) ^ 2) / (3 * Fintype.card E)) ^ q := by
  have hE : 0 < Fintype.card E := lt_of_lt_of_le (by positivity) hN
  have hER : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr hE
  have hNR : 2 * (m : ℝ) ^ 2 ≤ Fintype.card E := by exact_mod_cast hN
  have hsmall : genusRowError m (1 / Fintype.card E) < 1 := by
    have h := lt_of_le_of_lt
      (genusRowError_mono m (by positivity : 0 ≤ 1 / (Fintype.card E : ℝ))
        (inv_dimension_le_genusRadius hm hNR))
      (genusRowError_radius_lt_third hm)
    linarith
  have hmatrix := scaled_inverse_permutationGram_neumann_row_bound e hE
    (by simpa only [genusRowError, mul_one_div] using hsmall) q σ
  have hscalar := genusRowError_inv_dimension_neumann_tail_le hm hNR q
  exact hmatrix.trans (by simpa only [genusRowError, mul_one_div] using hscalar)

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.genusRowError_radius_lt_third
#print axioms ProjectionChannels.TensorHaar.genusRowError_radius_prefactor_le_two
#print axioms ProjectionChannels.TensorHaar.genusRowError_inv_dimension_neumann_tail_le
#print axioms ProjectionChannels.TensorHaar.nonnegative_polynomial_tail_le
#print axioms ProjectionChannels.TensorHaar.finite_expansion_tail_bound

#print axioms ProjectionChannels.TensorHaar.genus_tail_uniform_scaled

#print axioms ProjectionChannels.TensorHaar.scaled_inverse_permutationGram_neumann_row_bound_quadratic
#print axioms ProjectionChannels.TensorHaar.genus_tail_degree_uniform_error_of_bound
