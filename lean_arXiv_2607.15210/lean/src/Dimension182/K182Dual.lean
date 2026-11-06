import Preliminaries.PreliminariesLegendre
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# A global largest-eigenvalue certificate at output dimension 182

The constants are exact rationals. The two square-root bounds are proved by
squaring rational numbers in Lean, not supplied as numerical assumptions.
-/

namespace ProjectionChannels.K182

noncomputable section
open scoped BigOperators

def t : ℝ := 27 / 100000
def L : ℝ := 162513 / 1000000
def z : ℝ := 2077 / 2000

/-- An upper bound on `a*u - z*c_t(u)` on the unit interval. -/
def q (t a z : ℝ) : ℝ :=
  (a - z + Real.sqrt ((a - z) ^ 2 + 4 * t * a * z)) / 2

theorem scalar_upper_bound {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (a z : ℝ) :
    a * u - z * bernoulliCost t u ≤ q t a z := by
  have ht : 0 ≤ t * (1 - t) := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hu : 0 ≤ u * (1 - u) := mul_nonneg hu0 (sub_nonneg.mpr hu1)
  have hts := Real.sq_sqrt ht
  have hus := Real.sq_sqrt hu
  have hunit : (2 * u - 1) ^ 2 + (2 * Real.sqrt (u * (1 - u))) ^ 2 = 1 := by
    nlinarith
  have hrad : (a - z) ^ 2 + 4 * t * a * z =
      (a + z * (2 * t - 1)) ^ 2 + (2 * z * Real.sqrt (t * (1 - t))) ^ 2 := by
    have heq : (2 * z * Real.sqrt (t * (1 - t))) ^ 2 =
        (2 * z) ^ 2 * (t * (1 - t)) := by rw [mul_pow, hts]
    rw [heq]
    ring
  have hrad0 : 0 ≤ (a - z) ^ 2 + 4 * t * a * z := by
    rw [hrad]
    positivity
  have hDs : Real.sqrt ((a - z) ^ 2 + 4 * t * a * z) ^ 2 =
      (a + z * (2 * t - 1)) ^ 2 + (2 * z * Real.sqrt (t * (1 - t))) ^ 2 := by
    rw [Real.sq_sqrt hrad0, hrad]
  have h := scalar_cauchy hunit (Real.sqrt_nonneg _) hDs
  rw [bernoulliCost_expansion ht0 ht1 hu0 hu1]
  unfold q
  nlinarith

/-- Rational upper enclosure for the first square root in the dual bound. -/
theorem first_sqrt_upper :
    Real.sqrt (((1 - L) - z) ^ 2 + 4 * t * (1 - L) * z) ≤
      10166800730621 / 50000000000000 := by
  apply (Real.sqrt_le_iff).2
  constructor <;> norm_num [t, L, z]

/-- Rational upper enclosure for the second square root in the dual bound. -/
theorem second_sqrt_upper :
    Real.sqrt ((-L - z) ^ 2 + 4 * t * (-L) * z) ≤
      120093711527227 / 100000000000000 := by
  apply (Real.sqrt_le_iff).2
  constructor <;> norm_num [t, L, z]

/-- The global dual bound is strictly negative. -/
theorem dual_bound_neg : z / 182 + q t (1 - L) z + 181 * q t (-L) z < 0 := by
  have h₁ := first_sqrt_upper
  have h₂ := second_sqrt_upper
  unfold q
  dsimp [t, L, z] at *
  linarith

/-- Every feasible unnormalized vector satisfies the coordinate-to-sum bound. -/
theorem coordinate_le_L_sum {u : Fin 182 → ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hc : (∑ i, bernoulliCost t (u i)) ≤ 1 / 182) (i : Fin 182) :
    u i ≤ L * ∑ j, u j := by
  classical
  let a : Fin 182 → ℝ := fun j => if j = i then 1 - L else -L
  have heach (j : Fin 182) :
      a j * u j - z * bernoulliCost t (u j) ≤ q t (a j) z :=
    scalar_upper_bound (by norm_num [t]) (by norm_num [t]) (hu0 j) (hu1 j) _ _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => heach j)
  have hlin : (∑ j, a j * u j) = u i - L * ∑ j, u j := by
    have heq (j : Fin 182) : a j * u j = (if j = i then u j else 0) - L * u j := by
      dsimp [a]
      split_ifs <;> ring
    simp_rw [heq]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  have hq : (∑ j, q t (a j) z) = q t (1 - L) z + 181 * q t (-L) z := by
    have heq (j : Fin 182) : q t (a j) z =
        q t (-L) z + (if j = i then q t (1 - L) z - q t (-L) z else 0) := by
      dsimp [a]
      split_ifs <;> ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib]
    simp
    ring
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hlin, hq] at hsum
  have hcost : z * (∑ j, bernoulliCost t (u j)) ≤ z / 182 := by
    have hz : 0 ≤ z := by norm_num [z]
    have h := mul_le_mul_of_nonneg_left hc hz
    simpa [div_eq_mul_inv] using h
  have hneg := dual_bound_neg
  linarith

/-- The mass is positive, so normalization is well-defined. -/
theorem sum_pos {u : Fin 182 → ℝ}
    (hu0 : ∀ i, 0 ≤ u i)
    (hc : (∑ i, bernoulliCost t (u i)) ≤ 1 / 182) :
    0 < ∑ j, u j := by
  have hs : 0 ≤ ∑ j, u j := Finset.sum_nonneg (fun i _ => hu0 i)
  by_contra h
  have hzero : (∑ j, u j) = 0 := le_antisymm (le_of_not_gt h) hs
  have hz : ∀ i, u i = 0 := by
    intro i
    have hi : u i ≤ ∑ j, u j := Finset.single_le_sum (fun j _ => hu0 j) (Finset.mem_univ i)
    linarith [hu0 i]
  have hcostzero : bernoulliCost t 0 = t := by
    simp only [bernoulliCost, sub_zero, mul_one, mul_zero, Real.sqrt_zero]
    exact Real.sq_sqrt (by norm_num [t])
  simp_rw [hz, hcostzero] at hc
  norm_num [t] at hc

/-- Every feasible unnormalized coordinate lies in the strict convexity range. -/
theorem coordinate_lt_quarter {u : Fin 182 → ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hc : (∑ i, bernoulliCost t (u i)) ≤ 1 / 182) (i : Fin 182) :
    u i < 1 / 4 := by
  have hi : bernoulliCost t (u i) ≤ ∑ j, bernoulliCost t (u j) :=
    Finset.single_le_sum (fun j _ => bernoulliCost_nonneg t (u j)) (Finset.mem_univ i)
  have h := scalar_upper_bound (t := t) (by norm_num [t]) (by norm_num [t]) (hu0 i) (hu1 i) 1 1
  have hsqrt : Real.sqrt (((1 : ℝ) - 1) ^ 2 + 4 * t * 1 * 1) ≤ 1 / 25 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num [t]
  dsimp [q] at h
  linarith

/-- The normalized eigenvalue bound used in the entropy certificate. -/
theorem normalized_coordinate_le_L {u : Fin 182 → ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hc : (∑ i, bernoulliCost t (u i)) ≤ 1 / 182)
    (hs : 0 < ∑ j, u j) (i : Fin 182) :
    u i / (∑ j, u j) ≤ L := by
  exact (div_le_iff₀ hs).2 (coordinate_le_L_sum hu0 hu1 hc i)

end
end ProjectionChannels.K182

