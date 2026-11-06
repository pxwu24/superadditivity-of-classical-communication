import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The elementary Bernoulli Legendre identity

This file proves the exact scalar inequality and attains equality at the explicit
maximizer. It does not assume the random-matrix convergence theorem or formalize
free convolution. No custom axioms or `sorry` are used.
-/

namespace ProjectionChannels

noncomputable section

def bernoulliCost (t u : ℝ) : ℝ :=
  (Real.sqrt (t * (1 - u)) - Real.sqrt ((1 - t) * u)) ^ 2

def bernoulliDelta (t y : ℝ) : ℝ :=
  Real.sqrt ((y + 2 * t - 1) ^ 2 + 4 * t * (1 - t))

def bernoulliDual (t y : ℝ) : ℝ :=
  (y - 1 + bernoulliDelta t y) / 2

def bernoulliMaximizer (t y : ℝ) : ℝ :=
  (1 + (y + 2 * t - 1) / bernoulliDelta t y) / 2

theorem bernoulliCost_nonneg (t u : ℝ) : 0 ≤ bernoulliCost t u :=
  sq_nonneg _

theorem bernoulliCost_self (t : ℝ) : bernoulliCost t t = 0 := by
  simp [bernoulliCost, mul_comm]

theorem bernoulliDelta_original (t y : ℝ) :
    bernoulliDelta t y = Real.sqrt ((1 - y) ^ 2 + 4 * t * y) := by
  unfold bernoulliDelta
  congr 1
  ring

theorem bernoulliCost_expansion {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    bernoulliCost t u = t + (1 - 2 * t) * u -
      2 * Real.sqrt (t * (1 - t)) * Real.sqrt (u * (1 - u)) := by
  have htu : 0 ≤ t * (1 - u) := mul_nonneg ht0 (sub_nonneg.mpr hu1)
  have hut : 0 ≤ (1 - t) * u := mul_nonneg (sub_nonneg.mpr ht1) hu0
  have hprod : Real.sqrt (t * (1 - u)) * Real.sqrt ((1 - t) * u) =
      Real.sqrt (t * (1 - t)) * Real.sqrt (u * (1 - u)) := by
    rw [Real.sqrt_mul ht0, Real.sqrt_mul (sub_nonneg.mpr ht1),
      Real.sqrt_mul ht0, Real.sqrt_mul hu0]
    ring
  unfold bernoulliCost
  rw [sub_sq, Real.sq_sqrt htu, Real.sq_sqrt hut]
  nlinarith [hprod]

theorem bernoulliDelta_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    0 < bernoulliDelta t y := by
  have ht : 0 < 1 - t := sub_pos.mpr ht1
  apply Real.sqrt_pos.mpr
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)

theorem bernoulliDelta_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (y : ℝ) :
    bernoulliDelta t y ^ 2 = (y + 2 * t - 1) ^ 2 + 4 * t * (1 - t) := by
  have ht : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  apply Real.sq_sqrt
  positivity

/-- A two-dimensional Cauchy--Schwarz inequality proved by a sum of squares. -/
theorem scalar_cauchy {v b x z D : ℝ}
    (hunit : x ^ 2 + z ^ 2 = 1)
    (hD : 0 ≤ D) (hDs : D ^ 2 = v ^ 2 + b ^ 2) :
    v * x + b * z ≤ D := by
  have hid : (v * x + b * z) ^ 2 + (v * z - b * x) ^ 2 =
      (v ^ 2 + b ^ 2) * (x ^ 2 + z ^ 2) := by ring
  rw [hunit, mul_one, ← hDs] at hid
  exact le_of_sq_le_sq (by nlinarith [sq_nonneg (v * z - b * x)]) hD

/-- Fenchel's inequality for the explicitly defined Bernoulli cost. -/
theorem bernoulli_legendre_inequality {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (y : ℝ) :
    y * u - bernoulliCost t u ≤ bernoulliDual t y := by
  have ht : 0 ≤ t * (1 - t) := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hu : 0 ≤ u * (1 - u) := mul_nonneg hu0 (sub_nonneg.mpr hu1)
  have hts := Real.sq_sqrt ht
  have hus := Real.sq_sqrt hu
  have hunit : (2 * u - 1) ^ 2 + (2 * Real.sqrt (u * (1 - u))) ^ 2 = 1 := by
    nlinarith
  have hDs : bernoulliDelta t y ^ 2 =
      (y + 2 * t - 1) ^ 2 + (2 * Real.sqrt (t * (1 - t))) ^ 2 := by
    rw [bernoulliDelta_sq ht0 ht1]
    nlinarith
  have h := scalar_cauchy hunit (Real.sqrt_nonneg _) hDs
  change _ ≤ bernoulliDelta t y at h
  rw [bernoulliCost_expansion ht0 ht1 hu0 hu1]
  unfold bernoulliDual
  nlinarith

theorem bernoulliMaximizer_mem_Ioo {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    bernoulliMaximizer t y ∈ Set.Ioo (0 : ℝ) 1 := by
  have hD := bernoulliDelta_pos ht0 ht1 y
  have hDs := bernoulliDelta_sq ht0.le ht1.le y
  have ht : 0 < 1 - t := sub_pos.mpr ht1
  have hprod : 0 < 4 * t * (1 - t) := by positivity
  have hupper : y + 2 * t - 1 < bernoulliDelta t y := by nlinarith
  have hlower : -bernoulliDelta t y < y + 2 * t - 1 := by nlinarith
  have hquotUpper : (y + 2 * t - 1) / bernoulliDelta t y < 1 := by
    exact (div_lt_one hD).mpr hupper
  have hquotLower : -1 < (y + 2 * t - 1) / bernoulliDelta t y := by
    apply (lt_div_iff₀ hD).mpr
    simpa using hlower
  unfold bernoulliMaximizer
  constructor <;> linarith

theorem bernoulliMaximizer_product {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    bernoulliMaximizer t y * (1 - bernoulliMaximizer t y) =
      (Real.sqrt (t * (1 - t)) / bernoulliDelta t y) ^ 2 := by
  have hD := bernoulliDelta_pos ht0 ht1 y
  have hDs := bernoulliDelta_sq ht0.le ht1.le y
  have ht : 0 ≤ t * (1 - t) := mul_nonneg ht0.le (sub_pos.mpr ht1).le
  have hts := Real.sq_sqrt ht
  calc
    _ = (bernoulliDelta t y ^ 2 - (y + 2 * t - 1) ^ 2) /
        (4 * bernoulliDelta t y ^ 2) := by
      unfold bernoulliMaximizer
      field_simp only [ne_of_gt hD]
      <;> ring
    _ = _ := by
      have hnum : bernoulliDelta t y ^ 2 - (y + 2 * t - 1) ^ 2 =
          4 * t * (1 - t) := by linarith
      rw [hnum, div_pow, hts]
      ring


/-- The stated closed-form maximizer attains equality. -/
theorem bernoulli_legendre_equality {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    y * bernoulliMaximizer t y - bernoulliCost t (bernoulliMaximizer t y) =
      bernoulliDual t y := by
  have hD := bernoulliDelta_pos ht0 ht1 y
  have hDs := bernoulliDelta_sq ht0.le ht1.le y
  have ht : 0 ≤ t * (1 - t) := mul_nonneg ht0.le (sub_pos.mpr ht1).le
  have hts := Real.sq_sqrt ht
  have hu := bernoulliMaximizer_mem_Ioo ht0 ht1 y
  rw [bernoulliCost_expansion ht0.le ht1.le hu.1.le hu.2.le,
    bernoulliMaximizer_product ht0 ht1 y,
    Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hD.le)]
  calc
    _ = (y - 1) / 2 +
        ((y + 2 * t - 1) ^ 2 + 4 * Real.sqrt (t * (1 - t)) ^ 2) /
          (2 * bernoulliDelta t y) := by
      unfold bernoulliMaximizer
      field_simp only [ne_of_gt hD]
      <;> ring
    _ = _ := by
      rw [hts]
      rw [mul_assoc] at hDs
      rw [← hDs]
      unfold bernoulliDual
      field_simp only [ne_of_gt hD]
      <;> ring


/-- Equality holds only at the stated maximizer. -/
theorem bernoulli_legendre_equality_iff {t u : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (y : ℝ) :
    y * u - bernoulliCost t u = bernoulliDual t y ↔
      u = bernoulliMaximizer t y := by
  constructor
  · intro heq
    have hD := bernoulliDelta_pos ht0 ht1 y
    have hDs := bernoulliDelta_sq ht0.le ht1.le y
    have ht : 0 ≤ t * (1 - t) := mul_nonneg ht0.le (sub_pos.mpr ht1).le
    have hts := Real.sq_sqrt ht
    have hus := Real.sq_sqrt (mul_nonneg hu0 (sub_nonneg.mpr hu1))
    have hunit : (2 * u - 1) ^ 2 + (2 * Real.sqrt (u * (1 - u))) ^ 2 = 1 := by
      nlinarith
    have hDalt : bernoulliDelta t y ^ 2 =
        (y + 2 * t - 1) ^ 2 + (2 * Real.sqrt (t * (1 - t))) ^ 2 := by
      nlinarith
    rw [bernoulliCost_expansion ht0.le ht1.le hu0 hu1] at heq
    unfold bernoulliDual at heq
    have hdot : (y + 2 * t - 1) * (2 * u - 1) +
        (2 * Real.sqrt (t * (1 - t))) * (2 * Real.sqrt (u * (1 - u))) =
        bernoulliDelta t y := by nlinarith
    have hnorm :
        (bernoulliDelta t y * (2 * u - 1) - (y + 2 * t - 1)) ^ 2 +
        (bernoulliDelta t y * (2 * Real.sqrt (u * (1 - u))) -
          2 * Real.sqrt (t * (1 - t))) ^ 2 = 0 := by
      calc
        _ = bernoulliDelta t y ^ 2 *
              ((2 * u - 1) ^ 2 + (2 * Real.sqrt (u * (1 - u))) ^ 2) +
            ((y + 2 * t - 1) ^ 2 + (2 * Real.sqrt (t * (1 - t))) ^ 2) -
            2 * bernoulliDelta t y *
              ((y + 2 * t - 1) * (2 * u - 1) +
              (2 * Real.sqrt (t * (1 - t))) * (2 * Real.sqrt (u * (1 - u)))) := by ring
        _ = 0 := by rw [hunit, ← hDalt, hdot]; ring
    have hx : bernoulliDelta t y * (2 * u - 1) = y + 2 * t - 1 := by
      nlinarith [sq_nonneg (bernoulliDelta t y * (2 * Real.sqrt (u * (1 - u))) -
        2 * Real.sqrt (t * (1 - t)))]
    unfold bernoulliMaximizer
    field_simp only [ne_of_gt hD]
    nlinarith
  · intro hu
    rw [hu]
    exact bernoulli_legendre_equality ht0 ht1 y

/-- The dual value is the greatest value of the objective on the unit interval. -/
theorem bernoulli_legendre_maximum {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    IsGreatest ((fun u : ℝ => y * u - bernoulliCost t u) '' Set.Icc 0 1)
      (bernoulliDual t y) := by
  constructor
  · refine ⟨bernoulliMaximizer t y, ?_, bernoulli_legendre_equality ht0 ht1 y⟩
    exact ⟨(bernoulliMaximizer_mem_Ioo ht0 ht1 y).1.le,
      (bernoulliMaximizer_mem_Ioo ht0 ht1 y).2.le⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact bernoulli_legendre_inequality ht0.le ht1.le hu.1 hu.2 y

end

end ProjectionChannels

