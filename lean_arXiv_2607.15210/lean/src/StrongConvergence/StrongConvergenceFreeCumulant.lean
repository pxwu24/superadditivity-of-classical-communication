import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Formal Bernoulli cumulants

This module proves the quadratic formal-series identity underlying the
Bernoulli R-transform. It does not assume the random-matrix convergence theorem.
The real coefficients are defined recursively, rather than extracted from an
analytic square root. The identities are therefore formal algebraic identities;
the coefficient estimate later supplies a positive radius of convergence.
-/

open scoped BigOperators
open PowerSeries

noncomputable section
namespace ProjectionChannels.FreeCumulant

/-- Shifted Bernoulli free cumulants: coefficient `n` is cumulant `n+1`.
The shift makes the quadratic convolution a sum over order `n`. -/
def bernoulliTail (t : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => bernoulliTail t n -
      ∑ i : Fin (n + 1), bernoulliTail t i.val * bernoulliTail t (n - i.val)
termination_by n => n
decreasing_by all_goals omega

/-- Bernoulli free cumulants, with zeroth coefficient set to zero. -/
def bernoulliCumulant (t : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => bernoulliTail t n

@[simp] theorem bernoulliCumulant_zero (t : ℝ) : bernoulliCumulant t 0 = 0 := rfl

@[simp] theorem bernoulliCumulant_one (t : ℝ) : bernoulliCumulant t 1 = t := by
  simp [bernoulliCumulant, bernoulliTail]

theorem bernoulliCumulant_recurrence (t : ℝ) (n : ℕ) :
    bernoulliCumulant t (n + 2) = bernoulliCumulant t (n + 1) -
      ∑ i : Fin (n + 1),
        bernoulliCumulant t (i.val + 1) * bernoulliCumulant t (n + 1 - i.val) := by
  rw [bernoulliCumulant, bernoulliTail]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : n + 1 - i.val = (n - i.val) + 1 := by omega
  simp only [hi, bernoulliCumulant]

theorem bernoulliCumulant_two (t : ℝ) :
    bernoulliCumulant t 2 = t * (1 - t) := by
  simp [bernoulliCumulant, bernoulliTail, Fin.sum_univ_succ]
  ring

theorem bernoulliCumulant_three (t : ℝ) :
    bernoulliCumulant t 3 = t * (1 - t) * (1 - 2 * t) := by
  simp [bernoulliCumulant, bernoulliTail, Fin.sum_univ_succ]
  ring

theorem bernoulliCumulant_four (t : ℝ) :
    bernoulliCumulant t 4 = t * (1 - t) * (1 - 5 * t + 5 * t ^ 2) := by
  rw [bernoulliCumulant_recurrence t 2]
  simp [Fin.sum_univ_succ, bernoulliCumulant_two, bernoulliCumulant_three]
  ring

/-- The shifted cumulant series. -/
def bernoulliTailSeries (t : ℝ) : PowerSeries ℝ := PowerSeries.mk (bernoulliTail t)

/-- The zero-constant-term cumulant series `Σ_{n≥1} κ_n X^n`. -/
def bernoulliCumulantSeries (t : ℝ) : PowerSeries ℝ :=
  X * bernoulliTailSeries t

@[simp] theorem coeff_bernoulliCumulantSeries (t : ℝ) (n : ℕ) :
    coeff ℝ n (bernoulliCumulantSeries t) = bernoulliCumulant t n := by
  cases n with
  | zero => simp [bernoulliCumulantSeries]
  | succ n => simp [bernoulliCumulantSeries, bernoulliTailSeries, bernoulliCumulant]

@[simp] theorem constantCoeff_bernoulliCumulantSeries (t : ℝ) :
    constantCoeff ℝ (bernoulliCumulantSeries t) = 0 := by
  simp [bernoulliCumulantSeries]

theorem bernoulliCumulantSeries_eq_mk (t : ℝ) :
    bernoulliCumulantSeries t = PowerSeries.mk (bernoulliCumulant t) := by
  ext n
  simp

theorem bernoulliTailSeries_equation (t : ℝ) :
    bernoulliTailSeries t = C ℝ t + X * bernoulliTailSeries t -
      X * (bernoulliTailSeries t * bernoulliTailSeries t) := by
  ext n
  cases n with
  | zero => simp [bernoulliTailSeries, bernoulliTail]
  | succ n =>
    simp only [map_sub, map_add, coeff_succ_C, coeff_succ_X_mul, zero_add]
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← Fin.sum_univ_eq_sum_range]
    simp [bernoulliTailSeries, bernoulliTail]

/-- The defining quadratic equation of the Bernoulli cumulant series. -/
theorem bernoulliCumulantSeries_quadratic (t : ℝ) :
    bernoulliCumulantSeries t ^ 2 + (1 - X) * bernoulliCumulantSeries t -
      C ℝ t * X = 0 := by
  have h := congrArg (fun f : PowerSeries ℝ => X * f)
    (bernoulliTailSeries_equation t)
  dsimp [bernoulliCumulantSeries]
  linear_combination h

/-- A quadratic equation with constant linear coefficient one has at most
one solution with zero constant coefficient. This also applies after a formal
substitution `X ↦ W`, without introducing analytic branch assumptions. -/
theorem quadratic_zeroConstant_unique {t : ℝ} {W A B : PowerSeries ℝ}
    (hW : constantCoeff ℝ W = 0)
    (hA0 : constantCoeff ℝ A = 0) (hB0 : constantCoeff ℝ B = 0)
    (hA : A ^ 2 + (1 - W) * A - C ℝ t * W = 0)
    (hB : B ^ 2 + (1 - W) * B - C ℝ t * W = 0) : A = B := by
  have hfactor : (A - B) * (A + B + 1 - W) = 0 := by
    linear_combination hA - hB
  have hright : A + B + 1 - W ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff ℝ) h
    simp [hA0, hB0, hW] at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hright)

/-- The recursively constructed series is the unique zero-constant solution
of the Bernoulli quadratic equation. -/
theorem bernoulliCumulantSeries_unique (t : ℝ) (G : PowerSeries ℝ)
    (hG0 : constantCoeff ℝ G = 0)
    (hG : G ^ 2 + (1 - X) * G - C ℝ t * X = 0) :
    G = bernoulliCumulantSeries t :=
  quadratic_zeroConstant_unique (by simp) hG0 (by simp) hG
    (bernoulliCumulantSeries_quadratic t)

/-- The degenerate Bernoulli law at zero has no positive cumulants. -/
@[simp] theorem bernoulliCumulantSeries_zero : bernoulliCumulantSeries 0 = 0 := by
  symm
  apply bernoulliCumulantSeries_unique
  · simp
  · simp

/-- The degenerate Bernoulli law at one has only its first cumulant. -/
@[simp] theorem bernoulliCumulantSeries_one : bernoulliCumulantSeries 1 = X := by
  symm
  apply bernoulliCumulantSeries_unique
  · simp
  · simp only [map_one]
    ring

/-- Every formal substitution preserves the quadratic relation, provided
it fixes the real coefficients. The construction of such substitutions is
independent of this algebraic lemma. -/
theorem bernoulliCumulantSeries_map_quadratic (t : ℝ)
    (F : PowerSeries ℝ →+* PowerSeries ℝ)
    (hC : F (C ℝ t) = C ℝ t) :
    F (bernoulliCumulantSeries t) ^ 2 +
      (1 - F X) * F (bernoulliCumulantSeries t) - C ℝ t * F X = 0 := by
  have h := congrArg F (bernoulliCumulantSeries_quadratic t)
  simpa only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, hC] using h

/-- Ordinary moments of the Bernoulli law: every positive moment is `t`. -/
def bernoulliMomentSeries (t : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => if n = 0 then 1 else t)

@[simp] theorem constantCoeff_bernoulliMomentSeries (t : ℝ) :
    constantCoeff ℝ (bernoulliMomentSeries t) = 1 := by
  simp [bernoulliMomentSeries]

theorem bernoulliMomentSeries_geometric (t : ℝ) :
    (1 - X) * bernoulliMomentSeries t = 1 + C ℝ (t - 1) * X := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero => simp [bernoulliMomentSeries]
  | succ n =>
    cases n with
    | zero => simp [bernoulliMomentSeries, coeff_X]
    | succ n => simp [bernoulliMomentSeries, coeff_X]

/-- The Bernoulli moment series satisfies the quadratic relation obtained
by substituting `X * M` into the cumulant equation. -/
theorem bernoulliMomentSeries_quadratic (t : ℝ) :
    (bernoulliMomentSeries t - 1) ^ 2 +
      (1 - X * bernoulliMomentSeries t) * (bernoulliMomentSeries t - 1) -
      C ℝ t * (X * bernoulliMomentSeries t) = 0 := by
  have h := congrArg (fun f : PowerSeries ℝ => bernoulliMomentSeries t * f)
    (bernoulliMomentSeries_geometric t)
  simp only [map_sub, map_one] at h
  linear_combination h

/-- Algebraic moment--cumulant identity for any valid formal substitution
of `X * M` into the cumulant series. -/
theorem bernoulliMomentSeries_substitution (t : ℝ)
    (F : PowerSeries ℝ →+* PowerSeries ℝ)
    (hC : F (C ℝ t) = C ℝ t)
    (hX : F X = X * bernoulliMomentSeries t)
    (hzero : constantCoeff ℝ (F (bernoulliCumulantSeries t)) = 0) :
    F (bernoulliCumulantSeries t) = bernoulliMomentSeries t - 1 := by
  apply quadratic_zeroConstant_unique (t := t) (W := X * bernoulliMomentSeries t)
  · simp
  · exact hzero
  · simp
  · simpa only [hX] using bernoulliCumulantSeries_map_quadratic t F hC
  · exact bernoulliMomentSeries_quadratic t

/-- Substitution of a zero-constant series into a univariate formal series.
Mathlib's multivariate substitution specializes to the one-element variable
type; no custom infinite-sum construction is necessary. -/
def formalSubst (W : PowerSeries ℝ) (hW : constantCoeff ℝ W = 0) :
    PowerSeries ℝ →ₐ[ℝ] PowerSeries ℝ :=
  MvPowerSeries.substAlgHom
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun _ : Unit => W)
      (fun _ => hW))

@[simp] theorem formalSubst_C (W : PowerSeries ℝ) (hW : constantCoeff ℝ W = 0)
    (t : ℝ) : formalSubst W hW (C ℝ t) = C ℝ t := by
  exact (formalSubst W hW).commutes t

@[simp] theorem formalSubst_X (W : PowerSeries ℝ) (hW : constantCoeff ℝ W = 0) :
    formalSubst W hW X = W := by
  exact MvPowerSeries.substAlgHom_X _ ()

theorem constantCoeff_formalSubst_of_zero (W : PowerSeries ℝ)
    (hW : constantCoeff ℝ W = 0) (G : PowerSeries ℝ)
    (hG : constantCoeff ℝ G = 0) :
    constantCoeff ℝ (formalSubst W hW G) = 0 := by
  obtain ⟨H, rfl⟩ := PowerSeries.X_dvd_iff.mpr hG
  simp [hW]

/-- The full formal Bernoulli moment--cumulant relation. -/
theorem bernoulliMomentSeries_cumulant_identity (t : ℝ) :
    formalSubst (X * bernoulliMomentSeries t) (by simp)
      (bernoulliCumulantSeries t) = bernoulliMomentSeries t - 1 := by
  apply bernoulliMomentSeries_substitution t
    (formalSubst (X * bernoulliMomentSeries t) (by simp)).toRingHom
  · exact formalSubst_C _ _ _
  · exact formalSubst_X _ _
  · apply constantCoeff_formalSubst_of_zero
    simp

/-- The formal moment--cumulant relation characterizes all Bernoulli moments,
not merely the already specified Bernoulli moment series. -/
theorem bernoulliMomentSeries_unique (t : ℝ) (M : PowerSeries ℝ)
    (hM0 : constantCoeff ℝ M = 1)
    (hM : formalSubst (X * M) (by simp) (bernoulliCumulantSeries t) = M - 1) :
    M = bernoulliMomentSeries t := by
  have hq := bernoulliCumulantSeries_map_quadratic t
    (formalSubst (X * M) (by simp)).toRingHom (formalSubst_C _ _ _)
  change (formalSubst (X * M) (by simp) (bernoulliCumulantSeries t)) ^ 2 +
      (1 - formalSubst (X * M) (by simp) X) *
        formalSubst (X * M) (by simp) (bernoulliCumulantSeries t) -
      C ℝ t * formalSubst (X * M) (by simp) X = 0 at hq
  rw [hM, formalSubst_X] at hq
  have hfactor : M * ((1 - X) * M - 1 - C ℝ (t - 1) * X) = 0 := by
    simp only [map_sub, map_one]
    linear_combination hq
  have hMn : M ≠ 0 := by
    intro h
    simp [h] at hM0
  have hg := (mul_eq_zero.mp hfactor).resolve_left hMn
  have hdiff : (1 - X) * (M - bernoulliMomentSeries t) = 0 := by
    have hb := bernoulliMomentSeries_geometric t
    linear_combination hg - hb
  have hXn : (1 - X : PowerSeries ℝ) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff ℝ) h
    simp at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hXn)

private theorem catalan_le_succ (n : ℕ) : catalan n ≤ catalan (n + 1) := by
  rw [catalan_succ]
  have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
    Nat.zero_le (catalan i.val * catalan (n - i.val))) (Finset.mem_univ (0 : Fin (n + 1)))
  simpa using h

private theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  rw [catalan_eq_centralBinom_div]
  apply (Nat.div_le_self _ _).trans
  cases n with
  | zero => simp [Nat.centralBinom]
  | succ n =>
    have h := (Nat.choose_le_two_pow (2 * (n + 1)) (n + 1) (by omega)).le
    simpa [Nat.centralBinom, pow_mul] using h

/-- A uniform Catalan majorant for the recursively defined coefficients. -/
theorem abs_bernoulliTail_le_catalan {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    |bernoulliTail t n| ≤ (2 : ℝ) ^ n * (catalan n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [bernoulliTail, abs_of_nonneg ht0] using ht1
    | succ n =>
      have hn := ih n (by omega)
      have hs :
          ∑ i : Fin (n + 1), |bernoulliTail t i.val * bernoulliTail t (n - i.val)| ≤
          (2 : ℝ) ^ n * (catalan (n + 1) : ℝ) := by
        calc
          _ ≤ ∑ i : Fin (n + 1),
                ((2 : ℝ) ^ i.val * (catalan i.val : ℝ)) *
                  ((2 : ℝ) ^ (n - i.val) * (catalan (n - i.val) : ℝ)) := by
                apply Finset.sum_le_sum
                intro i _
                rw [abs_mul]
                exact mul_le_mul (ih _ (by omega)) (ih _ (by omega))
                  (abs_nonneg _) (by positivity)
          _ = (2 : ℝ) ^ n * (catalan (n + 1) : ℝ) := by
                rw [catalan_succ, Nat.cast_sum, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                rw [Nat.cast_mul]
                have hi : i.val + (n - i.val) = n := by omega
                calc
                  _ = (2 : ℝ) ^ (i.val + (n - i.val)) *
                        ((catalan i.val : ℝ) * (catalan (n - i.val) : ℝ)) := by
                        rw [pow_add]
                        ring
                  _ = _ := by rw [hi]
      have hmono : (catalan n : ℝ) ≤ (catalan (n + 1) : ℝ) := by
        exact_mod_cast catalan_le_succ n
      calc
        |bernoulliTail t (n + 1)| ≤ |bernoulliTail t n| +
            ∑ i : Fin (n + 1),
              |bernoulliTail t i.val * bernoulliTail t (n - i.val)| := by
              rw [bernoulliTail]
              exact (abs_sub _ _).trans (add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _)
        _ ≤ (2 : ℝ) ^ n * (catalan n : ℝ) +
            (2 : ℝ) ^ n * (catalan (n + 1) : ℝ) := add_le_add hn hs
        _ ≤ (2 : ℝ) ^ (n + 1) * (catalan (n + 1) : ℝ) := by
              rw [pow_succ]
              nlinarith [mul_le_mul_of_nonneg_left hmono (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]

/-- An explicit exponential coefficient bound, enough for analytic evaluation
on a nonzero neighborhood of the origin. -/
theorem abs_bernoulliCumulant_succ_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    |bernoulliCumulant t (n + 1)| ≤ (8 : ℝ) ^ n := by
  have hc : (catalan n : ℝ) ≤ (4 : ℝ) ^ n := by
    exact_mod_cast catalan_le_four_pow n
  calc
    |bernoulliCumulant t (n + 1)| = |bernoulliTail t n| := rfl
    _ ≤ (2 : ℝ) ^ n * (catalan n : ℝ) := abs_bernoulliTail_le_catalan ht0 ht1 n
    _ ≤ (2 : ℝ) ^ n * (4 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg (by norm_num) _)
    _ = (8 : ℝ) ^ n := by rw [← mul_pow]; norm_num

theorem abs_bernoulliCumulant_mul_pow_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (z : ℝ) (n : ℕ) :
    |bernoulliCumulant t (n + 1) * z ^ (n + 1)| ≤ |z| * (8 * |z|) ^ n := by
  calc
    |bernoulliCumulant t (n + 1) * z ^ (n + 1)| =
        |bernoulliCumulant t (n + 1)| * |z| ^ (n + 1) := by rw [abs_mul, abs_pow]
    _ ≤ (8 : ℝ) ^ n * |z| ^ (n + 1) :=
      mul_le_mul_of_nonneg_right (abs_bernoulliCumulant_succ_le ht0 ht1 n) (by positivity)
    _ = |z| * (8 * |z|) ^ n := by rw [mul_pow, pow_succ]; ring

/-- The cumulant power series is absolutely convergent on `|z| < 1/8`. -/
theorem summable_abs_bernoulliCumulant {t z : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : |z| < 1 / 8) :
    Summable (fun n : ℕ => |bernoulliCumulant t n * z ^ n|) := by
  have hz8 : |8 * abs z| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hgeom := (summable_geometric_of_abs_lt_one hz8).mul_left |z|
  apply (summable_nat_add_iff 1).mp
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (abs_bernoulliCumulant_mul_pow_le ht0 ht1 z) hgeom

/-- An explicit bound for the absolute value series on the convergence disk. -/
theorem tsum_abs_bernoulliCumulant_le {t z : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : |z| < 1 / 8) :
    (∑' n : ℕ, |bernoulliCumulant t n * z ^ n|) ≤ |z| / (1 - 8 * |z|) := by
  have hz8 : |8 * abs z| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hs := summable_abs_bernoulliCumulant ht0 ht1 hz
  rw [hs.tsum_eq_zero_add]
  simp only [bernoulliCumulant_zero, zero_mul, abs_zero, zero_add]
  calc
    _ ≤ ∑' n : ℕ, |z| * (8 * |z|) ^ n :=
      Summable.tsum_le_tsum (abs_bernoulliCumulant_mul_pow_le ht0 ht1 z)
        ((summable_nat_add_iff 1).mpr hs)
        ((summable_geometric_of_abs_lt_one hz8).mul_left |z|)
    _ = |z| / (1 - 8 * |z|) := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hz8, div_eq_mul_inv]

#print axioms bernoulliCumulantSeries_quadratic
#print axioms bernoulliCumulantSeries_unique
#print axioms bernoulliMomentSeries_quadratic
#print axioms bernoulliMomentSeries_substitution
#print axioms bernoulliMomentSeries_cumulant_identity
#print axioms bernoulliMomentSeries_unique
#print axioms abs_bernoulliCumulant_succ_le
#print axioms summable_abs_bernoulliCumulant
#print axioms tsum_abs_bernoulliCumulant_le

end ProjectionChannels.FreeCumulant
