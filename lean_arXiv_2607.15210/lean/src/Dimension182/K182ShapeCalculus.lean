import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Elementary support for the final draft's one-high minimizer argument.

This file proves the numerical hypotheses and the strict monotonicity used
in Step 4. It does NOT formalize the zero-coordinate perturbation, KKT
multiplier argument, or constrained second-order necessary condition.
Consequently this file does not discharge `HasOneHighEntropyMinimizer`
in the separate K182Entropy development.
-/

namespace ProjectionChannels.K182ShapeCalculus
noncomputable section

/-- The exact parameters in the paper satisfy all numerical hypotheses of
the one-high minimizer lemma. -/
theorem reduction_hypotheses :
    (1 : ℝ) / (182 * 181) < 27 / 100000 ∧
    (27 : ℝ) / 100000 < 1 - 1 / 182 ∧
    (Real.sqrt ((27 : ℝ) / 100000 * (1 - 1 / 182)) +
      Real.sqrt ((1 - (27 : ℝ) / 100000) / 182)) ^ 2 < 1 / 4 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have h₁ : Real.sqrt ((27 : ℝ) / 100000 * (1 - 1 / 182)) ≤ 17 / 1000 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num
  have h₂ : Real.sqrt ((1 - (27 : ℝ) / 100000) / 182) ≤ 75 / 1000 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num
  have h₁₀ := Real.sqrt_nonneg ((27 : ℝ) / 100000 * (1 - 1 / 182))
  have h₂₀ := Real.sqrt_nonneg ((1 - (27 : ℝ) / 100000) / 182)
  nlinarith only [h₁, h₂, h₁₀, h₂₀]

/-- Squaring the positive denominator in the derivative test reduces
its strict monotonicity to this polynomial inequality. -/
theorem denominator_sq_strictMono :
    StrictMonoOn (fun v : ℝ => v * (1 - v) ^ 3) (Set.Ioo 0 (1 / 4)) := by
  intro a ha b hb hab
  let x : ℝ := 1 / 4 - a
  let y : ℝ := 1 / 4 - b
  have hx : 0 < x := by dsimp [x]; linarith only [ha.2]
  have hy : 0 < y := by dsimp [y]; linarith only [hb.2]
  have hxy : 0 < x - y := by dsimp [x, y]; linarith only [hab]
  have hfactor :
      b * (1 - b) ^ 3 - a * (1 - a) ^ 3 =
      (x - y) * ((9 / 8 : ℝ) * (x + y) +
        2 * (x ^ 2 + x * y + y ^ 2) +
        (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)) := by
    dsimp [x, y]
    ring
  have hrhs : 0 < (x - y) * ((9 / 8 : ℝ) * (x + y) +
      2 * (x ^ 2 + x * y + y ^ 2) +
      (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)) := by positivity
  change a * (1 - a) ^ 3 < b * (1 - b) ^ 3
  exact sub_pos.mp (hfactor.symm ▸ hrhs)

/-- The denominator `sqrt(v (1-v)^3)` increases strictly on `(0,1/4)`.
It equals the paper's `sqrt(v) (1-v)^(3/2)` in this interval. -/
theorem denominator_strictMono :
    StrictMonoOn (fun v : ℝ => Real.sqrt (v * (1 - v) ^ 3))
      (Set.Ioo 0 (1 / 4)) := by
  intro a ha b hb hab
  apply Real.sqrt_lt_sqrt
  · have h : 0 < 1 - a := by linarith only [ha.2]
    exact mul_nonneg ha.1.le (pow_nonneg h.le _)
  · exact denominator_sq_strictMono ha hb hab

/-- The second-variation contradiction used for a repeated high coordinate.
Here `d` is the already-computed derivative `f_mu'(b)`, which is positive. -/
theorem negative_second_variation {s d : ℝ} (hs : 0 < s) (hd : 0 < d) :
    -(2 / s) * d < 0 := by
  have h : 0 < (2 / s) * d := mul_pos (div_pos (by norm_num) hs) hd
  nlinarith only [h]

#print axioms reduction_hypotheses
#print axioms denominator_sq_strictMono
#print axioms denominator_strictMono
#print axioms negative_second_variation

end
end ProjectionChannels.K182ShapeCalculus
