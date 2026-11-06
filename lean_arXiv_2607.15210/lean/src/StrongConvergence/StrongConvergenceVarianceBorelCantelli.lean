import StrongConvergence.StrongConvergenceProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.PSeries

/-! A summable bound for squared deviations implies almost-sure convergence.
The variance bound is an explicit hypothesis, to be supplied by an actual
random-matrix calculation.  Neither independence nor a concentration theorem
is assumed. -/

open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

namespace StrongConvergenceVarianceBorelCantelli

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
lemma tail_measure_le_sq_integral (f : Ω → ℝ)
    (hf : Integrable (fun ω => (f ω)^2) μ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |f ω|} ≤ (∫ ω, (f ω)^2 ∂μ) / ε^2 := by
  have hset : {ω | ε ≤ |f ω|} = {ω | ε^2 ≤ (f ω)^2} := by
    ext ω
    change ε ≤ |f ω| ↔ ε^2 ≤ (f ω)^2
    constructor
    · intro h
      nlinarith [sq_abs (f ω), sq_nonneg (|f ω|-ε)]
    · intro h
      by_contra hn
      have hn' : |f ω| < ε := lt_of_not_ge hn
      nlinarith [sq_abs (f ω), abs_nonneg (f ω)]
  rw [hset]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  simpa only [mul_comm] using mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => sq_nonneg (f ω))) hf (ε^2)

lemma summable_shifted_inverse_square :
    Summable (fun n : ℕ => 1 / ((n:ℝ)+1)^2) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))

lemma tsum_tail_ne_top_of_eventually_sq_integral_le (F : Ω → ℕ → ℝ)
    (c : ℕ → ℝ) (C : ℝ)
    (hint : ∀ n, Integrable (fun ω => (F ω n-c n)^2) μ)
    (hbound : ∀ᶠ n in atTop, (∫ ω, (F ω n-c n)^2 ∂μ) ≤ C/((n:ℝ)+1)^2)
    {ε : ℝ} (hε : 0 < ε) :
    (∑' n, μ {ω | ε ≤ |F ω n-c n|}) ≠ ∞ := by
  have hs : Summable (fun n : ℕ => μ.real {ω | ε ≤ |F ω n-c n|}) := by
    apply Summable.of_norm_bounded_eventually_nat
      (fun n : ℕ => (C/ε^2) * (1/((n:ℝ)+1)^2))
      (summable_shifted_inverse_square.mul_left _)
    filter_upwards [hbound] with n hn
    rw [Real.norm_of_nonneg measureReal_nonneg]
    calc
      μ.real {ω | ε ≤ |F ω n-c n|} ≤ (∫ ω, (F ω n-c n)^2 ∂μ)/ε^2 :=
        tail_measure_le_sq_integral _ (hint n) hε
      _ ≤ (C/((n:ℝ)+1)^2)/ε^2 :=
        div_le_div_of_nonneg_right hn (sq_nonneg ε)
      _ = _ := by ring
  have hconvert : (fun n => μ {ω | ε ≤ |F ω n-c n|}) =
      (fun n => ENNReal.ofReal (μ.real {ω | ε ≤ |F ω n-c n|})) := by
    funext n
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hconvert, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hs]
  exact ENNReal.ofReal_ne_top

theorem ae_tendsto_of_eventually_sq_integral_le (F : Ω → ℕ → ℝ)
    (c : ℕ → ℝ) (L C : ℝ)
    (hcenter : Tendsto c atTop (𝓝 L))
    (hint : ∀ n, Integrable (fun ω => (F ω n-c n)^2) μ)
    (hbound : ∀ᶠ n in atTop, (∫ ω, (F ω n-c n)^2 ∂μ) ≤ C/((n:ℝ)+1)^2) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => F ω n) atTop (𝓝 L) := by
  have h := StrongConvergenceProbability.ae_countable_tendsto_of_centered_tails μ
    (fun ω n (_ : Unit) => F ω n) (fun n (_ : Unit) => c n)
    (fun (_ : Unit) => L) (fun _ => hcenter) (by
      intro _ m
      exact tsum_tail_ne_top_of_eventually_sq_integral_le F c C hint hbound (by positivity))
  filter_upwards [h] with ω hω
  exact hω ()

end StrongConvergenceVarianceBorelCantelli

#print axioms StrongConvergenceVarianceBorelCantelli.ae_tendsto_of_eventually_sq_integral_le
