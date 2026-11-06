import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Direct summation of polynomial master estimates for smooth spectral tests. -/
open scoped BigOperators
noncomputable section
namespace StrongConvergence

/-- A degree threshold can be removed term by term by using the trivial bound
on the remaining terms. No integer cutoff or floor estimate is required. -/
lemma master_bound_all_degrees {A B C N w : ℝ}
    (hC : 0 ≤ C) (hN : 0 < N) (hw : 0 ≤ w)
    (hA : |A| ≤ 1) (hB : |B| ≤ 1)
    (hmaster : C*w^4 ≤ N → |A-B| ≤ C*w^14/N^2) :
    |A-B| ≤ (C*w^14 + 2*C^2*w^8)/N^2 := by
  by_cases h : C*w^4 ≤ N
  · exact (hmaster h).trans ((div_le_div_iff_of_pos_right (sq_pos_of_pos hN)).mpr
      (le_add_of_nonneg_right (by positivity)))
  · have hn : N < C*w^4 := lt_of_not_ge h
    have hs : N^2 ≤ C^2*w^8 := by nlinarith [sq_nonneg (C*w^4-N)]
    have hab := (abs_sub A B).trans (add_le_add hA hB)
    apply hab.trans
    apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
    nlinarith [mul_nonneg hC (pow_nonneg hw 14)]

/-- An `N⁻²` master estimate with degree power 14 extends to every series
whose coefficient weights of orders 8 and 14 are summable. -/
theorem smooth_series_master_bound {ι : Type*}
    (c A B w : ι → ℝ) {C N : ℝ} (hC : 0 ≤ C) (hN : 0 < N)
    (hw : ∀ i, 1 ≤ w i)
    (hc8 : Summable (fun i => |c i| *(w i)^8))
    (hc14 : Summable (fun i => |c i| *(w i)^14))
    (hA : ∀ i, |A i| ≤ 1) (hB : ∀ i, |B i| ≤ 1)
    (hmaster : ∀ i, C*(w i)^4 ≤ N → |A i-B i| ≤ C*(w i)^14/N^2) :
    |(∑' i, c i*A i) - ∑' i, c i*B i| ≤
      (C*(∑' i, |c i| *(w i)^14) + 2*C^2*(∑' i, |c i| *(w i)^8))/N^2 := by
  have hc : Summable (fun i => |c i|) := by
    apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ hc8
    intro i
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ (hw i)) (abs_nonneg (c i))
  have ha : Summable (fun i => c i*A i) := by
    apply Summable.of_norm_bounded _ hc
    intro i
    simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (hA i) (abs_nonneg (c i))
  have hb : Summable (fun i => c i*B i) := by
    apply Summable.of_norm_bounded _ hc
    intro i
    simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (hB i) (abs_nonneg (c i))
  let R : ι → ℝ := fun i => (C*(|c i| *(w i)^14) + 2*C^2*(|c i| *(w i)^8))/N^2
  have hr : Summable R := ((hc14.mul_left C).add (hc8.mul_left (2*C^2))).div_const _
  have hterm : ∀ i, |c i*A i-c i*B i| ≤ R i := by
    intro i
    rw [← mul_sub, abs_mul]
    have hh := mul_le_mul_of_nonneg_left
      (master_bound_all_degrees hC hN (zero_le_one.trans (hw i)) (hA i) (hB i) (hmaster i))
      (abs_nonneg (c i))
    convert hh using 1
    dsimp [R]
    ring
  rw [← ha.tsum_sub hb]
  have hn := (ha.sub hb).hasSum.norm_le_of_bounded hr.hasSum
    (fun i => by simpa only [Real.norm_eq_abs] using hterm i)
  rw [Real.norm_eq_abs] at hn
  apply hn.trans_eq
  dsimp only [R]
  rw [tsum_div_const, Summable.tsum_add (hc14.mul_left C) (hc8.mul_left (2*C^2)),
    tsum_mul_left, tsum_mul_left]


open MeasureTheory Filter

/-- A bounded pointwise series may be integrated term by term. Applied to
Chebyshev spectral tests, the dominating series is just `Σ |c_i|`. -/
theorem hasSum_integrals_of_bounded_expansion
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ι → ℝ) (A : ι → Ω → ℝ) (F : Ω → ℝ)
    (hc : Summable (fun i => |c i|))
    (hA : ∀ i, AEStronglyMeasurable (A i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |A i ω| ≤ 1)
    (hexp : ∀ᵐ ω ∂μ, HasSum (fun i => c i * A i ω) (F ω)) :
    HasSum (fun i => c i * ∫ ω, A i ω ∂μ) (∫ ω, F ω ∂μ) := by
  have h := hasSum_integral_of_dominated_convergence
    (μ := μ) (F := fun i ω => c i * A i ω) (f := F)
    (fun i _ => |c i|) (fun i => (hA i).const_mul (c i))
    (fun i => (hbound i).mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hω (abs_nonneg (c i)))
    (Eventually.of_forall fun _ => hc) (integrable_const _) hexp
  simpa only [integral_const_mul] using h

#print axioms hasSum_integrals_of_bounded_expansion
#print axioms smooth_series_master_bound
end StrongConvergence
