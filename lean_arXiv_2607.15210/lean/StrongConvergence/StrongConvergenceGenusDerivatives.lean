import StrongConvergence.StrongConvergenceGenusLimitTests
import StrongConvergence.StrongConvergencePolyMarkov
import StrongConvergence.StrongConvergencePositiveQuadratic

/-! Density derivatives of the actual genus-zero moment functional. -/
open Polynomial Set
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar PolyChebyshev

theorem testRankCoefficient_zero_derivative_abs_le {k q : ℕ}
    (hk : 0<k) (a : Fin k → ℝ) (p : ℝ[X]) (hp : p.natDegree≤q)
    {K H : ℝ} (hK : (∑ i, |a i|)≤K)
    (hb : ∀ x ∈ Icc (-K) K, |p.eval x|≤H)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    |(testRankCoefficient k q a p 0).derivative.eval t| ≤ 4*(q:ℝ)^3*H := by
  simpa only [div_one] using polynomial_markov_bound (testRankCoefficient k q a p 0) q
    (by norm_num : (0:ℝ)<1) (testRankCoefficient_natDegree_le a p 0)
    (fun x hx => testRankCoefficient_zero_abs_le hk a p hp hK hb hx) ht

theorem testRankCoefficient_zero_second_derivative_abs_le {k q : ℕ}
    (hk : 0<k) (a : Fin k → ℝ) (p : ℝ[X]) (hp : p.natDegree≤q)
    {K H : ℝ} (hK : (∑ i, |a i|)≤K)
    (hb : ∀ x ∈ Icc (-K) K, |p.eval x|≤H)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    |(testRankCoefficient k q a p 0).derivative.derivative.eval t| ≤
      16*(q:ℝ)^6*H := by
  have hd := (natDegree_derivative_le (testRankCoefficient k q a p 0)).trans
    ((Nat.sub_le _ _).trans (testRankCoefficient_natDegree_le a p 0))
  have h := polynomial_markov_bound (testRankCoefficient k q a p 0).derivative q
    (by norm_num : (0:ℝ)<1) hd
    (fun x hx => testRankCoefficient_zero_derivative_abs_le hk a p hp hK hb hx) ht
  convert h using 1
  ring

theorem testRankCoefficient_zero_quadratic_remainder {k q : ℕ}
    (hk : 0<k) (a : Fin k → ℝ) (p : ℝ[X]) (hp : p.natDegree≤q)
    {K H : ℝ} (hK : (∑ i, |a i|)≤K)
    (hb : ∀ x ∈ Icc (-K) K, |p.eval x|≤H)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    |(testRankCoefficient k q a p 0).eval s -
      (testRankCoefficient k q a p 0).eval t -
      (testRankCoefficient k q a p 0).derivative.eval t*(s-t)| ≤
      16*(q:ℝ)^6*H*(s-t)^2 := by
  have hK0 : 0≤K := (Finset.sum_nonneg (fun i _ => abs_nonneg (a i))).trans hK
  have hH : 0≤H := (abs_nonneg (p.eval 0)).trans (hb 0 ⟨by linarith, hK0⟩)
  exact StrongConvergence.polynomial_abs_quadratic_remainder_le _ (by positivity)
    (fun x hx => testRankCoefficient_zero_second_derivative_abs_le hk a p hp hK hb hx) ht hs

/-- B6 for a summable polynomial expansion of a nonnegative smooth test. All
density derivative bounds come from the actual genus-zero functional. -/
theorem genus_polynomial_series_le_quadratic {ι : Type*} {k : ℕ}
    (hk : 0<k) (a : Fin k → ℝ) (q : ι → ℕ) (p : ι → ℝ[X])
    (hp : ∀ i, (p i).natDegree≤q i) {K : ℝ} (hK : (∑ i, |a i|)≤K)
    (hb : ∀ i x, x∈Icc (-K) K → |(p i).eval x|≤1)
    (c : ι → ℝ) (hc3 : Summable (fun i => |c i| *(q i:ℝ)^3))
    (hc6 : Summable (fun i => |c i| *(q i:ℝ)^6))
    {f : ℝ → ℝ}
    (hvalues : ∀ s∈Icc (0:ℝ) 1,
      HasSum (fun i => c i*(testRankCoefficient k (q i) a (p i) 0).eval s) (f s))
    (hf : ∀ s∈Icc (0:ℝ) 1, 0≤f s) {t : ℝ}
    (ht0 : 0<t) (ht1 : t<1) (hft : f t=0)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    f s ≤ (16*∑' i, |c i| *(q i:ℝ)^6)*(s-t)^2 := by
  have hlinear : Summable (fun i => c i*
      (testRankCoefficient k (q i) a (p i) 0).derivative.eval t) := by
    apply Summable.of_norm_bounded (fun i => 4*(|c i| *(q i:ℝ)^3)) (hc3.mul_left 4)
    intro i
    rw [Real.norm_eq_abs, abs_mul]
    have hd := testRankCoefficient_zero_derivative_abs_le hk a (p i) (hp i) hK
      (hb i) ⟨ht0.le,ht1.le⟩
    calc
      _ ≤ |c i| *(4*(q i:ℝ)^3*1) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = _ := by ring
  apply StrongConvergence.polynomial_series_le_quadratic_of_nonneg
    (P := fun i => testRankCoefficient k (q i) a (p i) 0)
    (B := fun i => 16*(q i:ℝ)^6) ht0 ht1 (fun i => by positivity)
    hvalues hlinear.hasSum
  · convert hc6.hasSum.mul_left 16 using 1
    ext i
    ring
  · intro i x hx
    simpa only [mul_one] using
      testRankCoefficient_zero_second_derivative_abs_le hk a (p i) (hp i) hK (hb i) hx
  · exact hf
  · exact hft
  · exact hs

#print axioms genus_polynomial_series_le_quadratic
end ProjectionChannels.Canonical
