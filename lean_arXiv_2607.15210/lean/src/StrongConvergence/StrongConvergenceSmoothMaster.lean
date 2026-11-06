import StrongConvergence.StrongConvergenceSmoothLimit
import StrongConvergence.StrongConvergenceRankDensityBound

open MeasureTheory Filter Set Polynomial
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar

/-- The finite constant controlling the smooth-test approximation. -/
def smoothMasterConstant (k : ℕ) (c : ℤ → ℝ) : ℝ :=
  ((2:ℝ)^26*(k:ℝ)^2) * (∑'j, |c j| *(|(j:ℝ)|+1)^14) +
  2*((2:ℝ)^26*(k:ℝ)^2)^2 * (∑'j, |c j| *(|(j:ℝ)|+1)^8)

/-- The actual expected smooth spectral test differs from its genus-zero
functional at the exact floor density by a uniform inverse-square error. -/
theorem expected_spectralTest_smooth_master_bound {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht : t ∈ Icc (0:ℝ) 1) (a : Fin k → ℝ)
    {K : ℝ} (hK : 0<K) (hKa : (∑i, |a i|)≤K)
    (c : ℤ → ℝ) (χ : ℝ → ℝ)
    (hc : ∀p : ℕ, Summable (fun j => |c j| *(|(j:ℝ)|+1)^p))
    (hexp : ∀x ∈ Icc (-K) K, HasSum
      (fun j => c j*(scaledChebyshev K j).eval x) (χ x)) (n : ℕ) :
    |(∫sample, spectralTest k t a n χ sample ∂probability k) -
      smoothGenusValue k a K c ((rankSequence k t n:ℝ)/(((n+1)*k:ℕ):ℝ))| ≤
      smoothMasterConstant k c/((((n+1)*k:ℕ):ℝ)^2) := by
  let C : ℝ := (2:ℝ)^26*(k:ℝ)^2
  let N : ℝ := (((n+1)*k:ℕ):ℝ)
  have hN : 0<N := by dsimp [N]; exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hk
  have hC : 0≤C := by dsimp [C]; positivity
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hC64 : (64:ℝ)*k≤C := by dsimp [C]; nlinarith [sq_nonneg ((k:ℝ)-1)]
  have hcast (j : ℤ) : ((j.natAbs+1:ℕ):ℝ)=|(j:ℝ)|+1 := by
    simp only [Nat.cast_add, Nat.cast_one, Int.cast_natAbs, Int.cast_abs]
  have hc0 : Summable (fun j => |c j|) := by simpa using hc 0
  have he := expected_spectralTest_chebyshev_hasSum k t a n hK hKa c χ hc0 hexp
  rw [← he.tsum_eq]
  apply StrongConvergence.smooth_series_master_bound c
    (fun j => ∫sample, spectralTest k t a n (scaledChebyshev K j).eval sample ∂probability k)
    (fun j => (testRankCoefficient k (j.natAbs+1) a (scaledChebyshev K j) 0).eval
      ((rankSequence k t n:ℝ)/N))
    (fun j => |(j:ℝ)|+1) hC hN (fun j => by change 1 ≤ |(j:ℝ)|+1; linarith [abs_nonneg (j:ℝ)]) (hc 8) (hc 14)
  · intro j
    exact expected_spectralTest_abs_le k t a n hKa
      (fun x hx => scaledChebyshev_abs_le hK hx j)
  · intro j
    exact scaledChebyshev_genus_abs_le hk a hK hKa j
      (rankSequence_density_mem_Icc hk ht.1 ht.2 n)
  · intro j hj
    have hthreshold : 64*k*(j.natAbs+1)^4≤(n+1)*k := by
      have hl := mul_le_mul_of_nonneg_right hC64 (pow_nonneg (show 0≤|(j:ℝ)|+1 by positivity) 4)
      have hh : (64:ℝ)*k*(|(j:ℝ)|+1)^4≤N := hl.trans hj
      rw [← hcast j] at hh
      dsimp [N] at hh
      exact_mod_cast hh
    have hm := expected_spectralTest_master_bound hk ht.1 ht.2 n (j.natAbs+1)
      (by omega) a (scaledChebyshev K j) (scaledChebyshev_natDegree_le_succ K j)
      (H := 1) (fun x hx => scaledChebyshev_abs_le hK
        ⟨by linarith [hx.1], hx.2.trans hKa⟩ j) hthreshold
    simpa only [hcast, mul_one] using hm

#print axioms expected_spectralTest_smooth_master_bound
end ProjectionChannels.Canonical
