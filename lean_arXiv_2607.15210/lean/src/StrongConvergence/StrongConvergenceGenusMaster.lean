import StrongConvergence.StrongConvergenceGenusTestBound
import StrongConvergence.StrongConvergencePolyMaster

/-! The polynomial master inequality for the actual canonical Haar ensemble. -/
open Polynomial Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar PolyChebyshev

lemma master_dimension_index {k q N : ℕ} (hk : 0<k) (hq : 0<q)
    (hdiv : k ∣ N) (hN : 64*k*q^4≤N) :
    (N/k-1+1)*k=N ∧ q≤N/k-1+1 := by
  have hq4 : q≤q^4 := by
    simpa using Nat.pow_le_pow_right hq (by decide : 1≤4)
  have hqN : q*k≤N := by
    have hm := Nat.mul_le_mul_left k hq4
    nlinarith
  have hqd : q≤N/k := (Nat.le_div_iff_mul_le hk).mpr hqN
  have hd : 1≤N/k := hq.trans_le hqd
  rw [Nat.sub_add_cancel hd]
  exact ⟨Nat.div_mul_cancel hdiv, hqd⟩

lemma spectralTest_congr_rank (k : ℕ) (t s : ℝ) (a : Fin k → ℝ) (n : ℕ)
    (hr : rankSequence k t n = rankSequence k s n) (f : ℝ → ℝ) (sample : Sample k) :
    spectralTest k t a n f sample = spectralTest k s a n f sample := by
  unfold spectralTest
  congr 2
  simp only [projection, baseProjection, hr]

/-- The actual expected polynomial trace at a rank-grid point. -/
def expectedRankTest (k : ℕ) (a : Fin k → ℝ) (p : ℝ[X]) (N d : ℕ) : ℝ :=
  ∫ sample, spectralTest k ((d:ℝ)/N) a (N/k-1) p.eval sample ∂probability k

theorem expectedRankTest_truncation_error {k q N : ℕ}
    (hk : 0<k) (hq : 0<q) (hdiv : k ∣ N) (hN : 64*k*q^4≤N)
    (a : Fin k → ℝ) (p : ℝ[X]) (hdeg : p.natDegree≤q) {H : ℝ}
    (hb : ∀ x ∈ Icc (-(∑ i, |a i|)) (∑ i, |a i|), |p.eval x|≤H)
    (d : ℕ) (hd : d≤N) :
    |expectedRankTest k a p N d -
      (xPolynomial (fun i : Fin (2*q+1) => testRankCoefficient k q a p i.val)
        ((d:ℝ)/N)).eval (1/(N:ℝ))| ≤ 5*H/(N:ℝ)^2 := by
  obtain ⟨hindex,hqn⟩ := master_dimension_index hk hq hdiv hN
  have hNp : 0<N := by rw [← hindex]; positivity
  have hNR : (0:ℝ)<N := by exact_mod_cast hNp
  have ht0 : 0≤(d:ℝ)/N := by positivity
  have ht1 : (d:ℝ)/N≤1 := (div_le_one hNR).mpr (by exact_mod_cast hd)
  have hN' : 8*q^4≤(N/k-1+1)*k := by
    rw [hindex]
    nlinarith [Nat.mul_le_mul_left (64*q^4) hk]
  have h := expected_polynomial_truncation_error hk ht0 ht1 (N/k-1) q hq hqn
    a p hdeg hb hN'
  rw [hindex] at h
  have hr : rankSequence k ((d:ℝ)/N) (N/k-1)=d := by
    simpa only [hindex] using rankSequence_exact_density hk (N/k-1) d
  simpa only [hr, one_div, expectedRankTest] using h

/-- B4: a uniform inverse-square estimate for arbitrary polynomial spectral
tests of the canonical Haar compression, at every integer rank. -/
theorem expectedRankTest_master_bound {k q : ℕ}
    (hk : 0<k) (hq : 0<q) (a : Fin k → ℝ) (p : ℝ[X])
    (hdeg : p.natDegree≤q) {H : ℝ}
    (hb : ∀ x ∈ Icc (-(∑ i, |a i|)) (∑ i, |a i|), |p.eval x|≤H)
    (N d : ℕ) (hdiv : k ∣ N) (hN : 64*k*q^4≤N) (hd : d≤N) :
    |expectedRankTest k a p N d - (testRankCoefficient k q a p 0).eval ((d:ℝ)/N)| ≤
      (2:ℝ)^26*(k:ℝ)^2*(q:ℝ)^14*H/(N:ℝ)^2 := by
  have hK : 0≤∑ i, |a i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hH : 0≤H := (abs_nonneg (p.eval 0)).trans (hb 0 ⟨by linarith, hK⟩)
  apply polynomial_master_inequality k q
    (fun i : Fin (2*q+1) => testRankCoefficient k q a p i.val)
    (expectedRankTest k a p) hk hq hH
  · intro i
    exact testRankCoefficient_natDegree_le a p i.val
  · intro i hi
    rw [hi]
    exact testRankCoefficient_odd a p 1 rfl
  · intro N hdiv hN d hd
    exact expected_spectralTest_abs_le k ((d:ℝ)/N) a (N/k-1) le_rfl hb
  · intro N hdiv hN d hd
    exact expectedRankTest_truncation_error hk hq hdiv hN a p hdeg hb d hd
  · exact hdiv
  · exact hN
  · exact hd

/-- B4 in the original density parameter, with the exact floor-rounded rank
appearing in the leading polynomial. -/
theorem expected_spectralTest_master_bound {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0≤t) (ht1 : t≤1) (n q : ℕ) (hq : 0<q)
    (a : Fin k → ℝ) (p : ℝ[X]) (hdeg : p.natDegree≤q) {H : ℝ}
    (hb : ∀ x ∈ Icc (-(∑ i, |a i|)) (∑ i, |a i|), |p.eval x|≤H)
    (hN : 64*k*q^4≤(n+1)*k) :
    |(∫ sample, spectralTest k t a n p.eval sample ∂probability k) -
      (testRankCoefficient k q a p 0).eval
        ((rankSequence k t n:ℝ)/(((n+1)*k:ℕ):ℝ))| ≤
      (2:ℝ)^26*(k:ℝ)^2*(q:ℝ)^14*H/((((n+1)*k:ℕ):ℝ)^2) := by
  have hd : rankSequence k t n≤(n+1)*k := by
    simpa only [Index, Fintype.card_prod, Fintype.card_fin] using rankSequence_le ht0 ht1 n
  have h := expectedRankTest_master_bound hk hq a p hdeg hb ((n+1)*k)
    (rankSequence k t n) (dvd_mul_left k (n+1)) hN hd
  have hindex : (n+1)*k/k-1=n := by rw [Nat.mul_div_cancel _ hk]; omega
  unfold expectedRankTest at h
  rw [hindex] at h
  have hr := rankSequence_exact_density hk n (rankSequence k t n)
  have he : (∫ sample, spectralTest k
      ((rankSequence k t n:ℝ)/(((n+1)*k:ℕ):ℝ)) a n p.eval sample ∂probability k) =
      ∫ sample, spectralTest k t a n p.eval sample ∂probability k := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun sample =>
      spectralTest_congr_rank k _ _ a n hr _ sample
  rwa [he] at h

#print axioms expected_spectralTest_master_bound
end ProjectionChannels.Canonical
