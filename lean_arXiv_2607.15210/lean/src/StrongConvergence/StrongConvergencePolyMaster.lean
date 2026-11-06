import StrongConvergence.StrongConvergencePolyInterpolation

/-! Uniform polynomial estimates from finite-rank samples and a quadratic
truncation error. These are the deterministic master inequalities used to
connect the genus expansion to smooth spectral tests. -/

open Polynomial Set
open scoped BigOperators

namespace ProjectionChannels.PolyChebyshev

theorem master_bound_of_truncation (k N₀ q D : ℕ)
    (G : Fin (D + 1) → Polynomial ℝ) (E : ℕ → ℕ → ℝ) {H : ℝ}
    (hk : 0 < k) (hN₀ : 3 ≤ N₀) (hH : 0 ≤ H)
    (hqN : 8 * q ^ 3 ≤ N₀) (hDN : 8 * k * D ^ 3 ≤ N₀)
    (hdegree : ∀ i, (G i).natDegree ≤ q)
    (hlinear : ∀ i, i.val = 1 → G i = 0)
    (hbounded : ∀ N : ℕ, k ∣ N → N₀ ≤ N → ∀ d : ℕ, d ≤ N → |E N d| ≤ H)
    (herror : ∀ N : ℕ, k ∣ N → N₀ ≤ N → ∀ d : ℕ, d ≤ N →
      |E N d - (xPolynomial G ((d : ℝ) / N)).eval (1 / (N : ℝ))| ≤ 5 * H / (N : ℝ) ^ 2)
    (N d : ℕ) (hdiv : k ∣ N) (hN : N₀ ≤ N) (hd : d ≤ N) :
    |E N d - (G 0).eval ((d : ℝ) / N)| ≤
      (128 * (D : ℝ) ^ 6 * (N₀ : ℝ) ^ 2 + 5) * H / (N : ℝ) ^ 2 := by
  have hN₀pos : 0 < N₀ := by omega
  have hN₀R : (0 : ℝ) < N₀ := by exact_mod_cast hN₀pos
  have hsamples : ∀ N : ℕ, k ∣ N → N₀ ≤ N → ∀ d : ℕ, d ≤ N →
      |(sPolynomial G (1 / (N : ℝ))).eval ((d : ℝ) / N)| ≤ 2 * H := by
    intro N hdiv hN d hd
    have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN₀.trans hN
    have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have hsmall : 5 * H / (N : ℝ) ^ 2 ≤ H := by
      apply (div_le_iff₀ hNsq).mpr
      nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : (5 : ℝ) ≤ (N : ℝ) ^ 2) hH]
    have he := herror N hdiv hN d hd
    have hb := hbounded N hdiv hN d hd
    have ht := abs_add
      ((xPolynomial G ((d : ℝ) / N)).eval (1 / (N : ℝ)) - E N d) (E N d)
    simp only [sub_add_cancel, abs_sub_comm] at ht
    rw [← xPolynomial_eval_eq_sPolynomial_eval]
    linarith
  have hNR : (0 : ℝ) < N := hN₀R.trans_le (by exact_mod_cast hN)
  have hinter := two_variable_interpolation k N₀ q D G hk hN₀pos hqN hDN hdegree hlinear
    hsamples
    (show (1 / (N : ℝ)) ∈ Icc (0 : ℝ) (1 / (N₀ : ℝ)) from
      ⟨(one_div_pos.mpr hNR).le, one_div_le_one_div_of_le hN₀R (by exact_mod_cast hN)⟩)
    (show (d : ℝ) / N ∈ Icc (0 : ℝ) 1 from
      ⟨div_nonneg (Nat.cast_nonneg _) hNR.le, (div_le_one hNR).mpr (by exact_mod_cast hd)⟩)
  have ht := abs_sub_le (E N d)
    ((xPolynomial G ((d : ℝ) / N)).eval (1 / (N : ℝ))) ((G 0).eval ((d : ℝ) / N))
  have he := herror N hdiv hN d hd
  calc
    _ ≤ 5 * H / (N : ℝ) ^ 2 +
        64 * (D : ℝ) ^ 6 * (N₀ : ℝ) ^ 2 * (2 * H) * (1 / (N : ℝ)) ^ 2 := by linarith
    _ = _ := by ring

#print axioms master_bound_of_truncation

/-- Explicit degree and output-dimension constants in the polynomial master
inequality. The approximation hypotheses are finite sample estimates. -/
theorem polynomial_master_inequality (k q : ℕ)
    (G : Fin (2 * q + 1) → Polynomial ℝ) (E : ℕ → ℕ → ℝ) {H : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hH : 0 ≤ H)
    (hdegree : ∀ i, (G i).natDegree ≤ q)
    (hlinear : ∀ i, i.val = 1 → G i = 0)
    (hbounded : ∀ N : ℕ, k ∣ N → 64 * k * q ^ 4 ≤ N →
      ∀ d : ℕ, d ≤ N → |E N d| ≤ H)
    (herror : ∀ N : ℕ, k ∣ N → 64 * k * q ^ 4 ≤ N → ∀ d : ℕ, d ≤ N →
      |E N d - (xPolynomial G ((d : ℝ) / N)).eval (1 / (N : ℝ))| ≤ 5 * H / (N : ℝ) ^ 2)
    (N d : ℕ) (hdiv : k ∣ N) (hN : 64 * k * q ^ 4 ≤ N) (hd : d ≤ N) :
    |E N d - (G 0).eval ((d : ℝ) / N)| ≤
      (2 : ℝ) ^ 26 * (k : ℝ) ^ 2 * (q : ℝ) ^ 14 * H / (N : ℝ) ^ 2 := by
  have hk1 : 1 ≤ k := hk
  have hq1 : 1 ≤ q := hq
  have hq4 : 1 ≤ q ^ 4 := one_le_pow₀ hq1
  have h34 : q ^ 3 ≤ q ^ 4 := by
    calc
      q ^ 3 = q ^ 3 * 1 := by simp
      _ ≤ q ^ 3 * q := Nat.mul_le_mul_left _ hq1
      _ = q ^ 4 := by ring
  have hN₀ : 3 ≤ 64 * k * q ^ 4 := by
    nlinarith [Nat.mul_le_mul_left (64 * q ^ 4) hk1]
  have hqN : 8 * q ^ 3 ≤ 64 * k * q ^ 4 := by
    nlinarith [Nat.mul_le_mul_left (64 * q ^ 4) hk1]
  have hDN : 8 * k * (2 * q) ^ 3 ≤ 64 * k * q ^ 4 := by
    nlinarith [Nat.mul_le_mul_left (64 * k) h34]
  have h := master_bound_of_truncation k (64 * k * q ^ 4) q (2 * q) G E
    hk hN₀ hH hqN hDN hdegree hlinear hbounded herror N d hdiv hN hd
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hprod : (1 : ℝ) ≤ (k : ℝ) ^ 2 * (q : ℝ) ^ 14 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hkR) (one_le_pow₀ hqR)
  have hconst : 128 * ((2 * q : ℕ) : ℝ) ^ 6 * ((64 * k * q ^ 4 : ℕ) : ℝ) ^ 2 + 5 ≤
      (2 : ℝ) ^ 26 * (k : ℝ) ^ 2 * (q : ℝ) ^ 14 := by
    have heq : 128 * ((2 * q : ℕ) : ℝ) ^ 6 * ((64 * k * q ^ 4 : ℕ) : ℝ) ^ 2 =
        (2 : ℝ) ^ 25 * (k : ℝ) ^ 2 * (q : ℝ) ^ 14 := by push_cast; ring
    rw [heq]
    norm_num
    nlinarith
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hconst hH) (sq_nonneg (N : ℝ)))

#print axioms polynomial_master_inequality

end ProjectionChannels.PolyChebyshev
