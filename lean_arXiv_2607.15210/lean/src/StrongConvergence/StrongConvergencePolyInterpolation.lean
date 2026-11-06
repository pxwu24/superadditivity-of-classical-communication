import StrongConvergence.StrongConvergencePolyMarkov
import StrongConvergence.StrongConvergencePolyMeshes

/-! The deterministic two-variable interpolation step of the polynomial method. -/

open Polynomial Set
open scoped BigOperators

namespace ProjectionChannels.PolyChebyshev

noncomputable def xPolynomial {D : ℕ} (G : Fin (D + 1) → Polynomial ℝ) (s : ℝ) :
    Polynomial ℝ := ∑ i, C ((G i).eval s) * X ^ i.val

noncomputable def sPolynomial {D : ℕ} (G : Fin (D + 1) → Polynomial ℝ) (x : ℝ) :
    Polynomial ℝ := ∑ i, x ^ i.val • G i

theorem xPolynomial_eval_eq_sPolynomial_eval {D : ℕ}
    (G : Fin (D + 1) → Polynomial ℝ) (x s : ℝ) :
    (xPolynomial G s).eval x = (sPolynomial G x).eval s := by
  unfold xPolynomial sPolynomial
  rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_mul, eval_C, eval_pow, eval_X, eval_smul]
  change (G i).eval s * x ^ i.val = x ^ i.val * (G i).eval s
  ring

theorem xPolynomial_natDegree_le {D : ℕ} (G : Fin (D + 1) → Polynomial ℝ) (s : ℝ) :
    (xPolynomial G s).natDegree ≤ D := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  rw [C_mul_X_pow_eq_monomial]
  exact (natDegree_monomial_le _).trans (by omega)

theorem sPolynomial_natDegree_le {D q : ℕ} (G : Fin (D + 1) → Polynomial ℝ)
    (hG : ∀ i, (G i).natDegree ≤ q) (x : ℝ) :
    (sPolynomial G x).natDegree ≤ q := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_smul_le _ _).trans (hG i)

@[simp] theorem xPolynomial_eval_zero {D : ℕ} (G : Fin (D + 1) → Polynomial ℝ) (s : ℝ) :
    (xPolynomial G s).eval 0 = (G 0).eval s := by
  simp [xPolynomial, Polynomial.eval_finset_sum, Fin.sum_univ_succ]

theorem xPolynomial_derivative_eval_zero {D : ℕ} (G : Fin (D + 1) → Polynomial ℝ)
    (hG : ∀ i, i.val = 1 → G i = 0) (s : ℝ) :
    (xPolynomial G s).derivative.eval 0 = 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one,
    xPolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val = 1
  · simp [hi, hG i hi]
  · simp [hi, Ne.symm hi]

/-- The second-order mean-value estimate on an arbitrary positive interval. -/
theorem polynomial_sub_le_second_derivative_bound (p : Polynomial ℝ) {a C x : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hp0 : p.derivative.eval 0 = 0)
    (hb : ∀ u ∈ Icc (0 : ℝ) a, |p.derivative.derivative.eval u| ≤ C)
    (hx : x ∈ Icc (0 : ℝ) a) :
    |p.eval x - p.eval 0| ≤ C * x ^ 2 := by
  have hd : ∀ u ∈ Icc (0 : ℝ) x, |p.derivative.eval u| ≤ C * x := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) a := ⟨hu.1, hu.2.trans hx.2⟩
    have h := (convex_Icc (0 : ℝ) a).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v _ => (p.derivative.hasDerivAt v).hasDerivWithinAt)
      (fun v hv => by simpa only [Real.norm_eq_abs] using hb v hv)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) a from ⟨le_rfl, ha⟩) hu'
    simp only [Real.norm_eq_abs, hp0, sub_zero, abs_of_nonneg hu.1] at h
    exact h.trans (mul_le_mul_of_nonneg_left hu.2 hC)
  have h := (convex_Icc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ => (p.hasDerivAt v).hasDerivWithinAt)
    (fun v hv => by simpa only [Real.norm_eq_abs] using hd v hv)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) x from ⟨le_rfl, hx.1⟩)
    (show x ∈ Icc (0 : ℝ) x from ⟨hx.1, le_rfl⟩)
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.1, pow_two, mul_assoc] using h

/-- If the linear coefficient vanishes, two applications of Markov give a
quadratic bound in the inverse-dimension variable. -/
theorem polynomial_sub_le_of_bound_and_derivative_zero (p : Polynomial ℝ) (D : ℕ)
    {a B x : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hD : p.natDegree ≤ D) (hp0 : p.derivative.eval 0 = 0)
    (hb : ∀ u ∈ Icc (0 : ℝ) a, |p.eval u| ≤ B)
    (hx : x ∈ Icc (0 : ℝ) a) :
    |p.eval x - p.eval 0| ≤ (4 * (D : ℝ) ^ 3 / a) ^ 2 * B * x ^ 2 := by
  apply polynomial_sub_le_second_derivative_bound p ha.le (by positivity) hp0 _ hx
  intro u hu
  have hD' : p.derivative.natDegree ≤ D :=
    (natDegree_derivative_le p).trans ((Nat.sub_le _ _).trans hD)
  have h := polynomial_markov_bound p.derivative D ha hD'
    (fun v hv => polynomial_markov_bound p D ha hD hb hv) hu
  nlinarith

#print axioms polynomial_sub_le_of_bound_and_derivative_zero

/-- Two-variable interpolation from all admissible finite-rank samples.
The missing linear coefficient improves the inverse-dimension error to order
two.  The constants are the explicit B3b constants in the blueprint. -/
theorem two_variable_interpolation (k N₀ q D : ℕ)
    (G : Fin (D + 1) → Polynomial ℝ) {B : ℝ}
    (hk : 0 < k) (hN₀ : 0 < N₀)
    (hqN : 8 * q ^ 3 ≤ N₀) (hDN : 8 * k * D ^ 3 ≤ N₀)
    (hdegree : ∀ i, (G i).natDegree ≤ q)
    (hlinear : ∀ i, i.val = 1 → G i = 0)
    (hsamples : ∀ N : ℕ, k ∣ N → N₀ ≤ N → ∀ d : ℕ, d ≤ N →
      |(sPolynomial G (1 / (N : ℝ))).eval ((d : ℝ) / N)| ≤ B)
    {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / (N₀ : ℝ)))
    (hs : s ∈ Icc (0 : ℝ) 1) :
    |(xPolynomial G s).eval x - (G 0).eval s| ≤
      64 * (D : ℝ) ^ 6 * (N₀ : ℝ) ^ 2 * B * x ^ 2 := by
  have hN₀R : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  have hBR : 0 ≤ B := by
    have hN : N₀ ≤ k * N₀ := by nlinarith [Nat.succ_le_of_lt hk]
    exact (abs_nonneg _).trans (hsamples (k * N₀) (dvd_mul_right _ _) hN 0 (Nat.zero_le _))
  have hdensity (N : ℕ) (hdiv : k ∣ N) (hN : N₀ ≤ N) :
      ∀ u ∈ Icc (0 : ℝ) 1,
        |(sPolynomial G (1 / (N : ℝ))).eval u| ≤ 2 * B := by
    have hNp : 0 < N := hN₀.trans_le hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
    let I : Set ℝ := {u | ∃ d : ℕ, d ≤ N ∧ u = (d : ℝ) / N}
    apply polynomial_bound_of_dense_samples _ q (I := I) (δ := 1 / (N : ℝ))
      (by norm_num) (sPolynomial_natDegree_le G hdegree _)
    · rintro u ⟨d, hd, rfl⟩
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) hNR.le
      · exact (div_le_one hNR).mpr (by exact_mod_cast hd)
    · intro u hu
      obtain ⟨d, hd, herr⟩ := rank_grid_mesh N hNp hu
      exact ⟨(d : ℝ) / N, ⟨d, hd, rfl⟩, herr⟩
    · have h : 8 * (q : ℝ) ^ 3 ≤ (N : ℝ) := by exact_mod_cast hqN.trans hN
      rw [mul_one_div, div_le_one hNR]
      exact h
    · rintro u ⟨d, hd, rfl⟩
      exact hsamples N hdiv hN d hd
  have hxbound : ∀ u ∈ Icc (0 : ℝ) (1 / (N₀ : ℝ)),
      |(xPolynomial G s).eval u| ≤ 4 * B := by
    let I : Set ℝ := {u | ∃ N : ℕ, k ∣ N ∧ N₀ ≤ N ∧ u = 1 / (N : ℝ)}
    have hsup : ∀ u ∈ Icc (0 : ℝ) (1 / (N₀ : ℝ)),
        |(xPolynomial G s).eval u| ≤ 2 * (2 * B) := by
      apply polynomial_bound_of_dense_samples _ D (I := I) (δ := (k : ℝ) / (N₀ : ℝ) ^ 2)
        (one_div_pos.mpr hN₀R) (xPolynomial_natDegree_le G s)
      · rintro u ⟨N, hdiv, hN, rfl⟩
        have hNR : (0 : ℝ) < N := hN₀R.trans_le (by exact_mod_cast hN)
        exact ⟨(one_div_pos.mpr hNR).le, one_div_le_one_div_of_le hN₀R (by exact_mod_cast hN)⟩
      · intro u hu
        obtain ⟨N, hdiv, hN, herr⟩ := reciprocal_grid_mesh k N₀ hk hN₀ hu
        exact ⟨1 / (N : ℝ), ⟨N, hdiv, hN, rfl⟩, herr⟩
      · have h : 8 * (k : ℝ) * (D : ℝ) ^ 3 ≤ N₀ := by exact_mod_cast hDN
        rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hN₀R) hN₀R]
        nlinarith [mul_le_mul_of_nonneg_right h hN₀R.le]
      · rintro u ⟨N, hdiv, hN, rfl⟩
        rw [xPolynomial_eval_eq_sPolynomial_eval]
        exact hdensity N hdiv hN s hs
    intro u hu
    nlinarith [hsup u hu]
  have h := polynomial_sub_le_of_bound_and_derivative_zero (xPolynomial G s) D
    (one_div_pos.mpr hN₀R) (by positivity : 0 ≤ 4 * B)
    (xPolynomial_natDegree_le G s) (xPolynomial_derivative_eval_zero G hlinear s) hxbound hx
  rw [xPolynomial_eval_zero] at h
  simp only [one_div, div_eq_mul_inv, one_mul, inv_inv] at h
  convert h using 1
  ring

#print axioms two_variable_interpolation

end ProjectionChannels.PolyChebyshev
