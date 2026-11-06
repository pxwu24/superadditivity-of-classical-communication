import StrongConvergence.StrongConvergenceGenusTruncation

/-! Actual Haar moment bounds for truncation by inverse-dimension degree. -/
open Matrix Polynomial MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

/-- Odd coefficients vanish, so an even cutoff gains one further power. -/
def genusTailExponent (R : ℕ) : ℕ := if R % 2 = 0 then R + 2 else R + 1

lemma genusTailExponent_le (R : ℕ) : genusTailExponent R ≤ R + 2 := by
  unfold genusTailExponent
  split_ifs <;> omega

lemma neumann_dimension_scaling (F K A N : ℝ) (hN : N ≠ 0) (m R : ℕ) :
    F * N ^ m * K * (2 * (A / (3 * N)) ^ (R + m + 2)) =
      (F * K * A ^ m) * (A / N) ^ (R + 2) * (2 / (3 : ℝ) ^ (R + m + 2)) := by
  rw [div_pow, mul_pow, div_pow]
  have hq : R + m + 2 = m + (R + 2) := by omega
  rw [hq, pow_add A m (R + 2), pow_add N m (R + 2)]
  field_simp
  ring

lemma two_div_three_pow_le_half {q : ℕ} (hq : 2 ≤ q) :
    2 / (3 : ℝ) ^ q ≤ 1 / 2 := by
  have hp : (9 : ℝ) ≤ 3 ^ q := by
    convert (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hq) using 1
    norm_num
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ q)).mpr
  linarith

lemma radius_weight_identity (F K A N ε : ℝ) (hN : N ≠ 0)
    (hε : 1 - ε ≠ 0) (m p : ℕ) :
    K * (N⁻¹ / A⁻¹) ^ p * (F / ((A⁻¹) ^ m * (1 - ε))) =
      (F * K * A ^ m) * (A / N) ^ p * (1 / (1 - ε)) := by
  rw [div_pow, inv_pow, inv_pow]
  field_simp
  ring

end ProjectionChannels.TensorHaar
namespace ProjectionChannels.Canonical
open TensorHaar

/-- Every integer rank is realized exactly by the corresponding rational density. -/
theorem rankSequence_exact_density {k : ℕ} (hk : 0 < k) (n d : ℕ) :
    rankSequence k ((d : ℝ) / (((n + 1) * k : ℕ) : ℝ)) n = d := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hnR : (n : ℝ) + 1 ≠ 0 := by positivity
  have heq : ((d : ℝ) / (((n + 1) * k : ℕ) : ℝ)) * ((k : ℝ) * (n + 1)) = d := by
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    simp [mul_comm]
  rw [rankSequence, heq, Nat.floor_natCast]

/-- Explicit degree-truncation error for the actual expected Haar moment.
No moment convergence or spectral-limit theorem is assumed. -/
theorem expectedNormalizedMoment_degree_error
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n m R : ℕ) (hmn : m ≤ n) (a : Fin k → ℝ)
    (hN : 2 * (m + 1) ^ 2 ≤ (n + 1) * k) :
    ‖expectedNormalizedMoment k t n m a -
      complexPolynomialEval ((((n + 1) * k : ℕ) : ℝ)⁻¹)
        (degreeTruncation R (genusMomentPolynomial k (m + 1) a
          ((rankSequence k t n : ℝ) / (((n + 1) * k : ℕ) : ℝ)) (R + (m + 1))))‖ ≤
      2 * ((m + 1).factorial : ℝ) * (∑ i, |a i|) ^ (m + 1) *
        (2 * ((m + 1 : ℕ) : ℝ) ^ 2) ^ m *
        ((2 * ((m + 1 : ℕ) : ℝ) ^ 2) / (((n + 1) * k : ℕ) : ℝ)) ^
          genusTailExponent R := by
  let N : ℕ := (n + 1) * k
  let A : ℝ := 2 * ((m + 1 : ℕ) : ℝ) ^ 2
  let K : ℝ := (∑ i, |a i|) ^ (m + 1)
  let F : ℝ := ((m + 1).factorial : ℝ)
  let C : ℝ := F * K * A ^ m
  let u : ℝ := A / N
  let p : ℕ := genusTailExponent R
  let s : ℝ := (rankSequence k t n : ℝ) / N
  let Q := genusMomentPolynomial k (m + 1) a s (R + (m + 1))
  let ε := genusRowError (m + 1) (genusRadius (m + 1))
  have hNpos : 0 < N := Nat.mul_pos (Nat.succ_pos n) hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hA : 0 < A := by dsimp [A]; positivity
  have hAN : A ≤ N := by dsimp [A, N]; exact_mod_cast hN
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hu0 : 0 ≤ u := div_nonneg hA.le hNR.le
  have hu1 : u ≤ 1 := (div_le_one hNR).mpr hAN
  have hε : ε < 1 / 3 := genusRowError_radius_lt_third (Nat.succ_pos m)
  have hden : 0 < 1 - ε := by linarith
  have hinv : 1 / (1 - ε) ≤ 3 / 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hs : |s| ≤ 1 := by
    have hd := rankSequence_le (k := k) ht0 ht1 n
    have hdN : rankSequence k t n ≤ N := by
      simpa only [Index, Fintype.card_prod, Fintype.card_fin, N] using hd
    dsimp [s]
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one hNR).mpr (by exact_mod_cast hdN)
  have hxy : (N : ℝ)⁻¹ ≤ genusRadius (m + 1) := by
    simpa only [one_div] using inv_dimension_le_genusRadius (Nat.succ_pos m) hAN
  have hpoly :
      |Q.eval ((N : ℝ)⁻¹) - (degreeTruncation R Q).eval ((N : ℝ)⁻¹)| ≤
        K * ((N : ℝ)⁻¹ / genusRadius (m + 1)) ^ p *
          (F / ((genusRadius (m + 1)) ^ m * (1 - ε))) := by
    by_cases hR : R % 2 = 0
    · simpa [Q, K, F, p, genusTailExponent, hR, ε, Nat.succ_sub_one] using
        genusMomentPolynomial_truncation_error_even hk (Nat.succ_pos m) a hs
          (R + (m + 1)) R hR (by positivity : 0 ≤ (N : ℝ)⁻¹) hxy
    · simpa [Q, K, F, p, genusTailExponent, hR, ε, Nat.succ_sub_one] using
        genusMomentPolynomial_truncation_error hk (Nat.succ_pos m) a hs
          (R + (m + 1)) R (by positivity : 0 ≤ (N : ℝ)⁻¹) hxy
  have hpoly' :
      ‖complexPolynomialEval ((N : ℝ)⁻¹) Q -
        complexPolynomialEval ((N : ℝ)⁻¹) (degreeTruncation R Q)‖ ≤ (3 / 2) * C * u ^ p := by
    simp only [complexPolynomialEval_apply, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    have hy : genusRadius (m + 1) = A⁻¹ := by simp [genusRadius, A, one_div]
    rw [hy] at hpoly
    rw [radius_weight_identity F K A (N : ℝ) ε hNR.ne' hden.ne' m p] at hpoly
    calc
      _ ≤ C * u ^ p * (1 / (1 - ε)) := hpoly
      _ ≤ C * u ^ p * (3 / 2) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hmoment :
      ‖expectedNormalizedMoment k t n m a - complexPolynomialEval ((N : ℝ)⁻¹) Q‖ ≤
        C * u ^ p / 2 := by
    have h := expectedNormalizedMoment_neumann_error hk ht0 ht1 n m (R + (m + 1)) hmn a hN
    change ‖expectedNormalizedMoment k t n m a - complexPolynomialEval ((N : ℝ)⁻¹) Q‖ ≤
      F * (N : ℝ) ^ m * K * (2 * (A / (3 * (N : ℝ))) ^ (R + m + 2)) at h
    rw [neumann_dimension_scaling F K A (N : ℝ) hNR.ne' m R] at h
    calc
      _ ≤ C * u ^ (R + 2) * (2 / (3 : ℝ) ^ (R + m + 2)) := h
      _ ≤ C * u ^ (R + 2) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (two_div_three_pow_le_half (by omega)) (by positivity)
      _ ≤ C * u ^ p * (1 / 2) := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hu0 hu1 (genusTailExponent_le R)) hC
      _ = _ := by ring
  change ‖expectedNormalizedMoment k t n m a -
    complexPolynomialEval ((N : ℝ)⁻¹) (degreeTruncation R Q)‖ ≤ _
  calc
    _ ≤ ‖expectedNormalizedMoment k t n m a - complexPolynomialEval ((N : ℝ)⁻¹) Q‖ +
        ‖complexPolynomialEval ((N : ℝ)⁻¹) Q -
          complexPolynomialEval ((N : ℝ)⁻¹) (degreeTruncation R Q)‖ := by
            simpa only [dist_eq_norm] using dist_triangle
              (expectedNormalizedMoment k t n m a) (complexPolynomialEval ((N : ℝ)⁻¹) Q)
              (complexPolynomialEval ((N : ℝ)⁻¹) (degreeTruncation R Q))
    _ ≤ C * u ^ p / 2 + (3 / 2) * C * u ^ p := add_le_add hmoment hpoly'
    _ = _ := by dsimp [C, F, K, A, u, p, N]; ring

/-- Uniform inverse-square dimension bound for all moment orders at most `q`.
This is the concrete A6(ii) estimate needed for polynomial interpolation. -/
theorem expectedNormalizedMoment_degree_uniform_error
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n m q : ℕ) (hmn : m ≤ n) (hmq : m + 1 ≤ q) (a : Fin k → ℝ)
    (hN : 8 * q ^ 4 ≤ (n + 1) * k) :
    ‖expectedNormalizedMoment k t n m a -
      complexPolynomialEval ((((n + 1) * k : ℕ) : ℝ)⁻¹)
        (degreeTruncation (2 * q) (genusMomentPolynomial k (m + 1) a
          ((rankSequence k t n : ℝ) / (((n + 1) * k : ℕ) : ℝ)) (2 * q + (m + 1))))‖ ≤
      4 * (q : ℝ) ^ 2 * (∑ i, |a i|) ^ (m + 1) /
        ((8 : ℝ) ^ q * (q : ℝ) ^ q * ((((n + 1) * k : ℕ) : ℝ) ^ 2)) := by
  have hq : 0 < q := lt_of_lt_of_le (Nat.succ_pos m) hmq
  have hbase : 2 * (m + 1) ^ 2 ≤ (n + 1) * k := by
    have hpow := Nat.pow_le_pow_left hmq 2
    have hpow' := Nat.pow_le_pow_right hq (by decide : 2 ≤ 4)
    omega
  have hNR : 8 * (q : ℝ) ^ 4 ≤ (((n + 1) * k : ℕ) : ℝ) := by exact_mod_cast hN
  have heven : genusTailExponent (2 * q) = 2 * q + 2 := by
    simp [genusTailExponent, Nat.mul_mod]
  have h := expectedNormalizedMoment_degree_error hk ht0 ht1 n m (2 * q) hmn a hbase
  rw [heven] at h
  let err := ‖expectedNormalizedMoment k t n m a -
      complexPolynomialEval ((((n + 1) * k : ℕ) : ℝ)⁻¹)
        (degreeTruncation (2 * q) (genusMomentPolynomial k (m + 1) a
          ((rankSequence k t n : ℝ) / (((n + 1) * k : ℕ) : ℝ)) (2 * q + (m + 1))))‖
  have herror : |err - 0| ≤ (∑ i, |a i|) ^ (m + 1) *
      (2 * ((m + 1).factorial : ℝ) * (2 * ((m + 1 : ℕ) : ℝ) ^ 2) ^ ((m + 1) - 1) *
        ((2 * ((m + 1 : ℕ) : ℝ) ^ 2) / (((n + 1) * k : ℕ) : ℝ)) ^ (2 * q + 2)) := by
    simpa [err, abs_norm, mul_assoc, mul_left_comm, mul_comm] using h
  have hout := genus_tail_degree_uniform_error_of_bound (Nat.succ_pos m) hmq
    (Finset.sum_nonneg (fun i _ => abs_nonneg (a i))) hNR herror
  simpa [err, abs_norm] using hout

end ProjectionChannels.Canonical
#print axioms ProjectionChannels.Canonical.rankSequence_exact_density
#print axioms ProjectionChannels.Canonical.expectedNormalizedMoment_degree_error
#print axioms ProjectionChannels.Canonical.expectedNormalizedMoment_degree_uniform_error
