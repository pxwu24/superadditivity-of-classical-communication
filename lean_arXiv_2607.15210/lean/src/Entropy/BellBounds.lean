import Entropy.Combinatorics

open Real Finset
noncomputable section
namespace AppendixB

set_option maxHeartbeats 2000000

lemma abs_add_three (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  calc |a + b + c| ≤ |a + b| + |c| := abs_add _ _
    _ ≤ |a| + |b| + |c| := add_le_add_right (abs_add _ _) _

/-- `0 ≤ r_{k,t} ≤ 2γ/k²` and `|k² r_{k,t} - γ| ≤ 6γ/k²`, with `γ = (1-t)/t`. -/
lemma rkt_bounds {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {k : ℕ} (hk : 2 ≤ (k : ℝ))
    (hkt : 1 ≤ (k : ℝ) ^ 2 * t) :
    0 ≤ rkt k t ∧ rkt k t ≤ 2 * ((1 - t) / t) / (k : ℝ) ^ 2 ∧
      |(k : ℝ) ^ 2 * rkt k t - (1 - t) / t| ≤ 6 * ((1 - t) / t) / (k : ℝ) ^ 2 := by
  have h1t : 0 < 1 - t := by linarith
  have ht0' := ht0.ne'
  have hK0 : (0 : ℝ) < k := by linarith
  have hK0' := hK0.ne'
  have hK2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hden_lo : (k : ℝ) ^ 4 * t / 2 ≤ (k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1 := by
    have : 2 * (k : ℝ) ^ 2 * t ≤ (k : ℝ) ^ 4 * t / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hK2 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2 * t)]
    linarith
  have hden0 : 0 < (k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1 :=
    lt_of_lt_of_le (by positivity) hden_lo
  have hden0' := hden0.ne'
  unfold rkt
  refine ⟨div_nonneg (mul_nonneg (sq_nonneg _) h1t.le) hden0.le, ?_, ?_⟩
  · rw [div_le_div_iff₀ hden0 (by positivity)]
    calc (k : ℝ) ^ 2 * (1 - t) * (k : ℝ) ^ 2
        = 2 * ((1 - t) / t) * ((k : ℝ) ^ 4 * t / 2) := by field_simp <;> ring
      _ ≤ 2 * ((1 - t) / t) * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1) :=
          mul_le_mul_of_nonneg_left hden_lo (by positivity)
  · have e : (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (1 - t) / ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1))
          - (1 - t) / t
        = (1 - t) * (2 * (k : ℝ) ^ 2 * t - 1)
            / (t * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1)) := by
      field_simp <;> ring
    have hnum : 0 ≤ (1 - t) * (2 * (k : ℝ) ^ 2 * t - 1) := mul_nonneg h1t.le (by linarith)
    rw [e, abs_of_nonneg (div_nonneg hnum (mul_pos ht0 hden0).le),
      div_le_div_iff₀ (mul_pos ht0 hden0) (by positivity)]
    have h3 : (1 - t) * (2 * (k : ℝ) ^ 2 * t - 1) * (k : ℝ) ^ 2
        ≤ (1 - t) * (2 * (k : ℝ) ^ 2 * t) * (k : ℝ) ^ 2 := by
      nlinarith [mul_nonneg h1t.le (sq_nonneg (k : ℝ))]
    have h4 : (1 - t) * (2 * (k : ℝ) ^ 2 * t) * (k : ℝ) ^ 2
        ≤ 6 * ((1 - t) / t) * (t * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1)) := by
      have e2 : 6 * ((1 - t) / t) * (t * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1))
          = 6 * (1 - t) * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1) := by
        field_simp <;> ring
      rw [e2]
      have := mul_le_mul_of_nonneg_left hden_lo (by positivity : (0 : ℝ) ≤ 6 * (1 - t))
      nlinarith [this, mul_nonneg (mul_nonneg h1t.le (pow_nonneg hK0.le 4)) ht0.le]
    linarith

/-- The last step shared by both Bell-output proofs:
    `F_p(X) - c_p Y = (F_p(X) - c_p X) + c_p (X - Y)`. -/
lemma final_step {p C₂ : ℝ} (hF : ∀ x, |x| ≤ 1 / 2 → |Fp p x - cp p * x| ≤ C₂ * x ^ 2)
    {X Y e : ℝ} (hXY : |X - Y| ≤ e) (hX : |X| ≤ 1 / 2) :
    |Fp p X - cp p * Y| ≤ C₂ * X ^ 2 + |cp p| * e := by
  have h1 := hF X hX
  calc |Fp p X - cp p * Y| = |(Fp p X - cp p * X) + cp p * (X - Y)| := by congr 1; ring
    _ ≤ |Fp p X - cp p * X| + |cp p * (X - Y)| := abs_add _ _
    _ ≤ C₂ * X ^ 2 + |cp p| * e := by
        rw [abs_mul]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left hXY (abs_nonneg _))

/-- `|ψ_p(y)| ≤ (|κ_p| + C) y²` near `0`. -/
lemma psi_quad {p η C : ℝ} (hη' : η ≤ 1 / 2) (hC : 0 ≤ C)
    (hloc : ∀ y, |y| ≤ η → |psi p y - kappa p * y ^ 2| ≤ C * |y| ^ 3) :
    ∀ y, |y| ≤ η → |psi p y| ≤ (|kappa p| + C) * y ^ 2 := by
  intro y hy
  have h1 := hloc y hy
  have hy0 := abs_nonneg y
  have h2 : |y| ^ 3 ≤ y ^ 2 := by
    rw [← sq_abs y]
    nlinarith [mul_nonneg (pow_nonneg hy0 2) (by linarith : (0 : ℝ) ≤ 1 - |y|)]
  have h3 : |kappa p * y ^ 2| = |kappa p| * y ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
  have h4 : |psi p y| ≤ |psi p y - kappa p * y ^ 2| + |kappa p * y ^ 2| := by
    calc |psi p y| = |(psi p y - kappa p * y ^ 2) + kappa p * y ^ 2| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add _ _
  nlinarith [mul_le_mul_of_nonneg_left h2 hC]

/-- `D² w_m = k (r - m)(k - r - m + 1)/r²`, from `kN = rD`. -/
lemma D2wm {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (m : ℕ) :
    (Nat.choose k r : ℝ) ^ 2 * wm k r m
      = (k : ℝ) * (((r : ℝ) - m) * ((k : ℝ) - r - m + 1)) / (r : ℝ) ^ 2 := by
  have hk : 1 ≤ k := le_trans hr hrk
  have h1 := choose_mul_left hr hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hD : (0 : ℝ) < (Nat.choose k r : ℝ) := by exact_mod_cast Nat.choose_pos hrk
  have hk0' := hk0.ne'
  have hr0' := hr0.ne'
  have hD' := hD.ne'
  have hNeq : (Nat.choose (k - 1) (r - 1) : ℝ) = r * (Nat.choose k r : ℝ) / k := by
    rw [eq_div_iff hk0']
    linarith [h1]
  unfold wm
  rw [hNeq]
  field_simp <;> ring

/-- `|d_m| ≤ 2 ((2r/k)² D)²` for `m ≤ r - 2`. -/
lemma dm_small {k r' m : ℕ} (hk : 2 * (r' + 1) ≤ k) (hm : m < r') :
    |dm k m| ≤ 2 * ((2 * ((r' + 1 : ℕ) : ℝ) / k) ^ 2 * (Nat.choose k (r' + 1) : ℝ)) ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hq0 : (0 : ℝ) ≤ 2 * ((r' + 1 : ℕ) : ℝ) / k := by positivity
  have hq1 : 2 * ((r' + 1 : ℕ) : ℝ) / k ≤ 1 := by
    rw [div_le_one hk0]; exact_mod_cast hk
  have hD0 : (0 : ℝ) ≤ Nat.choose k (r' + 1) := Nat.cast_nonneg _
  have hb : ∀ j, j ≤ m →
      (Nat.choose k j : ℝ) ≤ (2 * ((r' + 1 : ℕ) : ℝ) / k) ^ 2 * Nat.choose k (r' + 1) := by
    intro j hj
    have h := choose_le_pow (k := k) (r := r' + 1) hk ((r' + 1) - j) (by omega)
    have e : r' + 1 - (r' + 1 - j) = j := by omega
    rw [e] at h
    calc (Nat.choose k j : ℝ)
        ≤ (2 * ((r' + 1 : ℕ) : ℝ) / k) ^ (r' + 1 - j) * Nat.choose k (r' + 1) := h
      _ ≤ (2 * ((r' + 1 : ℕ) : ℝ) / k) ^ 2 * Nat.choose k (r' + 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 (by omega)) hD0
  have h1 := hb m le_rfl
  have hc0 : (0 : ℝ) ≤ Nat.choose k m := Nat.cast_nonneg _
  have h3 := pow_le_pow_left hc0 h1 2
  have hB0 : (0 : ℝ) ≤ ((2 * ((r' + 1 : ℕ) : ℝ) / k) ^ 2 * Nat.choose k (r' + 1)) ^ 2 :=
    sq_nonneg _
  unfold dm
  split_ifs with h0
  · rw [sub_zero, abs_of_nonneg (by positivity)]
    linarith
  · have h2 := hb (m - 1) (by omega)
    have hc1 : (0 : ℝ) ≤ Nat.choose k (m - 1) := Nat.cast_nonneg _
    have h4 := pow_le_pow_left hc1 h2 2
    rw [abs_le]
    constructor <;> nlinarith [h3, h4, sq_nonneg (Nat.choose k m : ℝ),
      sq_nonneg (Nat.choose k (m - 1) : ℝ)]

end AppendixB
end
