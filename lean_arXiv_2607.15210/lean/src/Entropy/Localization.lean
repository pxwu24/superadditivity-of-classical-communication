import Entropy.Defs

set_option maxHeartbeats 400000

open Real Finset
noncomputable section
namespace AppendixB

/-! ## 8. The localization bound (app-ct-bound) -/

/-- (app-ct-bound), squared: `(u-t)² ≤ c_t(u) (2√(t(1-t)) + √(2 c_t(u)))²`. -/
lemma ct_bound {t u : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u - t) ^ 2 ≤ ct t u * (2 * Real.sqrt (t * (1 - t)) + Real.sqrt (2 * ct t u)) ^ 2 := by
  have h1t : 0 ≤ 1 - t := by linarith
  have h1u : 0 ≤ 1 - u := by linarith
  have hc : ct t u = (Real.sqrt t * Real.sqrt (1 - u) - Real.sqrt (1 - t) * Real.sqrt u) ^ 2 := by
    simp only [ct]
    rw [Real.sqrt_mul ht0.le, Real.sqrt_mul h1t]
  have hab : Real.sqrt (t * (1 - t)) = Real.sqrt t * Real.sqrt (1 - t) := Real.sqrt_mul ht0.le _
  rw [hc, hab]
  set a := Real.sqrt t with ha_def
  set b := Real.sqrt (1 - t) with hb_def
  set x := Real.sqrt u with hx_def
  set y := Real.sqrt (1 - u) with hy_def
  have ha : a ^ 2 = t := Real.sq_sqrt ht0.le
  have hb : b ^ 2 = 1 - t := Real.sq_sqrt h1t
  have hx : x ^ 2 = u := Real.sq_sqrt hu0
  have hy : y ^ 2 = 1 - u := Real.sq_sqrt h1u
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hut : u - t = (b * x - a * y) * (b * x + a * y) := by
    linear_combination (-x ^ 2) * hb + (-(1 - t)) * hx + y ^ 2 * ha + t * hy
  have hlag : (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 = 1 := by
    linear_combination (x ^ 2 + y ^ 2) * ha + (x ^ 2 + y ^ 2) * hb + hx + hy
  have hs0 : 0 ≤ a * x + b * y := by positivity
  have hs1 : a * x + b * y ≤ 1 := by nlinarith only [hlag, sq_nonneg (a * y - b * x)]
  have hdist : (x - a) ^ 2 + (y - b) ^ 2 = 2 - 2 * (a * x + b * y) := by
    linear_combination hx + hy + ha + hb
  have hdist2 : (x - a) ^ 2 + (y - b) ^ 2 ≤ 2 * (a * y - b * x) ^ 2 := by
    rw [hdist]
    nlinarith only [hlag, mul_nonneg hs0 (by linarith only [hs1] : (0 : ℝ) ≤ 1 - (a * x + b * y))]
  have hab1 : a ^ 2 + b ^ 2 = 1 := by rw [ha, hb]; ring
  have hlag2 : (b * (x - a) + a * (y - b)) ^ 2 + (b * (y - b) - a * (x - a)) ^ 2
      = (a ^ 2 + b ^ 2) * ((x - a) ^ 2 + (y - b) ^ 2) := by ring
  rw [hab1, one_mul] at hlag2
  have hcs : (b * x + a * y - 2 * (a * b)) ^ 2 ≤ 2 * (a * y - b * x) ^ 2 := by
    have e : b * x + a * y - 2 * (a * b) = b * (x - a) + a * (y - b) := by ring
    rw [e]
    nlinarith only [sq_nonneg (b * (y - b) - a * (x - a)), hlag2, hdist2]
  have hsq : |b * x + a * y - 2 * (a * b)| ≤ Real.sqrt (2 * (a * y - b * x) ^ 2) :=
    Real.abs_le_sqrt hcs
  have hbxay : b * x + a * y ≤ 2 * (a * b) + Real.sqrt (2 * (a * y - b * x) ^ 2) := by
    have := le_abs_self (b * x + a * y - 2 * (a * b))
    linarith
  have hpos : 0 ≤ b * x + a * y := by positivity
  rw [hut]
  calc ((b * x - a * y) * (b * x + a * y)) ^ 2
      = (a * y - b * x) ^ 2 * (b * x + a * y) ^ 2 := by ring
    _ ≤ (a * y - b * x) ^ 2 * (2 * (a * b) + Real.sqrt (2 * (a * y - b * x) ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos hbxay 2) (sq_nonneg _)

/-- The sum of `f` over `(u₊, u₋, t, …, t)`. -/
lemma sum_cons2 (n : ℕ) (a b c : ℝ) (f : ℝ → ℝ) :
    ∑ i : Fin (n + 2),
        f ((Fin.cons a (Fin.cons b (fun _ : Fin n => c) : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ) i)
      = f a + f b + n * f c := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- For `q = u / ∑u`: `∑ (k q_i - 1)² = (k² ∑ w_i² - k (∑ w_i)²) / (∑ u)²`, `w = u - t`. -/
lemma eps_sq_sum {k : ℕ} (t : ℝ) (u : Fin k → ℝ) (hS : ∑ j, u j ≠ 0) :
    ∑ i, ((k : ℝ) * (u i / ∑ j, u j) - 1) ^ 2
      = ((k : ℝ) ^ 2 * ∑ i, (u i - t) ^ 2 - k * (∑ i, (u i - t)) ^ 2) / (∑ j, u j) ^ 2 := by
  set S := ∑ j, u j with hS_def
  set W := ∑ i, (u i - t) with hW
  have hSW : S = k * t + W := by
    rw [hW, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have e : ∀ i, (k : ℝ) * (u i / S) - 1 = ((k : ℝ) * (u i - t) - W) / S := by
    intro i
    field_simp
    rw [hSW]
    ring
  simp only [e, div_pow]
  rw [← Finset.sum_div]
  congr 1
  have e2 : ∀ i, ((k : ℝ) * (u i - t) - W) ^ 2
      = (k : ℝ) ^ 2 * (u i - t) ^ 2 - 2 * k * W * (u i - t) + W ^ 2 := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← hW]
  ring

/-! ## 9. Proposition app-localization -/

lemma sqrt_tt_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : Real.sqrt (t * (1 - t)) ≤ 1 / 2 := by
  calc Real.sqrt (t * (1 - t)) ≤ Real.sqrt ((1 / 2) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (t - 1 / 2)])
    _ = 1 / 2 := Real.sqrt_sq (by norm_num)

/-- Pure arithmetic: the last step of Prop. app-localization (i), with `k = s²`. -/
lemma loc_final {t s B : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : 4 ≤ s) (hkt : 16 ≤ s ^ 2 * t)
    (hB : B ^ 2 ≤ 4 * (t * (1 - t)) + 6 / s) :
    s ^ 2 * B ^ 2 / (s ^ 2 * t - 2) ^ 2
      ≤ 4 * ((1 - t) / t) / s ^ 2 + 200 / t ^ 3 / (s ^ 2 * s) := by
  have hs0 : 0 < s := by linarith
  have hs0' := hs0.ne'
  have ht0' := ht0.ne'
  set x := s ^ 2 * t with hx
  have hx0 : 0 < x := by linarith
  have hx2 : 0 < x - 2 := by linarith
  have hx0' := hx0.ne'
  have h1 : s ^ 2 / (x - 2) ^ 2 ≤ (1 + 8 / x) / (t ^ 2 * s ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : s ^ 2 * (t ^ 2 * s ^ 2) = x ^ 2 := by rw [hx]; ring
    rw [e]
    have e2 : (1 + 8 / x) * (x - 2) ^ 2 = (x + 8) * (x - 2) ^ 2 / x := by
      field_simp
    rw [e2, le_div_iff₀ hx0]
    nlinarith only [hkt, mul_le_mul_of_nonneg_left hkt hx0.le]
  have h8 : 8 / x ≤ 1 / 2 := by rw [div_le_iff₀ hx0]; linarith
  have h80 : 0 ≤ 8 / x := by positivity
  have h2 : B ^ 2 * (1 + 8 / x) ≤ 4 * (t * (1 - t)) + 17 / s := by
    have hB' : B ^ 2 * (1 + 8 / x) ≤ (4 * (t * (1 - t)) + 6 / s) * (1 + 8 / x) :=
      mul_le_mul_of_nonneg_right hB (by linarith)
    have e : 4 * (t * (1 - t)) * (8 / x) = 32 * (1 - t) / s ^ 2 := by
      rw [hx]; field_simp <;> ring
    have h3 : 32 * (1 - t) / s ^ 2 ≤ 8 / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      nlinarith only [mul_nonneg hs0.le (by linarith only [hs, ht0] : (0 : ℝ) ≤ s - 4 * (1 - t))]
    have h4 : 6 / s * (1 + 8 / x) ≤ 9 / s := by
      have h5 : 6 / s * (1 + 8 / x) ≤ 6 / s * (3 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h6 : 6 / s * (3 / 2) = 9 / s := by ring
      linarith
    have e2 : (4 * (t * (1 - t)) + 6 / s) * (1 + 8 / x)
        = 4 * (t * (1 - t)) + 4 * (t * (1 - t)) * (8 / x) + 6 / s * (1 + 8 / x) := by ring
    rw [e2, e] at hB'
    calc B ^ 2 * (1 + 8 / x)
        ≤ 4 * (t * (1 - t)) + 32 * (1 - t) / s ^ 2 + 6 / s * (1 + 8 / x) := hB'
      _ ≤ 4 * (t * (1 - t)) + 8 / s + 9 / s :=
        add_le_add (add_le_add_left h3 _) h4
      _ = 4 * (t * (1 - t)) + 17 / s := by ring
  calc s ^ 2 * B ^ 2 / (x - 2) ^ 2 = B ^ 2 * (s ^ 2 / (x - 2) ^ 2) := by ring
    _ ≤ B ^ 2 * ((1 + 8 / x) / (t ^ 2 * s ^ 2)) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = B ^ 2 * (1 + 8 / x) / (t ^ 2 * s ^ 2) := by ring
    _ ≤ (4 * (t * (1 - t)) + 17 / s) / (t ^ 2 * s ^ 2) :=
        div_le_div_of_nonneg_right h2 (by positivity)
    _ = 4 * ((1 - t) / t) / s ^ 2 + 17 / (t ^ 2 * (s ^ 2 * s)) := by
        field_simp <;> ring
    _ ≤ 4 * ((1 - t) / t) / s ^ 2 + 200 / t ^ 3 / (s ^ 2 * s) := by
        have h7 : 17 / (t ^ 2 * (s ^ 2 * s)) ≤ 200 / t ^ 3 / (s ^ 2 * s) := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h9 : 0 ≤ t ^ 2 * (s ^ 2 * s) := by positivity
          nlinarith only [mul_nonneg h9 (by linarith only [ht1] : (0 : ℝ) ≤ 200 - 17 * t)]
        linarith

/-- Prop. app-localization (i). -/
lemma localization {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ C k₀ : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ (k : ℝ) → ∀ q ∈ Lam k t,
      (∑ i, q i = 1) ∧ (∀ i, 0 ≤ q i) ∧
      (∀ i, |(k : ℝ) * q i - 1| ≤ C / Real.sqrt k) ∧
      ∑ i, ((k : ℝ) * q i - 1) ^ 2 ≤ 4 * ((1 - t) / t) / k + C / (k * Real.sqrt k) := by
  refine ⟨200 / t ^ 3, max 16 (16 / t), by positivity, fun k hk q hq => ?_⟩
  obtain ⟨u, ⟨hu01, hct⟩, rfl⟩ := hq
  beta_reduce
  have hk16 : (16 : ℝ) ≤ k := le_trans (le_max_left _ _) hk
  have hkt : 16 ≤ (k : ℝ) * t := by
    have := le_trans (le_max_right _ _) hk
    rw [div_le_iff₀ ht0] at this
    linarith
  have hkpos : (0 : ℝ) < k := by linarith
  have ht1' : t ^ 2 ≤ 1 := by nlinarith
  set s := Real.sqrt k with hs_def
  have hs2 : s ^ 2 = k := Real.sq_sqrt hkpos.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hkpos
  have hs4 : 4 ≤ s := by nlinarith only [hs2, hk16, hs0]
  have hc0 : ∀ i, 0 ≤ ct t (u i) := fun i => sq_nonneg _
  have hci : ∀ i, ct t (u i) ≤ 1 / k := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => hc0 j) (Finset.mem_univ i)) hct
  have hT := sqrt_tt_le ht0 ht1
  have hT0 : 0 ≤ Real.sqrt (t * (1 - t)) := Real.sqrt_nonneg _
  have hTsq : Real.sqrt (t * (1 - t)) ^ 2 = t * (1 - t) := Real.sq_sqrt (by nlinarith)
  have h2s : 0 < 2 / s := by positivity
  have h2s' : 2 / s ≤ 1 / 2 := by rw [div_le_iff₀ hs0]; linarith
  have hci2 : ∀ i, Real.sqrt (2 * ct t (u i)) ≤ 2 / s := by
    intro i
    calc Real.sqrt (2 * ct t (u i)) ≤ Real.sqrt ((2 / s) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_pow, hs2]
          have h1 := hci i
          calc 2 * ct t (u i) ≤ 2 * (1 / k) := by linarith
            _ ≤ 2 ^ 2 / k := by
                rw [mul_one_div]
                exact div_le_div_of_nonneg_right (by norm_num) hkpos.le
      _ = 2 / s := Real.sqrt_sq h2s.le
  set B := 2 * Real.sqrt (t * (1 - t)) + 2 / s with hB
  have hB0 : 0 ≤ B := by positivity
  have hB2 : B ≤ 2 := by rw [hB]; linarith
  have hBsq : B ^ 2 ≤ 4 * (t * (1 - t)) + 6 / s := by
    have h2 : (2 / s) ^ 2 ≤ 2 / s := by
      nlinarith only [mul_nonneg h2s.le (by linarith only [h2s'] : (0 : ℝ) ≤ 1 - 2 / s)]
    have e : B ^ 2 = 4 * Real.sqrt (t * (1 - t)) ^ 2
        + 4 * Real.sqrt (t * (1 - t)) * (2 / s) + (2 / s) ^ 2 := by rw [hB]; ring
    rw [e, hTsq]
    have h3 : 4 * Real.sqrt (t * (1 - t)) * (2 / s) ≤ 4 * (1 / 2) * (2 / s) := by
      have := mul_le_mul_of_nonneg_right hT h2s.le
      nlinarith only [this]
    have h4 : 4 * (1 / 2) * (2 / s) = 4 / s := by ring
    have h5 : 4 / s + 2 / s = 6 / s := by ring
    linarith
  have hw2 : ∀ i, (u i - t) ^ 2 ≤ ct t (u i) * B ^ 2 := by
    intro i
    have h1 := ct_bound ht0 ht1 (hu01 i).1 (hu01 i).2
    have h3 : 0 ≤ 2 * Real.sqrt (t * (1 - t)) + Real.sqrt (2 * ct t (u i)) := by positivity
    have h2 : 2 * Real.sqrt (t * (1 - t)) + Real.sqrt (2 * ct t (u i)) ≤ B := by
      rw [hB]; linarith [hci2 i]
    calc (u i - t) ^ 2
        ≤ ct t (u i) * (2 * Real.sqrt (t * (1 - t)) + Real.sqrt (2 * ct t (u i))) ^ 2 := h1
      _ ≤ ct t (u i) * B ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 2) (hc0 i)
  have hWsq : ∑ i, (u i - t) ^ 2 ≤ B ^ 2 / k := by
    calc ∑ i, (u i - t) ^ 2 ≤ ∑ i, ct t (u i) * B ^ 2 := Finset.sum_le_sum (fun i _ => hw2 i)
      _ = (∑ i, ct t (u i)) * B ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (1 / k) * B ^ 2 := mul_le_mul_of_nonneg_right hct (sq_nonneg _)
      _ = B ^ 2 / k := by ring
  have hwi : ∀ i, |u i - t| ≤ 2 / s := by
    intro i
    have h1 : (u i - t) ^ 2 ≤ (2 / s) ^ 2 := by
      calc (u i - t) ^ 2 ≤ ct t (u i) * B ^ 2 := hw2 i
        _ ≤ (1 / k) * 2 ^ 2 :=
            mul_le_mul (hci i) (pow_le_pow_left₀ hB0 hB2 2) (sq_nonneg _) (by positivity)
        _ = (2 / s) ^ 2 := by rw [div_pow, hs2]; ring
    have := sq_le_sq.mp h1
    rwa [abs_of_pos h2s] at this
  have hsumw : |∑ i, (u i - t)| ≤ 2 := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin k => (1 : ℝ))
      (fun i => u i - t)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h1
    have h2 : (k : ℝ) * ∑ i, (u i - t) ^ 2 ≤ 2 ^ 2 := by
      calc (k : ℝ) * ∑ i, (u i - t) ^ 2 ≤ k * (B ^ 2 / k) :=
            mul_le_mul_of_nonneg_left hWsq hkpos.le
        _ = B ^ 2 := by field_simp
        _ ≤ 2 ^ 2 := pow_le_pow_left₀ hB0 hB2 2
    have h3 : (∑ i, (u i - t)) ^ 2 ≤ 2 ^ 2 := le_trans h1 h2
    have := sq_le_sq.mp h3
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
  have hSW : ∑ i, u i = k * t + ∑ i, (u i - t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hSlo : (k : ℝ) * t - 2 ≤ ∑ i, u i := by
    rw [hSW]; have := abs_le.mp hsumw; linarith
  have hS0 : 0 < ∑ i, u i := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hS0.ne']
  · intro i
    exact div_nonneg (hu01 i).1 hS0.le
  · intro i
    have e : (k : ℝ) * (u i / ∑ j, u j) - 1
        = ((k : ℝ) * (u i - t) - ∑ j, (u j - t)) / ∑ j, u j := by
      have := hS0.ne'
      field_simp
      rw [hSW]
      ring
    rw [e, abs_div, abs_of_pos hS0, div_le_iff₀ hS0]
    have h1 : |(k : ℝ) * (u i - t) - ∑ j, (u j - t)| ≤ k * (2 / s) + 2 := by
      calc |(k : ℝ) * (u i - t) - ∑ j, (u j - t)|
          ≤ |(k : ℝ) * (u i - t)| + |∑ j, (u j - t)| := abs_sub _ _
        _ = k * |u i - t| + |∑ j, (u j - t)| := by rw [abs_mul, abs_of_pos hkpos]
        _ ≤ k * (2 / s) + 2 := by
            have := mul_le_mul_of_nonneg_left (hwi i) hkpos.le
            linarith [hsumw]
    have h2 : (k : ℝ) * (2 / s) = 2 * s := by
      rw [← hs2]; field_simp <;> ring
    have h3 : (k : ℝ) * t / 2 ≤ ∑ j, u j := by linarith
    have h4 : 200 / t ^ 3 / s * ((k : ℝ) * t / 2) ≤ 200 / t ^ 3 / s * ∑ j, u j :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 2 * s + 2 ≤ 200 / t ^ 3 / s * ((k : ℝ) * t / 2) := by
      rw [← hs2]
      have e2 : 200 / t ^ 3 / s * (s ^ 2 * t / 2) = 100 * s / t ^ 2 := by
        have := hs0.ne'; have := ht0.ne'
        field_simp <;> ring
      rw [e2, le_div_iff₀ (by positivity)]
      nlinarith only [hs4, mul_le_mul_of_nonneg_left ht1' (by linarith only [hs4] : (0 : ℝ) ≤ 2 * s + 2)]
    linarith [h1, h2, h4, h5]
  · rw [eps_sq_sum t u hS0.ne']
    have hnum : (k : ℝ) ^ 2 * ∑ i, (u i - t) ^ 2 - k * (∑ i, (u i - t)) ^ 2 ≤ k * B ^ 2 := by
      have h1 : (k : ℝ) ^ 2 * ∑ i, (u i - t) ^ 2 ≤ (k : ℝ) ^ 2 * (B ^ 2 / k) :=
        mul_le_mul_of_nonneg_left hWsq (by positivity)
      have h2 : (k : ℝ) ^ 2 * (B ^ 2 / k) = k * B ^ 2 := by field_simp <;> ring
      have h3 : 0 ≤ (k : ℝ) * (∑ i, (u i - t)) ^ 2 := by positivity
      rw [h2] at h1
      linarith only [h1, h3]
    have hden0 : 0 < ((k : ℝ) * t - 2) ^ 2 := pow_pos (by linarith) 2
    have hden : ((k : ℝ) * t - 2) ^ 2 ≤ (∑ j, u j) ^ 2 := pow_le_pow_left₀ (by linarith) hSlo 2
    have hfin := loc_final ht0 ht1 hs4 (by rw [hs2]; exact hkt) hBsq
    rw [hs2] at hfin
    calc ((k : ℝ) ^ 2 * ∑ i, (u i - t) ^ 2 - k * (∑ i, (u i - t)) ^ 2) / (∑ j, u j) ^ 2
        ≤ (k * B ^ 2) / (∑ j, u j) ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ (k * B ^ 2) / ((k : ℝ) * t - 2) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hden0 hden
      _ ≤ 4 * ((1 - t) / t) / k + 200 / t ^ 3 / (k * s) := hfin


end AppendixB
