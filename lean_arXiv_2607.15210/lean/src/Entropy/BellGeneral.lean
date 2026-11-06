import Entropy.Analysis
import Entropy.BellBounds
open Real Finset
noncomputable section
namespace AppendixB
set_option maxHeartbeats 2000000
private lemma general_half_bound (P E K : ℝ) (h : 2 * (P + E) + 1 ≤ K)
    (h2 : K ≤ K ^ 2) : P + E ≤ (1 / 2 : ℝ) * K ^ 2 := by
  linarith only [h, h2]

/-- Prop. app-antisymmetric-bell-entropy-asymptotics, eq. (68), at the level of spectra:
    `ω_{k,r,t}` has eigenvalues `ν_m` with multiplicities `d_m` (Prop. app-spectrum-W), and
    `S_p(ω_{k,r,t}) = 2 log C(k,r) - B_{p,r}(γ)/k² + O(k^{-3})`. -/
theorem bell_output {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      |renyi p (Finset.range (r + 1)) (dm k) (bellNu k r t)
        - (2 * Real.log (Nat.choose k r) - Bpr p r ((1 - t) / t) / k ^ 2)| ≤ C / k ^ 3 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨η₁, C₁, hη₁, hη₁', hC₁, hloc⟩ := psi_local hp
  obtain ⟨C₂, hC₂, hF⟩ := Fp_local p
  have hγ0 : 0 < (1 - t) / t := div_pos (by linarith) ht0
  set γ := (1 - t) / t with hγ
  set R : ℝ := ((r' + 1 : ℕ) : ℝ) with hR
  have hRr' : R = (r' : ℝ) + 1 := by rw [hR]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ R := by rw [hRr']; have := Nat.cast_nonneg (α := ℝ) r'; linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hg00 : 0 < γ / R ^ 2 := by positivity
  obtain ⟨L, ηL, hηL, hL, hlip⟩ := psi_lip hp (show -1 < γ / R ^ 2 by linarith)
  obtain ⟨Bψ, hBψ⟩ := psi_bdd hp (2 * γ) (by positivity)
  have hBψ0 : 0 ≤ Bψ := le_trans (abs_nonneg _) (hBψ 0 (by norm_num) (by positivity))
  set P0 := |psi p (γ / R ^ 2)| with hP0
  set E : ℝ := 2 * (|kappa p| + C₁) * (2 * γ) ^ 2 + (8 * R ^ 3 + 16 * R ^ 4) * Bψ
      + R ^ 2 * L * (12 * γ * R) + (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨C₂ * (R ^ 2 * P0 + E) ^ 2 + |cp p| * E,
    max (max (4 * R + 4) (1 / t + 3)) (max (12 * γ * R / ηL + 1)
      (max (2 * γ / η₁ + 1) (2 * (R ^ 2 * P0 + E) + 1))), fun k hk => ?_⟩
  have hkR : 4 * R + 4 ≤ (k : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hkt : 1 / t + 3 ≤ (k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkL : 12 * γ * R / ηL + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkη : 2 * γ / η₁ + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hk
  have hkX : 2 * (R ^ 2 * P0 + E) + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hk
  have hkpos : (0 : ℝ) < k := by linarith only [hkR, hR1]
  have hk1 : (1 : ℝ) ≤ k := by linarith only [hkR, hR1]
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [mul_nonneg hkpos.le (sub_nonneg.mpr hk1)]
  have hkk3 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg (k : ℝ)) (sub_nonneg.mpr hk1)]
  have hkk4 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 4 := by nlinarith only [mul_nonneg (pow_nonneg hkpos.le 3) (sub_nonneg.mpr hk1)]
  have hk2R : 2 * (r' + 1) ≤ k := by
    have h : ((2 * (r' + 1) : ℕ) : ℝ) ≤ k := by
      push_cast; rw [hRr'] at hkR; linarith
    exact_mod_cast h
  have hk2 : (2 : ℝ) ≤ k := by linarith
  have hk2t : 1 ≤ (k : ℝ) ^ 2 * t := by
    have h1 : 1 / t ≤ (k : ℝ) := by linarith
    rw [div_le_iff₀ ht0] at h1; nlinarith only [h1, mul_le_mul_of_nonneg_right hkk ht0.le]
  obtain ⟨hρ0, hρ1, hρ2⟩ := rkt_bounds ht0 ht1 hk2 hk2t
  rw [← hγ] at hρ1 hρ2
  set ρ := rkt k t with hρ
  set D : ℝ := (Nat.choose k (r' + 1) : ℝ) with hD
  have hD0 : 0 < D := by rw [hD]; exact_mod_cast Nat.choose_pos (by omega)
  have hD0' := hD0.ne'
  have hρη : ρ ≤ η₁ := by
    have h1 : 2 * γ / (k : ℝ) ^ 2 ≤ 2 * γ / (k : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hkpos hkk
    have h2 : 2 * γ / (k : ℝ) ≤ η₁ := by
      rw [div_le_iff₀ hkpos]
      have h3 : 2 * γ / η₁ ≤ k := by linarith
      rw [div_le_iff₀ hη₁] at h3
      linarith
    linarith
  have hρ12 : ρ ≤ 1 / 2 := le_trans hρη hη₁'
  have hρk : ρ * (k : ℝ) ^ 2 ≤ 2 * γ := by
    have h1 := (abs_le.mp hρ2).2
    have h2 : 6 * γ / (k : ℝ) ^ 2 ≤ γ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith only [mul_nonneg hγ0.le (show 0 ≤ (k : ℝ)^2 - 6 by nlinarith only [hkR, hR1])]
    nlinarith only [h1, h2]
  -- Step 1: the spectrum is `(1 + y_m)/D²`
  set y : ℕ → ℝ := fun m => ρ * (D ^ 2 * wm k (r' + 1) m - 1) with hy
  have hD2wm : ∀ m, D ^ 2 * wm k (r' + 1) m
      = (k : ℝ) * ((R - m) * ((k : ℝ) - R - m + 1)) / R ^ 2 := by
    intro m
    have h := D2wm (k := k) (r := r' + 1) (by omega) (by omega) m
    rw [← hR, ← hD] at h
    exact h
  have hwm0 : ∀ m ∈ Finset.range (r' + 1 + 1), 0 ≤ wm k (r' + 1) m := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hm' : (m : ℝ) ≤ R := by
      rw [hRr']; exact_mod_cast (by omega : m ≤ r' + 1)
    have hnn1 : 0 ≤ R - m := by linarith
    have hnn2 : 0 ≤ (k : ℝ) - R - m + 1 := by linarith
    unfold wm
    rw [← hR]
    exact div_nonneg (mul_nonneg hnn1 hnn2) (by positivity)
  have hνy : ∀ m ∈ Finset.range (r' + 1 + 1), bellNu k (r' + 1) t m = (1 + y m) / D ^ 2 := by
    intro m _
    simp only [bellNu, hy]
    rw [← hρ, ← hD]
    field_simp <;> ring
  have hd : ∀ m ∈ Finset.range (r' + 1 + 1), 0 ≤ dm k m := by
    intro m hm
    rw [Finset.mem_range] at hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [dm]
    · have h1 := choose_le_ratio (k := k) (r := r' + 1) (j := m - 1) (by omega) hk2R
      rw [Nat.sub_add_cancel hpos] at h1
      have h2 : 2 * ((r' + 1 : ℕ) : ℝ) / k ≤ 1 := by
        rw [div_le_one hkpos]; exact_mod_cast hk2R
      have h4 : (0 : ℝ) ≤ Nat.choose k m := Nat.cast_nonneg _
      have h3 : (Nat.choose k (m - 1) : ℝ) ≤ Nat.choose k m := by
        nlinarith only [h1, mul_le_mul_of_nonneg_right h2 h4]
      simp only [dm, if_neg (Nat.pos_iff_ne_zero.mp hpos)]
      have h5 : (0 : ℝ) ≤ Nat.choose k (m - 1) := Nat.cast_nonneg _
      exact sub_nonneg.mpr (pow_le_pow_left h5 h3 2)
  have hdM : ∑ m ∈ Finset.range (r' + 1 + 1), dm k m = D ^ 2 := mult_sum k (r' + 1)
  have hdy : ∑ m ∈ Finset.range (r' + 1 + 1), dm k m * y m = 0 := by
    simp only [hy]
    have h1 := trace_identity (k := k) (r := r' + 1) (by omega) (by omega)
    have e : ∀ m, dm k m * (ρ * (D ^ 2 * wm k (r' + 1) m - 1))
        = ρ * D ^ 2 * (dm k m * wm k (r' + 1) m) - ρ * dm k m := by
      intro m; ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, h1, hdM]
    ring
  have hy_lo : ∀ m ∈ Finset.range (r' + 1 + 1), -ρ ≤ y m := by
    intro m hm
    simp only [hy]
    have h2 : 0 ≤ D ^ 2 * wm k (r' + 1) m := mul_nonneg (sq_nonneg D) (hwm0 m hm)
    nlinarith only [mul_nonneg hρ0 h2]
  have hy1 : ∀ m ∈ Finset.range (r' + 1 + 1), -1 < y m := fun m hm => by
    have := hy_lo m hm; linarith
  have hy_hi : ∀ m ∈ Finset.range (r' + 1 + 1), y m ≤ 2 * γ := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hm' : (m : ℝ) ≤ R := by
      rw [hRr']; exact_mod_cast (by omega : m ≤ r' + 1)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hfac : (k : ℝ) * ((R - m) * ((k : ℝ) - R - m + 1)) / R ^ 2 ≤ (k : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h2 : 0 ≤ (k : ℝ) - R - m + 1 := by linarith
      have h5 : (R - m) * ((k : ℝ) - R - m + 1) ≤ R * k :=
        mul_le_mul (by linarith) (by linarith) h2 hR0.le
      have h6 := mul_le_mul_of_nonneg_left h5 hkpos.le
      have h7 : (k : ℝ) * (R * k) ≤ (k : ℝ) ^ 2 * R ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_left hR1 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2 * R)]
      linarith only [h6, h7]
    simp only [hy]
    rw [hD2wm]
    nlinarith only [mul_le_mul_of_nonneg_left hfac hρ0, hρk, hρ0]
  have hψbdd : ∀ m ∈ Finset.range (r' + 1 + 1), |psi p (y m)| ≤ Bψ := fun m hm =>
    hBψ (y m) (by linarith only [hy_lo m hm, hρ12]) (hy_hi m hm)
  -- Step 2: exact expansion
  rw [renyi_congr p _ _ _ _ hνy,
    exact_expansion p (Finset.range (r' + 1 + 1)) (dm k) y (D ^ 2) (by positivity) hd hdM hy1 hdy]
  set X := (∑ m ∈ Finset.range (r' + 1 + 1), dm k m * psi p (y m)) / D ^ 2 with hX
  -- Step 3: estimates
  have hsplit : ∑ m ∈ Finset.range (r' + 1 + 1), dm k m * psi p (y m)
      = (∑ m ∈ Finset.range r', dm k m * psi p (y m)) + dm k r' * psi p (y r')
        + dm k (r' + 1) * psi p (y (r' + 1)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hyR : y (r' + 1) = -ρ := by
    simp only [hy]
    rw [hD2wm, ← hR]
    simp
  -- the term m = r - 1: `y_{r-1}` is close to `γ/R²`
  have hyr : |y r' - γ / R ^ 2| ≤ 12 * γ * R / k := by
    have hRr : R - (r' : ℝ) = 1 := by rw [hRr']; ring
    have e : y r' - γ / R ^ 2
        = (ρ * (k : ℝ) ^ 2 - γ) / R ^ 2 - ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1) := by
      simp only [hy]
      rw [hD2wm]
      have e1 : (k : ℝ) - R - r' + 1 = (k : ℝ) - 2 * R + 2 := by linarith [hRr]
      rw [e1, hRr]
      have := hR0.ne'
      field_simp <;> ring
    rw [e]
    have h1 : |(ρ * (k : ℝ) ^ 2 - γ) / R ^ 2| ≤ 6 * γ / (k : ℝ) ^ 2 := by
      rw [abs_div, abs_of_pos (sq_pos_of_pos hR0)]
      have h2 : |ρ * (k : ℝ) ^ 2 - γ| ≤ 6 * γ / (k : ℝ) ^ 2 := by
        have := hρ2
        rwa [mul_comm ((k : ℝ) ^ 2) ρ] at this
      calc |ρ * (k : ℝ) ^ 2 - γ| / R ^ 2 ≤ |ρ * (k : ℝ) ^ 2 - γ| :=
            div_le_self (abs_nonneg _) (by nlinarith only [hR1])
        _ ≤ 6 * γ / (k : ℝ) ^ 2 := h2
    have hfac0 : 0 ≤ (k : ℝ) * (2 * R - 2) / R ^ 2 :=
      div_nonneg (mul_nonneg hkpos.le (by linarith)) (by positivity)
    have h3 : 0 ≤ ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1) := mul_nonneg hρ0 (by linarith)
    have h4 : ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1) ≤ 6 * γ / k := by
      have h5 : (k : ℝ) * (2 * R - 2) / R ^ 2 ≤ 2 * k := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [mul_nonneg hkpos.le (by nlinarith only [sq_nonneg (R - 1)] : (0 : ℝ) ≤ 2 * R ^ 2 - 2 * R + 2)]
      calc ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1) ≤ (2 * γ / (k : ℝ) ^ 2) * (2 * k + 1) :=
            mul_le_mul hρ1 (by linarith) (by linarith) (by positivity)
        _ ≤ 6 * γ / k := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hkpos]
            nlinarith only [mul_nonneg hγ0.le (mul_nonneg hkpos.le (sub_nonneg.mpr hk1))]
    calc |(ρ * (k : ℝ) ^ 2 - γ) / R ^ 2 - ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1)|
        ≤ |(ρ * (k : ℝ) ^ 2 - γ) / R ^ 2| + |ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1)| :=
          abs_sub _ _
      _ ≤ 6 * γ / (k : ℝ) ^ 2 + 6 * γ / k := by rw [abs_of_nonneg h3]; linarith only [h1, h4]
      _ ≤ 12 * γ * R / k := by
          have h6 : 6 * γ / (k : ℝ) ^ 2 ≤ 6 * γ / k :=
            div_le_div_of_nonneg_left (by positivity) hkpos hkk
          have h7 : 12 * γ / k ≤ 12 * γ * R / k :=
            div_le_div_of_nonneg_right (by nlinarith only [mul_nonneg hγ0.le (sub_nonneg.mpr hR1)]) hkpos.le
          have e2 : 6 * γ / k + 6 * γ / k = 12 * γ / k := by ring
          linarith only [h6, h7, e2]
  have hyL : |y r' - γ / R ^ 2| ≤ ηL := by
    refine le_trans hyr ?_
    rw [div_le_iff₀ hkpos]
    have h3 : 12 * γ * R / ηL ≤ k := by linarith
    rw [div_le_iff₀ hηL] at h3
    linarith
  -- ratio facts for `d_{r-1}/D²`
  have hkr0 : 0 < (k : ℝ) - r' := by
    have := hRr'.symm.le; have := Nat.cast_nonneg (α := ℝ) r'; linarith
  have hkr0' := hkr0.ne'
  have hratio : (Nat.choose k r' : ℝ) = D * R / ((k : ℝ) - r') := by
    have h := choose_succ_ratio (k := k) (j := r') (by omega)
    rw [eq_div_iff hkr0', hD, hRr']
    linarith [h]
  have hT2a : |(R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2| ≤ 8 * R ^ 3 / (k : ℝ) ^ 3 := by
    have hr'R : (r' : ℝ) ≤ R := by rw [hRr']; linarith
    have hr'0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg _
    have hkr : (k : ℝ) / 2 ≤ (k : ℝ) - r' := by linarith
    have e : (R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2
        = R ^ 2 * ((r' : ℝ) * (2 * k - r')) / ((k : ℝ) ^ 2 * ((k : ℝ) - r') ^ 2) := by
      field_simp <;> ring
    have hnum : 0 ≤ R ^ 2 * ((r' : ℝ) * (2 * k - r')) :=
      mul_nonneg (by positivity) (mul_nonneg hr'0 (by linarith))
    rw [e, abs_of_nonneg (div_nonneg hnum (by positivity)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : ((k : ℝ) / 2) ^ 2 ≤ ((k : ℝ) - r') ^ 2 := pow_le_pow_left (by positivity) hkr 2
    have h3 : (r' : ℝ) * (2 * k - r') ≤ R * (2 * k) := by
      nlinarith only [mul_le_mul_of_nonneg_right hr'R (by linarith : (0 : ℝ) ≤ 2 * k - r'),
        mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) * k - r' ≤ 2 * k) hR0.le]
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ R ^ 2 * (k : ℝ) ^ 3)
    have h5 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * R ^ 3 * (k : ℝ) ^ 2)
    nlinarith only [h4, h5]
  have hT2b : r' ≠ 0 → ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 ≤ 16 * R ^ 4 / (k : ℝ) ^ 4 := by
    intro hr0
    have h := choose_le_pow (k := k) (r := r' + 1) hk2R 2 (by omega)
    have e : r' + 1 - 2 = r' - 1 := by omega
    rw [e, ← hD, ← hR] at h
    have h1 : (Nat.choose k (r' - 1) : ℝ) / D ≤ (2 * R / k) ^ 2 := by
      rw [div_le_iff₀ hD0]; exact h
    have h0 : (0 : ℝ) ≤ (Nat.choose k (r' - 1) : ℝ) / D := by positivity
    calc ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 ≤ ((2 * R / k) ^ 2) ^ 2 := pow_le_pow_left h0 h1 2
      _ = 16 * R ^ 4 / (k : ℝ) ^ 4 := by field_simp <;> ring
  have hT2d : |dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2| ≤ (8 * R ^ 3 + 16 * R ^ 4) / (k : ℝ) ^ 3 := by
    have hdmr : dm k r' / D ^ 2 = (R / ((k : ℝ) - r')) ^ 2
        - (if r' = 0 then 0 else ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2) := by
      unfold dm
      rw [hratio]
      split_ifs <;> field_simp <;> ring
    rw [hdmr]
    have h8 : 8 * R ^ 3 / (k : ℝ) ^ 3 ≤ (8 * R ^ 3 + 16 * R ^ 4) / (k : ℝ) ^ 3 :=
      div_le_div_of_nonneg_right (by nlinarith only [pow_nonneg hR0.le 4]) (by positivity)
    split_ifs with hr0
    · rw [sub_zero]; exact le_trans hT2a h8
    · have h1 := hT2b hr0
      have h2 : 16 * R ^ 4 / (k : ℝ) ^ 4 ≤ 16 * R ^ 4 / (k : ℝ) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hkk4
      have h3 : 0 ≤ ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 := sq_nonneg _
      have e : (R / ((k : ℝ) - r')) ^ 2 - ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 - R ^ 2 / (k : ℝ) ^ 2
          = ((R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2)
            - ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 := by ring
      rw [e]
      calc |((R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2) - ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2|
          ≤ |(R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2|
            + |((Nat.choose k (r' - 1) : ℝ) / D) ^ 2| := abs_sub _ _
        _ ≤ 8 * R ^ 3 / (k : ℝ) ^ 3 + 16 * R ^ 4 / (k : ℝ) ^ 3 := by
            rw [abs_of_nonneg h3]; linarith only [hT2a, h1, h2]
        _ = (8 * R ^ 3 + 16 * R ^ 4) / (k : ℝ) ^ 3 := by ring
  -- the four contributions to `X - R² ψ(γ/R²)/k²`
  have hB1 : |(∑ m ∈ Finset.range r', dm k m * psi p (y m)) / D ^ 2|
      ≤ (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) / (k : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hD0), div_le_iff₀ (sq_pos_of_pos hD0)]
    have hterm : ∀ m ∈ Finset.range r',
        |dm k m * psi p (y m)| ≤ 2 * ((2 * R / k) ^ 2 * D) ^ 2 * Bψ := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [abs_mul]
      have h1 := dm_small (k := k) (r' := r') (m := m) hk2R hm
      rw [← hR, ← hD] at h1
      have h2 := hψbdd m (by rw [Finset.mem_range]; omega)
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    calc |∑ m ∈ Finset.range r', dm k m * psi p (y m)|
        ≤ ∑ m ∈ Finset.range r', |dm k m * psi p (y m)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.range r', 2 * ((2 * R / k) ^ 2 * D) ^ 2 * Bψ := Finset.sum_le_sum hterm
      _ = (r' : ℝ) * (2 * ((2 * R / k) ^ 2 * D) ^ 2 * Bψ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) / (k : ℝ) ^ 3 * D ^ 2 := by
          have e : (r' : ℝ) * (2 * ((2 * R / k) ^ 2 * D) ^ 2 * Bψ)
              = (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) * D ^ 2 / (k : ℝ) ^ 4 := by
            field_simp <;> ring
          have e2 : (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) / (k : ℝ) ^ 3 * D ^ 2
              = (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) * D ^ 2 / (k : ℝ) ^ 3 := by ring
          rw [e, e2]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkk4
  have hB2 : |(dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2) * psi p (y r')|
      ≤ (8 * R ^ 3 + 16 * R ^ 4) * Bψ / (k : ℝ) ^ 3 := by
    rw [abs_mul]
    have h1 := hψbdd r' (by rw [Finset.mem_range]; omega)
    calc |dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2| * |psi p (y r')|
        ≤ (8 * R ^ 3 + 16 * R ^ 4) / (k : ℝ) ^ 3 * Bψ :=
          mul_le_mul hT2d h1 (abs_nonneg _) (by positivity)
      _ = (8 * R ^ 3 + 16 * R ^ 4) * Bψ / (k : ℝ) ^ 3 := by ring
  have hB3 : |R ^ 2 / (k : ℝ) ^ 2 * (psi p (y r') - psi p (γ / R ^ 2))|
      ≤ R ^ 2 * L * (12 * γ * R) / (k : ℝ) ^ 3 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have h2 : |psi p (y r') - psi p (γ / R ^ 2)| ≤ L * (12 * γ * R / k) :=
      le_trans (hlip (y r') hyL) (mul_le_mul_of_nonneg_left hyr hL)
    calc R ^ 2 / (k : ℝ) ^ 2 * |psi p (y r') - psi p (γ / R ^ 2)|
        ≤ R ^ 2 / (k : ℝ) ^ 2 * (L * (12 * γ * R / k)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = R ^ 2 * L * (12 * γ * R) / (k : ℝ) ^ 3 := by field_simp <;> ring
  have hB4 : |dm k (r' + 1) / D ^ 2 * psi p (y (r' + 1))|
      ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by
    rw [hyR, abs_mul]
    have hdR : |dm k (r' + 1) / D ^ 2| ≤ 1 := by
      have h0 := hd (r' + 1) (by rw [Finset.mem_range]; omega)
      have h1 : dm k (r' + 1) ≤ D ^ 2 := by
        simp only [dm, if_neg (Nat.add_one_ne_zero r'), Nat.add_sub_cancel]
        rw [← hD]
        nlinarith only [sq_nonneg (Nat.choose k r' : ℝ)]
      rw [abs_div, abs_of_nonneg h0, abs_of_pos (by positivity), div_le_one (by positivity)]
      exact h1
    have hψ := psi_quad hη₁' hC₁ hloc (-ρ) (by rw [abs_neg, abs_of_nonneg hρ0]; exact hρη)
    have hρ2' : ρ ^ 2 ≤ (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by
      calc ρ ^ 2 ≤ (2 * γ / (k : ℝ) ^ 2) ^ 2 := pow_le_pow_left hρ0 hρ1 2
        _ = (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by rw [div_pow]; ring
    have h4 : (2 * γ) ^ 2 / (k : ℝ) ^ 4 ≤ (2 * γ) ^ 2 / (k : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hkk4
    have h5 : (|kappa p| + C₁) * (-ρ) ^ 2 ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by
      rw [neg_sq]
      have := mul_le_mul_of_nonneg_left (le_trans hρ2' h4)
        (by positivity : (0 : ℝ) ≤ |kappa p| + C₁)
      calc (|kappa p| + C₁) * ρ ^ 2 ≤ (|kappa p| + C₁) * ((2 * γ) ^ 2 / (k : ℝ) ^ 3) := this
        _ = (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by ring
    calc |dm k (r' + 1) / D ^ 2| * |psi p (-ρ)| ≤ 1 * ((|kappa p| + C₁) * (-ρ) ^ 2) :=
          mul_le_mul hdR hψ (abs_nonneg _) zero_le_one
      _ ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by rw [one_mul]; exact h5
  have hXY : |X - R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2| ≤ E / (k : ℝ) ^ 3 := by
    rw [hX, hsplit]
    have e : ((∑ m ∈ Finset.range r', dm k m * psi p (y m)) + dm k r' * psi p (y r')
          + dm k (r' + 1) * psi p (y (r' + 1))) / D ^ 2 - R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2
        = (∑ m ∈ Finset.range r', dm k m * psi p (y m)) / D ^ 2
          + (dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2) * psi p (y r')
          + R ^ 2 / (k : ℝ) ^ 2 * (psi p (y r') - psi p (γ / R ^ 2))
          + dm k (r' + 1) / D ^ 2 * psi p (y (r' + 1)) := by ring
    rw [e]
    have h1 := abs_add_three ((∑ m ∈ Finset.range r', dm k m * psi p (y m)) / D ^ 2)
      ((dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2) * psi p (y r'))
      (R ^ 2 / (k : ℝ) ^ 2 * (psi p (y r') - psi p (γ / R ^ 2)))
    have h2 := abs_add ((∑ m ∈ Finset.range r', dm k m * psi p (y m)) / D ^ 2
      + (dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2) * psi p (y r')
      + R ^ 2 / (k : ℝ) ^ 2 * (psi p (y r') - psi p (γ / R ^ 2)))
      (dm k (r' + 1) / D ^ 2 * psi p (y (r' + 1)))
    have h3 : 0 ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by positivity
    have e2 : E / (k : ℝ) ^ 3
        = (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) / (k : ℝ) ^ 3
          + (8 * R ^ 3 + 16 * R ^ 4) * Bψ / (k : ℝ) ^ 3
          + R ^ 2 * L * (12 * γ * R) / (k : ℝ) ^ 3
          + (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3
          + (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by
      rw [hE]; ring
    rw [e2]
    linarith only [hB1, hB2, hB3, hB4, h1, h2, h3]
  have hXb : |X| ≤ (R ^ 2 * P0 + E) / (k : ℝ) ^ 2 := by
    have h1 : |X| ≤ |R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2| + E / (k : ℝ) ^ 3 := by
      have := abs_sub_abs_le_abs_sub X (R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2)
      linarith only [this, hXY]
    have h2 : |R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2| = R ^ 2 * P0 / (k : ℝ) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < R ^ 2),
        abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
    have h3 : E / (k : ℝ) ^ 3 ≤ E / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hE0 (by positivity) hkk3
    have e : R ^ 2 * P0 / (k : ℝ) ^ 2 + E / (k : ℝ) ^ 2 = (R ^ 2 * P0 + E) / (k : ℝ) ^ 2 := by
      ring
    linarith only [h1, h2, h3, e]
  have hX12 : |X| ≤ 1 / 2 := by
    refine le_trans hXb ?_
    rw [div_le_iff₀ (by positivity)]
    exact general_half_bound (R ^ 2 * P0) E (k : ℝ) hkX hkk
  have hlog : Real.log (D ^ 2) = 2 * Real.log D := by
    rw [Real.log_pow]; norm_num
  have hB := B_identity p R γ hR0.ne'
  have e : Real.log (D ^ 2) + Fp p X - (2 * Real.log D - Bpr p R γ / (k : ℝ) ^ 2)
      = Fp p X - cp p * (R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2) := by
    rw [hlog, mul_div_assoc', hB]; ring
  rw [e]
  calc |Fp p X - cp p * (R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2)|
      ≤ C₂ * X ^ 2 + |cp p| * (E / (k : ℝ) ^ 3) := final_step hF hXY hX12
    _ ≤ C₂ * ((R ^ 2 * P0 + E) / (k : ℝ) ^ 2) ^ 2 + |cp p| * (E / (k : ℝ) ^ 3) := by
        have h1 : X ^ 2 ≤ ((R ^ 2 * P0 + E) / (k : ℝ) ^ 2) ^ 2 := by
          rw [← sq_abs X]; exact pow_le_pow_left (abs_nonneg _) hXb 2
        have := mul_le_mul_of_nonneg_left h1 hC₂
        linarith only [this]
    _ ≤ (C₂ * (R ^ 2 * P0 + E) ^ 2 + |cp p| * E) / (k : ℝ) ^ 3 := by
        have e1 : C₂ * ((R ^ 2 * P0 + E) / (k : ℝ) ^ 2) ^ 2
            = C₂ * (R ^ 2 * P0 + E) ^ 2 / (k : ℝ) ^ 4 := by
          rw [div_pow]; ring
        have e2 : C₂ * (R ^ 2 * P0 + E) ^ 2 / (k : ℝ) ^ 4
            ≤ C₂ * (R ^ 2 * P0 + E) ^ 2 / (k : ℝ) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hkk4
        have e3 : (C₂ * (R ^ 2 * P0 + E) ^ 2 + |cp p| * E) / (k : ℝ) ^ 3
            = C₂ * (R ^ 2 * P0 + E) ^ 2 / (k : ℝ) ^ 3 + |cp p| * (E / (k : ℝ) ^ 3) := by ring
        linarith only [e1, e2, e3]
end AppendixB
end
