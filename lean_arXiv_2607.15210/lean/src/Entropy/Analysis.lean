import Entropy.Defs

open Real Finset
noncomputable section
namespace AppendixB

set_option maxHeartbeats 800000

lemma renyi_congr (p : ℝ) {ι : Type*} (s : Finset ι) (d ν ν' : ι → ℝ)
    (h : ∀ j ∈ s, ν j = ν' j) : renyi p s d ν = renyi p s d ν' := by
  unfold renyi
  split_ifs
  · rw [Finset.sum_congr rfl (fun j hj => by rw [h j hj])]
  · rw [Finset.sum_congr rfl (fun j hj => by rw [h j hj])]

/-! ## 2. Algebraic identities -/

/-- (app-cp-kappa). -/
lemma cp_mul_kappa (p : ℝ) : cp p * kappa p = -p / 2 := by
  unfold cp kappa
  split_ifs with h
  · subst h; norm_num
  · have h1 : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    field_simp <;> ring

/-- (app-B-identity): `c_p r² ψ_p(γ/r²) = -B_{p,r}(γ)`. -/
lemma B_identity (p r γ : ℝ) (hr : r ≠ 0) :
    cp p * (r ^ 2 * psi p (γ / r ^ 2)) = -Bpr p r γ := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  unfold cp psi Bpr
  split_ifs with h
  · set L := Real.log (1 + γ / r ^ 2)
    have e : r ^ 2 * ((1 + γ / r ^ 2) * L - γ / r ^ 2) = (r ^ 2 + γ) * L - γ := by
      field_simp <;> ring
    rw [e]
    ring
  · set P := (1 + γ / r ^ 2) ^ p
    have h1 : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    field_simp <;> ring

/-- `B_{p,1}((1-t)/t) = A_p(t)`. -/
lemma B_one_eq_A (p t : ℝ) (ht : 0 < t) : Bpr p 1 ((1 - t) / t) = Ap p t := by
  have h1 : (1 : ℝ) + (1 - t) / t / 1 ^ 2 = t⁻¹ := by
    field_simp
  have hinv : (t⁻¹) ^ p = t ^ (-p) := by
    rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le]
  unfold Bpr Ap
  split_ifs with h
  · rw [h1]
    have ht0 : t ≠ 0 := ht.ne'
    have e : (1 - t) / t = t⁻¹ - 1 := by field_simp
    rw [e]
    ring
  · rw [h1, hinv]
    have ht0 : t ≠ 0 := ht.ne'
    have hp1 : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hp2 : p - 1 ≠ 0 := sub_ne_zero.mpr h
    have e : (1 - t) / t = t⁻¹ - 1 := by field_simp
    rw [e]
    field_simp <;> ring

/-- The arithmetic step of Prop. app-spectrum-G. -/
lemma eig_recursion (k r m : ℝ) :
    (r - 1 - m) * (k - r - m + 2) + (k - 2 * r + 2) = (r - m) * (k - r - m + 1) := by
  ring

/-! ## 3. Proposition app-exact-expansion -/

theorem exact_expansion (p : ℝ) {ι : Type*} (s : Finset ι) (d y : ι → ℝ) (M : ℝ)
    (hM : 0 < M) (hd : ∀ j ∈ s, 0 ≤ d j) (hdM : ∑ j ∈ s, d j = M)
    (hy : ∀ j ∈ s, -1 < y j) (hdy : ∑ j ∈ s, d j * y j = 0) :
    renyi p s d (fun j => (1 + y j) / M)
      = Real.log M + Fp p ((∑ j ∈ s, d j * psi p (y j)) / M) := by
  have hM0 : M ≠ 0 := hM.ne'
  by_cases hp : p = 1
  · subst hp
    simp only [renyi, Fp, psi, eq_self_iff_true, if_true]
    have hlog : ∀ j ∈ s, Real.log ((1 + y j) / M) = Real.log (1 + y j) - Real.log M :=
      fun j hj => Real.log_div (by linarith [hy j hj]) hM0
    have hterm : ∀ j ∈ s, d j * ((1 + y j) / M * Real.log ((1 + y j) / M))
        = (d j * ((1 + y j) * Real.log (1 + y j) - y j)) / M + (d j * y j) / M
          - (d j + d j * y j) * Real.log M / M := by
      intro j hj
      rw [hlog j hj]
      field_simp <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_mul,
      Finset.sum_add_distrib, hdM, hdy]
    field_simp <;> ring
  · simp only [renyi, Fp, psi, if_neg hp]
    have hpos : ∀ j ∈ s, 0 < 1 + y j := fun j hj => by linarith [hy j hj]
    have h1 : ∑ j ∈ s, d j * ((1 + y j) / M) ^ p
        = (∑ j ∈ s, d j * (1 + y j) ^ p) / M ^ p := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Real.div_rpow (hpos j hj).le hM.le]
      ring
    have h2 : ∑ j ∈ s, d j * (1 + y j) ^ p
        = M + ∑ j ∈ s, d j * ((1 + y j) ^ p - 1 - p * y j) := by
      have : ∀ j ∈ s, d j * (1 + y j) ^ p
          = d j + p * (d j * y j) + d j * ((1 + y j) ^ p - 1 - p * y j) := by
        intro j _
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hdM, hdy]
      ring
    have hex : ∃ j ∈ s, 0 < d j := by
      by_contra hcon
      push_neg at hcon
      have := Finset.sum_nonpos hcon
      linarith
    have hpos2 : 0 < ∑ j ∈ s, d j * (1 + y j) ^ p := by
      obtain ⟨j, hj, hdj⟩ := hex
      exact Finset.sum_pos'
        (fun i hi => mul_nonneg (hd i hi) (Real.rpow_nonneg (hpos i hi).le _))
        ⟨j, hj, mul_pos hdj (Real.rpow_pos_of_pos (hpos j hj) _)⟩
    rw [h1]
    rw [h2] at hpos2 ⊢
    set G := ∑ j ∈ s, d j * ((1 + y j) ^ p - 1 - p * y j) with hG
    have h1p : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
    have hMG : M + G = M * (1 + G / M) := by
      field_simp
    have h3 : 0 < 1 + G / M := by
      have e : 1 + G / M = (M + G) / M := by field_simp
      rw [e]
      exact div_pos hpos2 hM
    rw [Real.log_div hpos2.ne' (Real.rpow_pos_of_pos hM p).ne', Real.log_rpow hM, hMG,
      Real.log_mul hM0 h3.ne']
    field_simp <;> ring

/-! ## 4. Proposition app-local-bounds -/

/-- `|log(1+x) - x| ≤ 2x²` for `|x| ≤ 1/2`. -/
lemma log_bound1 {x : ℝ} (hx : |x| ≤ 1 / 2) : |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  have e : (∑ i ∈ Finset.range 1, (-x) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -x)
      = Real.log (1 + x) - x := by
    simp only [Finset.sum_range_one, sub_neg_eq_add]
    push_cast
    ring
  rw [e, abs_neg] at h
  have h1 : 0 < 1 - |x| := by linarith
  refine le_trans h ?_
  rw [div_le_iff₀ h1]
  have hx2 : |x| ^ (1 + 1) = x ^ 2 := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, sq_abs]
  rw [hx2]
  nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * |x|)]

/-- `|log(1+y) - (y - y²/2)| ≤ 2|y|³` for `|y| ≤ 1/2`. -/
lemma log_bound2 {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |Real.log (1 + y) - (y - y ^ 2 / 2)| ≤ 2 * |y| ^ 3 := by
  have hx : |(-y)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  have e : (∑ i ∈ Finset.range 2, (-y) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -y)
      = Real.log (1 + y) - (y - y ^ 2 / 2) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add]
    push_cast
    ring
  rw [e, abs_neg] at h
  have h1 : 0 < 1 - |y| := by linarith
  refine le_trans h ?_
  rw [div_le_iff₀ h1]
  have e3 : |y| ^ (2 + 1) = |y| ^ 3 := by norm_num
  rw [e3]
  have h0 : 0 ≤ |y| ^ 3 := by positivity
  nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - 2 * |y|)]

/-- `|e^z - 1 - z - z²/2| ≤ |z|³` for `|z| ≤ 1`. -/
lemma exp_bound2 {z : ℝ} (hz : |z| ≤ 1) : |Real.exp z - (1 + z + z ^ 2 / 2)| ≤ |z| ^ 3 := by
  have h := Real.exp_bound hz (show 0 < 3 by norm_num)
  have e : ∑ i ∈ Finset.range 3, z ^ i / (Nat.factorial i : ℝ) = 1 + z + z ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
      Nat.factorial_one, Nat.factorial_two]
    push_cast
    ring
  rw [e] at h
  refine le_trans h ?_
  have h0 : 0 ≤ |z| ^ 3 := by positivity
  have hc : ((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * ((3 : ℕ) : ℝ)) ≤ 1 := by
    norm_num [Nat.factorial]
  calc |z| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * ((3 : ℕ) : ℝ)))
      ≤ |z| ^ 3 * 1 := mul_le_mul_of_nonneg_left hc h0
    _ = |z| ^ 3 := mul_one _

/-- Prop. app-local-bounds (i), case `p ≠ 1`, with explicit constants. -/
lemma rpow_bound {p y : ℝ} (hp : 0 < p) (hy : |y| ≤ 1 / 2) (hyp : 4 * p * |y| ≤ 1) :
    |(1 + y) ^ p - 1 - p * y - p * (p - 1) / 2 * y ^ 2|
      ≤ (8 * p ^ 3 + 3 * p ^ 2 + 2 * p) * |y| ^ 3 := by
  have hpos : 0 < 1 + y := by have := neg_abs_le y; linarith
  have ha := abs_nonneg y
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have h3 : |y| ^ 3 ≤ |y| ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hy (pow_nonneg ha 2)
    nlinarith [this]
  have h4 : |y| ^ 2 ≤ |y| / 2 := by
    have := mul_le_mul_of_nonneg_right hy ha
    nlinarith [this]
  have hb1 : |Real.log (1 + y) - (y - y ^ 2 / 2)| ≤ 2 * |y| ^ 3 := log_bound2 hy
  set L := Real.log (1 + y) with hL
  set e1 := L - (y - y ^ 2 / 2) with he1
  have hy2' : 0 ≤ y ^ 2 / 2 := by positivity
  have hLb : |L| ≤ 2 * |y| := by
    have hL' : L = y - y ^ 2 / 2 + e1 := by rw [he1]; ring
    have h1 : |y - y ^ 2 / 2 + e1| ≤ |y| + y ^ 2 / 2 + |e1| := by
      calc |y - y ^ 2 / 2 + e1| ≤ |y - y ^ 2 / 2| + |e1| := abs_add _ _
        _ ≤ |y| + |y ^ 2 / 2| + |e1| := by
            have := abs_sub y (y ^ 2 / 2)
            linarith
        _ = |y| + y ^ 2 / 2 + |e1| := by rw [abs_of_nonneg hy2']
    rw [hL']
    linarith [h1, hb1, h3, h4, hy2]
  set u := L * p with hu
  have hub : |u| ≤ 2 * p * |y| := by
    rw [hu, abs_mul, abs_of_pos hp]
    nlinarith [hLb]
  have hu1 : |u| ≤ 1 := by nlinarith [hub, hyp]
  have hexp := exp_bound2 hu1
  set E2 := Real.exp u - (1 + u + u ^ 2 / 2) with hE2
  have hrp : (1 + y) ^ p = Real.exp u := by
    rw [Real.rpow_def_of_pos hpos]
  have key : (1 + y) ^ p - 1 - p * y - p * (p - 1) / 2 * y ^ 2
      = E2 + p * e1 + p ^ 2 / 2 * ((e1 - y ^ 2 / 2) * (2 * y - y ^ 2 / 2 + e1)) := by
    rw [hrp, hE2, he1, hu]
    ring
  have hE2b : |E2| ≤ 8 * p ^ 3 * |y| ^ 3 := by
    calc |E2| ≤ |u| ^ 3 := hexp
      _ ≤ (2 * p * |y|) ^ 3 := pow_le_pow_left (abs_nonneg u) hub 3
      _ = 8 * p ^ 3 * |y| ^ 3 := by ring
  have he1b : |p * e1| ≤ 2 * p * |y| ^ 3 := by
    rw [abs_mul, abs_of_pos hp]
    nlinarith [hb1]
  have hA : |e1 - y ^ 2 / 2| ≤ 3 / 2 * |y| ^ 2 := by
    have := abs_sub e1 (y ^ 2 / 2)
    rw [abs_of_nonneg hy2'] at this
    linarith [hb1, hy2, h3]
  have hB : |2 * y - y ^ 2 / 2 + e1| ≤ 3 * |y| := by
    have h1 : |2 * y - y ^ 2 / 2 + e1| ≤ 2 * |y| + y ^ 2 / 2 + |e1| := by
      calc |2 * y - y ^ 2 / 2 + e1| ≤ |2 * y - y ^ 2 / 2| + |e1| := abs_add _ _
        _ ≤ |2 * y| + |y ^ 2 / 2| + |e1| := by
            have := abs_sub (2 * y) (y ^ 2 / 2)
            linarith
        _ = 2 * |y| + y ^ 2 / 2 + |e1| := by
            rw [abs_mul, abs_two, abs_of_nonneg hy2']
    linarith [h1, hb1, hy2, h3, h4]
  have hC : |p ^ 2 / 2 * ((e1 - y ^ 2 / 2) * (2 * y - y ^ 2 / 2 + e1))|
      ≤ 3 * p ^ 2 * |y| ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < p ^ 2 / 2)]
    have h5 := mul_le_mul hA hB (abs_nonneg _) (by positivity)
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ p ^ 2 / 2)
    have h7 : 0 ≤ p ^ 2 * |y| ^ 3 := by positivity
    nlinarith [h6, h7]
  rw [key]
  calc |E2 + p * e1 + p ^ 2 / 2 * ((e1 - y ^ 2 / 2) * (2 * y - y ^ 2 / 2 + e1))|
      ≤ |E2| + |p * e1| + |p ^ 2 / 2 * ((e1 - y ^ 2 / 2) * (2 * y - y ^ 2 / 2 + e1))| :=
        (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ 8 * p ^ 3 * |y| ^ 3 + 2 * p * |y| ^ 3 + 3 * p ^ 2 * |y| ^ 3 := by
        linarith [hE2b, he1b, hC]
    _ = (8 * p ^ 3 + 3 * p ^ 2 + 2 * p) * |y| ^ 3 := by ring

/-- Prop. app-local-bounds (i), case `p = 1`. -/
lemma xlogx_bound {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |(1 + y) * Real.log (1 + y) - y - y ^ 2 / 2| ≤ 4 * |y| ^ 3 := by
  have hb := log_bound2 hy
  set e1 := Real.log (1 + y) - (y - y ^ 2 / 2) with he1
  have key : (1 + y) * Real.log (1 + y) - y - y ^ 2 / 2 = -(y ^ 3 / 2) + (1 + y) * e1 := by
    rw [he1]; ring
  rw [key]
  have h1 : |-(y ^ 3 / 2)| = |y| ^ 3 / 2 := by
    rw [abs_neg, abs_div, abs_pow, abs_two]
  have h2 : |(1 + y) * e1| ≤ 3 / 2 * (2 * |y| ^ 3) := by
    rw [abs_mul]
    have h3 : |1 + y| ≤ 3 / 2 := by
      have := abs_add (1 : ℝ) y
      rw [abs_one] at this
      linarith
    exact mul_le_mul h3 hb (abs_nonneg _) (by norm_num)
  calc |-(y ^ 3 / 2) + (1 + y) * e1| ≤ |-(y ^ 3 / 2)| + |(1 + y) * e1| := abs_add _ _
    _ ≤ |y| ^ 3 / 2 + 3 / 2 * (2 * |y| ^ 3) := by rw [h1]; linarith
    _ ≤ 4 * |y| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg y) 3]

/-- Prop. app-local-bounds (i). -/
lemma psi_local {p : ℝ} (hp : 0 < p) :
    ∃ η C : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ 0 ≤ C ∧
      ∀ y, |y| ≤ η → |psi p y - kappa p * y ^ 2| ≤ C * |y| ^ 3 := by
  by_cases h : p = 1
  · refine ⟨1 / 2, 4, by norm_num, le_rfl, by norm_num, fun y hy => ?_⟩
    have := xlogx_bound hy
    simp only [psi, kappa, if_pos h]
    convert this using 2 <;> ring
  · refine ⟨min (1 / 2) (1 / (4 * p)), 8 * p ^ 3 + 3 * p ^ 2 + 2 * p,
      lt_min (by norm_num) (by positivity), min_le_left _ _, by positivity, fun y hy => ?_⟩
    have hy1 : |y| ≤ 1 / 2 := le_trans hy (min_le_left _ _)
    have hy2 : 4 * p * |y| ≤ 1 := by
      have := le_trans hy (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith [this]
    have := rpow_bound hp hy1 hy2
    simp only [psi, kappa, if_neg h]
    convert this using 2 <;> ring

/-- Prop. app-local-bounds (ii). -/
lemma Fp_local (p : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |x| ≤ 1 / 2 → |Fp p x - cp p * x| ≤ C * x ^ 2 := by
  by_cases h : p = 1
  · refine ⟨0, le_rfl, fun x _ => ?_⟩
    simp [Fp, cp, h]
  · have h1 : 0 < |1 - p| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
    refine ⟨2 / |1 - p|, by positivity, fun x hx => ?_⟩
    simp only [Fp, cp, if_neg h]
    have hb := log_bound1 hx
    have e : Real.log (1 + x) / (1 - p) - 1 / (1 - p) * x = (Real.log (1 + x) - x) / (1 - p) := by
      ring
    rw [e, abs_div, div_le_iff₀ h1]
    calc |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := hb
      _ = 2 / |1 - p| * x ^ 2 * |1 - p| := by field_simp

/-- `|ψ_p(δ)| ≤ (|κ_p| + C)|δ|` near `0`. -/
lemma psi_small {p η C : ℝ} (hη' : η ≤ 1 / 2) (hC : 0 ≤ C)
    (hloc : ∀ y, |y| ≤ η → |psi p y - kappa p * y ^ 2| ≤ C * |y| ^ 3) :
    ∀ δ, |δ| ≤ η → |psi p δ| ≤ (|kappa p| + C) * |δ| := by
  intro δ hδ
  have h1 := hloc δ hδ
  have hd0 := abs_nonneg δ
  have hd1 : |δ| ≤ 1 := by linarith
  have h2 : |kappa p * δ ^ 2| ≤ |kappa p| * |δ| := by
    rw [abs_mul, abs_pow]
    have : |δ| ^ 2 ≤ |δ| := by nlinarith
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have h3 : C * |δ| ^ 3 ≤ C * |δ| := by
    have : |δ| ^ 3 ≤ |δ| := pow_le_of_le_one hd0 hd1 (by norm_num)
    exact mul_le_mul_of_nonneg_left this hC
  have h4 : |psi p δ| ≤ |psi p δ - kappa p * δ ^ 2| + |kappa p * δ ^ 2| := by
    calc |psi p δ| = |(psi p δ - kappa p * δ ^ 2) + kappa p * δ ^ 2| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add _ _
  nlinarith [h1, h2, h3, h4]

/-- Prop. app-local-bounds (iii), Lipschitz part, near a fixed point `ys > -1`. -/
lemma psi_lip {p : ℝ} (hp : 0 < p) {ys : ℝ} (hys : -1 < ys) :
    ∃ L η : ℝ, 0 < η ∧ 0 ≤ L ∧
      ∀ y, |y - ys| ≤ η → |psi p y - psi p ys| ≤ L * |y - ys| := by
  obtain ⟨η₀, C, hη₀, hη₀', hC, hloc⟩ := psi_local hp
  have hsmall := psi_small hη₀' hC hloc
  have hs : 0 < 1 + ys := by linarith
  have hδ : ∀ y, |y - ys| ≤ η₀ * (1 + ys) → |(y - ys) / (1 + ys)| ≤ η₀ := by
    intro y hy
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact hy
  by_cases h1 : p = 1
  · refine ⟨|Real.log (1 + ys)| + |kappa p| + C, η₀ * (1 + ys), by positivity, by positivity,
      fun y hy => ?_⟩
    set δ := (y - ys) / (1 + ys) with hδdef
    have hδb := hδ y hy
    have hδ1 : 0 < 1 + δ := by have := neg_abs_le δ; linarith
    have hyd : y = ys + (1 + ys) * δ := by
      rw [hδdef]; field_simp
    have hfac : 1 + y = (1 + ys) * (1 + δ) := by rw [hyd]; ring
    have hdiff : psi p y - psi p ys = (1 + ys) * (δ * Real.log (1 + ys) + psi p δ) := by
      simp only [psi, if_pos h1]
      rw [hfac, Real.log_mul hs.ne' hδ1.ne']
      set A := Real.log (1 + ys)
      set B := Real.log (1 + δ)
      rw [hyd]
      ring
    have hδy : (1 + ys) * |δ| = |y - ys| := by
      rw [hδdef, abs_div, abs_of_pos hs]
      field_simp
    rw [hdiff, abs_mul, abs_of_pos hs]
    have hψ := hsmall δ hδb
    have hin : |δ * Real.log (1 + ys) + psi p δ|
        ≤ |δ| * |Real.log (1 + ys)| + (|kappa p| + C) * |δ| := by
      calc |δ * Real.log (1 + ys) + psi p δ| ≤ |δ * Real.log (1 + ys)| + |psi p δ| :=
            abs_add _ _
        _ ≤ |δ| * |Real.log (1 + ys)| + (|kappa p| + C) * |δ| := by
            rw [abs_mul]; linarith
    calc (1 + ys) * |δ * Real.log (1 + ys) + psi p δ|
        ≤ (1 + ys) * (|δ| * |Real.log (1 + ys)| + (|kappa p| + C) * |δ|) :=
          mul_le_mul_of_nonneg_left hin hs.le
      _ = (|Real.log (1 + ys)| + |kappa p| + C) * ((1 + ys) * |δ|) := by ring
      _ = (|Real.log (1 + ys)| + |kappa p| + C) * |y - ys| := by rw [hδy]
  · have hQ : 0 < (1 + ys) ^ p := Real.rpow_pos_of_pos hs p
    refine ⟨((1 + ys) ^ p * (p + |kappa p| + C) + p * (1 + ys)) / (1 + ys), η₀ * (1 + ys),
      by positivity, by positivity, fun y hy => ?_⟩
    set δ := (y - ys) / (1 + ys) with hδdef
    have hδb := hδ y hy
    have hδ1 : 0 < 1 + δ := by have := neg_abs_le δ; linarith
    have hyd : y = ys + (1 + ys) * δ := by
      rw [hδdef]; field_simp
    have hpow : (1 + y) ^ p = (1 + ys) ^ p * (1 + δ) ^ p := by
      rw [← Real.mul_rpow hs.le hδ1.le]
      congr 1
      rw [hyd]; ring
    have hdiff : psi p y - psi p ys
        = (1 + ys) ^ p * (p * δ + psi p δ) - p * ((1 + ys) * δ) := by
      simp only [psi, if_neg h1]
      rw [hpow]
      set P := (1 + δ) ^ p
      set Q := (1 + ys) ^ p
      rw [hyd]
      ring
    have hδy : |δ| = |y - ys| / (1 + ys) := by
      rw [hδdef, abs_div, abs_of_pos hs]
    have hψ := hsmall δ hδb
    have hin : |p * δ + psi p δ| ≤ p * |δ| + (|kappa p| + C) * |δ| := by
      calc |p * δ + psi p δ| ≤ |p * δ| + |psi p δ| := abs_add _ _
        _ ≤ p * |δ| + (|kappa p| + C) * |δ| := by
            rw [abs_mul, abs_of_pos hp]; linarith
    have h2 : |(1 + ys) ^ p * (p * δ + psi p δ) - p * ((1 + ys) * δ)|
        ≤ ((1 + ys) ^ p * (p + |kappa p| + C) + p * (1 + ys)) * |δ| := by
      calc |(1 + ys) ^ p * (p * δ + psi p δ) - p * ((1 + ys) * δ)|
          ≤ |(1 + ys) ^ p * (p * δ + psi p δ)| + |p * ((1 + ys) * δ)| := abs_sub _ _
        _ = (1 + ys) ^ p * |p * δ + psi p δ| + p * ((1 + ys) * |δ|) := by
            rw [abs_mul, abs_of_pos hQ, abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hs]
        _ ≤ (1 + ys) ^ p * (p * |δ| + (|kappa p| + C) * |δ|) + p * ((1 + ys) * |δ|) := by
            have := mul_le_mul_of_nonneg_left hin hQ.le
            linarith
        _ = ((1 + ys) ^ p * (p + |kappa p| + C) + p * (1 + ys)) * |δ| := by ring
    rw [hdiff]
    rw [hδy] at h2
    calc _ ≤ _ := h2
      _ = ((1 + ys) ^ p * (p + |kappa p| + C) + p * (1 + ys)) / (1 + ys) * |y - ys| := by
          ring

/-- Prop. app-local-bounds (iii), boundedness part, on `[-1/2, Y]`. -/
lemma psi_bdd {p : ℝ} (hp : 0 < p) (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ B : ℝ, ∀ y, -1 / 2 ≤ y → y ≤ Y → |psi p y| ≤ B := by
  by_cases h1 : p = 1
  · refine ⟨(1 + Y) * (Y + 1) + (Y + 1), fun y hy0 hy1 => ?_⟩
    simp only [psi, if_pos h1]
    have hpos : 0 < 1 + y := by linarith
    have hl1 : Real.log (1 + y) ≤ Y := by
      have := Real.log_le_sub_one_of_pos hpos; linarith
    have hl2 : -1 ≤ Real.log (1 + y) := by
      have h3 := Real.one_sub_inv_le_log_of_pos hpos
      have h4 : (1 + y)⁻¹ ≤ 2 := by
        rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith
      linarith
    have habs : |Real.log (1 + y)| ≤ Y + 1 := by
      rw [abs_le]; constructor <;> linarith
    have hy2 : |y| ≤ Y + 1 := by
      rw [abs_le]; constructor <;> linarith
    calc |(1 + y) * Real.log (1 + y) - y| ≤ |(1 + y) * Real.log (1 + y)| + |y| := abs_sub _ _
      _ = (1 + y) * |Real.log (1 + y)| + |y| := by rw [abs_mul, abs_of_pos hpos]
      _ ≤ (1 + Y) * (Y + 1) + (Y + 1) := by
          have := mul_le_mul (by linarith : 1 + y ≤ 1 + Y) habs (abs_nonneg _) (by linarith)
          linarith
  · refine ⟨(1 + Y) ^ p + 1 + p * (Y + 1), fun y hy0 hy1 => ?_⟩
    simp only [psi, if_neg h1]
    have hpos : 0 < 1 + y := by linarith
    have hr : (1 + y) ^ p ≤ (1 + Y) ^ p := Real.rpow_le_rpow hpos.le (by linarith) hp.le
    have hr0 : 0 ≤ (1 + y) ^ p := Real.rpow_nonneg hpos.le _
    have hy2 : |y| ≤ Y + 1 := by
      rw [abs_le]; constructor <;> linarith
    have e1 : |(1 + y) ^ p - 1| ≤ (1 + y) ^ p + 1 := by
      rw [abs_le]; constructor <;> linarith
    have e2 : |p * y| ≤ p * (Y + 1) := by
      rw [abs_mul, abs_of_pos hp]; exact mul_le_mul_of_nonneg_left hy2 hp.le
    calc |(1 + y) ^ p - 1 - p * y| ≤ |(1 + y) ^ p - 1| + |p * y| := abs_sub _ _
      _ ≤ (1 + Y) ^ p + 1 + p * (Y + 1) := by linarith

/-! ## 5. Proposition app-uniform-expansion -/

theorem uniform_expansion {p : ℝ} (hp : 0 < p) :
    ∃ η C : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ 0 ≤ C ∧
      ∀ {ι : Type} (s : Finset ι) (d y : ι → ℝ) (M e : ℝ),
        0 < M → (∀ j ∈ s, 0 ≤ d j) → ∑ j ∈ s, d j = M → ∑ j ∈ s, d j * y j = 0 →
        (∀ j ∈ s, |y j| ≤ e) → e ≤ η →
        |renyi p s d (fun j => (1 + y j) / M) - Real.log M
            + p / 2 * ((∑ j ∈ s, d j * y j ^ 2) / M)|
          ≤ C * (e + (∑ j ∈ s, d j * y j ^ 2) / M) * ((∑ j ∈ s, d j * y j ^ 2) / M) := by
  obtain ⟨η₁, C₁, hη₁, hη₁', hC₁, hloc⟩ := psi_local hp
  obtain ⟨C₂, hC₂, hF⟩ := Fp_local p
  set K := |kappa p| + C₁ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨min η₁ (1 / (2 * (K + 1))), C₂ * K ^ 2 + |cp p| * C₁,
    lt_min hη₁ (by positivity), le_trans (min_le_left _ _) hη₁', by positivity, ?_⟩
  intro ι s d y M e hM hd hdM hdy hye heη
  have he1 : e ≤ η₁ := le_trans heη (min_le_left _ _)
  have he2 : e ≤ 1 / (2 * (K + 1)) := le_trans heη (min_le_right _ _)
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hdM
    linarith
  obtain ⟨j0, hj0⟩ := hsne
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) (hye j0 hj0)
  have hy1 : ∀ j ∈ s, -1 < y j := fun j hj => by
    have h1 := hye j hj
    have h2 := neg_abs_le (y j)
    linarith
  have hexp := exact_expansion p s d y M hM hd hdM hy1 hdy
  rw [hexp]
  set Q := (∑ j ∈ s, d j * y j ^ 2) / M with hQ
  set X := (∑ j ∈ s, d j * psi p (y j)) / M with hX
  have hQ0 : 0 ≤ Q :=
    div_nonneg (Finset.sum_nonneg (fun j hj => mul_nonneg (hd j hj) (sq_nonneg _))) hM.le
  have hQM : Q * M = ∑ j ∈ s, d j * y j ^ 2 := by
    rw [hQ]; field_simp
  have hXQ : |X - kappa p * Q| ≤ C₁ * e * Q := by
    have hsum : ∑ j ∈ s, d j * (psi p (y j) - kappa p * y j ^ 2)
        = ∑ j ∈ s, d j * psi p (y j) - kappa p * ∑ j ∈ s, d j * y j ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have e' : X - kappa p * Q = (∑ j ∈ s, d j * (psi p (y j) - kappa p * y j ^ 2)) / M := by
      rw [hsum, hX, hQ]; ring
    rw [e', abs_div, abs_of_pos hM, div_le_iff₀ hM]
    calc |∑ j ∈ s, d j * (psi p (y j) - kappa p * y j ^ 2)|
        ≤ ∑ j ∈ s, |d j * (psi p (y j) - kappa p * y j ^ 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, d j * (C₁ * e * y j ^ 2) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [abs_mul, abs_of_nonneg (hd j hj)]
          refine mul_le_mul_of_nonneg_left ?_ (hd j hj)
          have h1 := hloc (y j) (le_trans (hye j hj) he1)
          have h2 : |y j| ^ 3 ≤ e * y j ^ 2 := by
            calc |y j| ^ 3 = |y j| * |y j| ^ 2 := by ring
              _ = |y j| * y j ^ 2 := by rw [sq_abs]
              _ ≤ e * y j ^ 2 := mul_le_mul_of_nonneg_right (hye j hj) (sq_nonneg _)
          calc |psi p (y j) - kappa p * y j ^ 2| ≤ C₁ * |y j| ^ 3 := h1
            _ ≤ C₁ * (e * y j ^ 2) := mul_le_mul_of_nonneg_left h2 hC₁
            _ = C₁ * e * y j ^ 2 := by ring
      _ = C₁ * e * (Q * M) := by
          rw [hQM, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = C₁ * e * Q * M := by ring
  have hQe : Q ≤ e ^ 2 := by
    rw [hQ, div_le_iff₀ hM, ← hdM, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have : y j ^ 2 ≤ e ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left (abs_nonneg _) (hye j hj) 2
    nlinarith [hd j hj]
  have hXb : |X| ≤ K * Q := by
    have h1 : |X| ≤ |X - kappa p * Q| + |kappa p * Q| := by
      calc |X| = |(X - kappa p * Q) + kappa p * Q| := by rw [sub_add_cancel]
        _ ≤ _ := abs_add _ _
    rw [abs_mul, abs_of_nonneg hQ0] at h1
    have h2 : C₁ * e * Q ≤ C₁ * Q := by
      have he' : e ≤ 1 := by linarith
      have := mul_le_mul_of_nonneg_left he' (mul_nonneg hC₁ hQ0)
      nlinarith [this]
    rw [hK]
    nlinarith [hXQ, h1, h2]
  have hX12 : |X| ≤ 1 / 2 := by
    have h1 : K * Q ≤ K * e ^ 2 := mul_le_mul_of_nonneg_left hQe hK0
    have h2 : e * (2 * (K + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at he2; linarith
    have h3 : K * e ≤ 1 / 2 := by nlinarith [h2, he0]
    have h4 : K * e * e ≤ 1 / 2 * e := mul_le_mul_of_nonneg_right h3 he0
    nlinarith [h1, h4, hXb]
  have hF' := hF X hX12
  have hc := cp_mul_kappa p
  have key : Real.log M + Fp p X - Real.log M + p / 2 * Q
      = (Fp p X - cp p * X) + cp p * (X - kappa p * Q) := by
    have : p / 2 = -(cp p * kappa p) := by rw [hc]; ring
    rw [this]; ring
  rw [key]
  have hX2 : X ^ 2 ≤ (K * Q) ^ 2 := by
    rw [← sq_abs X]; exact pow_le_pow_left (abs_nonneg _) hXb 2
  calc |(Fp p X - cp p * X) + cp p * (X - kappa p * Q)|
      ≤ |Fp p X - cp p * X| + |cp p * (X - kappa p * Q)| := abs_add _ _
    _ ≤ C₂ * X ^ 2 + |cp p| * (C₁ * e * Q) := by
        rw [abs_mul]
        exact add_le_add hF' (mul_le_mul_of_nonneg_left hXQ (abs_nonneg _))
    _ ≤ C₂ * (K * Q) ^ 2 + |cp p| * (C₁ * e * Q) := by
        have := mul_le_mul_of_nonneg_left hX2 hC₂
        linarith
    _ ≤ (C₂ * K ^ 2 + |cp p| * C₁) * (e + Q) * Q := by
        have h1 : 0 ≤ C₂ * K ^ 2 * (e * Q) := by positivity
        have h2 : 0 ≤ |cp p| * C₁ * (Q * Q) := by positivity
        nlinarith [h1, h2]

end AppendixB
end
