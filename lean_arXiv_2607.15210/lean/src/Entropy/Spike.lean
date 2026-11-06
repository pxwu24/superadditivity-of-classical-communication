import Entropy.SpikeArithmetic

set_option maxHeartbeats 1000000
open Real Finset
noncomputable section
namespace AppendixB

/-- Prop. app-localization (ii): the two-spike point `u* = (u₊, u₋, t, …, t)`. -/
lemma two_spike {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ C k₀ : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      ∃ q ∈ Lam k t, 4 * ((1 - t) / t) / k - C / k ^ 2 ≤ ∑ i, ((k : ℝ) * q i - 1) ^ 2 := by
  refine ⟨8 / t ^ 3, max 2 (max (1 / (2 * t)) (1 / (2 * (1 - t)))), by positivity,
    fun k hk => ?_⟩
  have hk2 : (2 : ℝ) ≤ k := le_trans (le_max_left _ _) hk
  have hka : 1 / (2 * t) ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkb : 1 / (2 * (1 - t)) ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hk2n : 2 ≤ k := by exact_mod_cast hk2
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  set K : ℝ := ((n + 2 : ℕ) : ℝ) with hK
  have hK0 : 0 < K := by linarith
  have hKa : 1 ≤ 2 * t * K := by
    rw [div_le_iff₀ (by positivity)] at hka; linarith
  have h1t : 0 < 1 - t := by linarith
  have hKb : 1 ≤ 2 * (1 - t) * K := by
    rw [div_le_iff₀ (by positivity)] at hkb; linarith
  obtain ⟨a, ha_def⟩ : ∃ a, a = Real.sqrt t := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, b = Real.sqrt (1 - t) := ⟨_, rfl⟩
  obtain ⟨σ, hσ_def⟩ : ∃ σ, σ = Real.sqrt (1 / (2 * K)) := ⟨_, rfl⟩
  obtain ⟨cs, hcs_def⟩ : ∃ cs, cs = Real.sqrt (1 - 1 / (2 * K)) := ⟨_, rfl⟩
  have hσK : 1 / (2 * K) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have ha : a ^ 2 = t := by rw [ha_def]; exact Real.sq_sqrt ht0.le
  have hb : b ^ 2 = 1 - t := by rw [hb_def]; exact Real.sq_sqrt h1t.le
  have hσ : σ ^ 2 = 1 / (2 * K) := by rw [hσ_def]; exact Real.sq_sqrt (by positivity)
  have hcs : cs ^ 2 = 1 - 1 / (2 * K) := by
    rw [hcs_def]; exact Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ a := by rw [ha_def]; exact Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := by rw [hb_def]; exact Real.sqrt_nonneg _
  have hσ0 : 0 ≤ σ := by rw [hσ_def]; exact Real.sqrt_nonneg _
  have hcs0 : 0 ≤ cs := by rw [hcs_def]; exact Real.sqrt_nonneg _
  have hσt : 1 / (2 * K) ≤ t := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hσ1t : 1 / (2 * K) ≤ 1 - t := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hsum1 : a ^ 2 + b ^ 2 = 1 := by rw [ha, hb]; ring
  have hsum2 : cs ^ 2 + σ ^ 2 = 1 := by rw [hcs, hσ]; ring
  -- `b σ ≤ a cs` and `a σ ≤ b cs`
  have hle1 : b * σ ≤ a * cs := by
    have h1 : (b * σ) ^ 2 ≤ (a * cs) ^ 2 := by
      rw [mul_pow, mul_pow, ha, hb, hσ, hcs]; nlinarith only [hσt]
    calc b * σ = Real.sqrt ((b * σ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((a * cs) ^ 2) := Real.sqrt_le_sqrt h1
      _ = a * cs := Real.sqrt_sq (by positivity)
  have hle2 : a * σ ≤ b * cs := by
    have h1 : (a * σ) ^ 2 ≤ (b * cs) ^ 2 := by
      rw [mul_pow, mul_pow, ha, hb, hσ, hcs]; nlinarith only [hσ1t]
    calc a * σ = Real.sqrt ((a * σ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((b * cs) ^ 2) := Real.sqrt_le_sqrt h1
      _ = b * cs := Real.sqrt_sq (by positivity)
  set up := (a * cs + b * σ) ^ 2 with hup
  set um := (a * cs - b * σ) ^ 2 with hum
  have hup1 : 1 - up = (b * cs - a * σ) ^ 2 := by
    rw [hup]; linear_combination (-(cs ^ 2 + σ ^ 2)) * hsum1 - hsum2
  have hum1 : 1 - um = (b * cs + a * σ) ^ 2 := by
    rw [hum]; linear_combination (-(cs ^ 2 + σ ^ 2)) * hsum1 - hsum2
  have hctp : ct t up = σ ^ 2 := by
    unfold ct
    rw [hup1, Real.sqrt_mul ht0.le, Real.sqrt_mul h1t.le, ← ha_def, ← hb_def,
      Real.sqrt_sq (by linarith : 0 ≤ b * cs - a * σ), hup,
      Real.sqrt_sq (by positivity : 0 ≤ a * cs + b * σ)]
    linear_combination σ ^ 2 * (a ^ 2 + b ^ 2 + 1) * hsum1
  have hctm : ct t um = σ ^ 2 := by
    unfold ct
    rw [hum1, Real.sqrt_mul ht0.le, Real.sqrt_mul h1t.le, ← ha_def, ← hb_def,
      Real.sqrt_sq (by positivity : 0 ≤ b * cs + a * σ), hum,
      Real.sqrt_sq (by linarith : 0 ≤ a * cs - b * σ)]
    linear_combination σ ^ 2 * (a ^ 2 + b ^ 2 + 1) * hsum1
  have hctt : ct t t = 0 := by simp [ct, mul_comm]
  have hup01 : 0 ≤ up ∧ up ≤ 1 := ⟨by positivity, by linarith only [hup1, sq_nonneg (b * cs - a * σ)]⟩
  have hum01 : 0 ≤ um ∧ um ≤ 1 := ⟨by positivity, by linarith only [hum1, sq_nonneg (b * cs + a * σ)]⟩
  -- the point `u*`
  set ustar : Fin (n + 2) → ℝ :=
    (Fin.cons up (Fin.cons um (fun _ : Fin n => t) : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ)
    with hustar
  have hsum_ct : ∑ i, ct t (ustar i) = 1 / K := by
    rw [hustar, sum_cons2 n up um t (ct t), hctp, hctm, hctt, hσ]
    ring
  have hmem : ustar ∈ Dset (n + 2) t := by
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hustar] using hup01
      · refine Fin.cases ?_ (fun l => ?_) j
        · simpa [hustar] using hum01
        · simp only [hustar, Fin.cons_succ]
          exact ⟨ht0.le, ht1.le⟩
    · rw [hsum_ct]
  -- sums over `u*`
  have hw1 : up - t = (b ^ 2 - a ^ 2) * σ ^ 2 + 2 * a * b * cs * σ := by
    rw [hup]; linear_combination a ^ 2 * hsum2 + ha
  have hw2 : um - t = (b ^ 2 - a ^ 2) * σ ^ 2 - 2 * a * b * cs * σ := by
    rw [hum]; linear_combination a ^ 2 * hsum2 + ha
  have hSum : ∑ i, ustar i = up + um + n * t := by
    rw [hustar, sum_cons2 n up um t (fun x => x)]
  have hW : ∑ i, (ustar i - t) = (1 - 2 * t) / K := by
    rw [hustar, sum_cons2 n up um t (fun x => x - t), hw1, hw2, hσ, ha, hb]
    field_simp <;> ring
  have hW2 : ∑ i, (ustar i - t) ^ 2 ≥ 4 * t * (1 - t) * (1 - 1 / (2 * K)) / K := by
    rw [hustar, sum_cons2 n up um t (fun x => (x - t) ^ 2)]
    simp only [sub_self]
    rw [hw1, hw2]
    have e : ((b ^ 2 - a ^ 2) * σ ^ 2 + 2 * a * b * cs * σ) ^ 2
        + ((b ^ 2 - a ^ 2) * σ ^ 2 - 2 * a * b * cs * σ) ^ 2 + (n : ℝ) * 0 ^ 2
        = 2 * ((b ^ 2 - a ^ 2) * σ ^ 2) ^ 2 + 8 * (a ^ 2 * b ^ 2) * (cs ^ 2 * σ ^ 2) := by ring
    rw [e, ha, hb, hcs, hσ]
    have h1 : 0 ≤ 2 * (((1 - t) - t) * (1 / (2 * K))) ^ 2 := by positivity
    have e2 : 8 * (t * (1 - t)) * ((1 - 1 / (2 * K)) * (1 / (2 * K)))
        = 4 * t * (1 - t) * (1 - 1 / (2 * K)) / K := by
      field_simp <;> ring
    linarith only [h1, e2]
  have hSeq : ∑ i, ustar i = K * t + (1 - 2 * t) / K := by
    have h := hW
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    linarith only [h]
  have hS0 : 0 < ∑ i, ustar i := by
    rw [hSeq]
    have e : K * t + (1 - 2 * t) / K = ((K ^ 2 - 2) * t + 1) / K := by
      field_simp
      ring
    rw [e]
    apply div_pos _ hK0
    have hKsq : 0 ≤ K ^ 2 - 2 := by nlinarith only [hk2]
    nlinarith only [mul_nonneg hKsq ht0.le]
  refine ⟨fun i => ustar i / ∑ j, ustar j, ⟨ustar, hmem, rfl⟩, ?_⟩
  rw [eps_sq_sum t ustar hS0.ne']
  apply spike_final ht0 ht1 hk2
  · nlinarith only [mul_le_mul_of_nonneg_left hKb (by positivity : (0 : ℝ) ≤ 2 * t),
      mul_le_mul_of_nonneg_left hKa (by positivity : (0 : ℝ) ≤ 2 * (1 - t))]
  · -- the numerator: `K² ∑ w² - K (∑ w)² ≥ 4 t (1-t) K - 1`
    change 4 * t * (1 - t) * K - 1 ≤ K ^ 2 * (∑ i, (ustar i - t) ^ 2) - K * (∑ i, (ustar i - t)) ^ 2
    rw [hW]
    have h1 : K ^ 2 * (4 * t * (1 - t) * (1 - 1 / (2 * K)) / K)
        ≤ K ^ 2 * ∑ i, (ustar i - t) ^ 2 := mul_le_mul_of_nonneg_left hW2 (by positivity)
    have e1 : K ^ 2 * (4 * t * (1 - t) * (1 - 1 / (2 * K)) / K)
        = 4 * t * (1 - t) * K - 2 * t * (1 - t) := by field_simp <;> ring
    have e2 : K * ((1 - 2 * t) / K) ^ 2 = (1 - 2 * t) ^ 2 / K := by field_simp <;> ring
    have h2 : (1 - 2 * t) ^ 2 / K ≤ 1 / 2 := by
      rw [div_le_iff₀ hK0]; nlinarith only [hk2, mul_nonneg ht0.le h1t.le]
    have h3 : 2 * t * (1 - t) ≤ 1 / 2 := by nlinarith only [sq_nonneg (2 * t - 1)]
    linarith only [h1, e1, e2, h2, h3]
  · exact hS0
  · rw [hSeq]
    have : (1 - 2 * t) / K ≤ 1 / K := div_le_div_of_nonneg_right (by linarith) hK0.le
    linarith only [this]
end AppendixB
end
