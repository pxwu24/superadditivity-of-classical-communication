import Entropy.Analysis
import Entropy.BellBounds
open Real Finset
noncomputable section
namespace AppendixB
set_option maxHeartbeats 2000000
private lemma half_bound (P E K : ℝ) (h : 2 * (P + E) + 1 ≤ K)
    (h2 : K ≤ K ^ 2) : P + E ≤ 1 / 2 * K ^ 2 := by
  linarith only [h, h2]

/-- Prop. app-bell-entropy-asymptotics, eq. (44):
    `S_p(λ^Bell_{k,t}) = 2 log k - A_p(t)/k² + O(k^{-4})`, where `λ^Bell_{k,t}` consists of
    `α_{k,t}` (multiplicity 1) and `β_{k,t}` (multiplicity `k² - 1`). -/
theorem bell_output_r1 {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      |renyi p (Finset.univ : Finset (Fin 2)) ![1, (k : ℝ) ^ 2 - 1] ![alphaB k t, betaB k t]
        - (2 * Real.log k - Ap p t / k ^ 2)| ≤ C / k ^ 4 := by
  obtain ⟨η₁, C₁, hη₁, hη₁', hC₁, hloc⟩ := psi_local hp
  obtain ⟨C₂, hC₂, hF⟩ := Fp_local p
  have hγ0 : 0 < (1 - t) / t := div_pos (by linarith) ht0
  obtain ⟨L, ηL, hηL, hL, hlip⟩ := psi_lip hp (show -1 < (1 - t) / t by linarith)
  set γ := (1 - t) / t with hγ
  set P0 := |psi p γ| with hP0
  set E := 8 * γ * L + (|kappa p| + C₁) * (2 * γ) ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨C₂ * (P0 + E) ^ 2 + |cp p| * E,
    max (max 2 (1 / t)) (max (8 * γ / ηL + 1) (max (2 * γ / η₁ + 1) (2 * (P0 + E) + 1))),
    fun k hk => ?_⟩
  have hk2 : (2 : ℝ) ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hkt : 1 / t ≤ (k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkL : 8 * γ / ηL + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkη : 2 * γ / η₁ + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hk
  have hkP : 2 * (P0 + E) + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk2]
  have hk2t : 1 ≤ (k : ℝ) ^ 2 * t := by
    rw [div_le_iff₀ ht0] at hkt
    have hh := mul_le_mul_of_nonneg_right hkk ht0.le
    linarith only [hkt, hh]
  obtain ⟨hρ0, hρ1, hρ2⟩ := rkt_bounds ht0 ht1 hk2 hk2t
  rw [← hγ] at hρ1 hρ2
  set ρ := rkt k t with hρ
  have hρη : ρ ≤ η₁ := by
    have h1 : 2 * γ / (k : ℝ) ^ 2 ≤ 2 * γ / (k : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hkpos hkk
    have h2 : 2 * γ / (k : ℝ) ≤ η₁ := by
      rw [div_le_iff₀ hkpos]
      have h3 : 2 * γ / η₁ ≤ k := by linarith
      rw [div_le_iff₀ hη₁] at h3
      linarith
    linarith
  set y0 := ρ * ((k : ℝ) ^ 2 - 1) with hy0
  have hyγ : |y0 - γ| ≤ 8 * γ / (k : ℝ) ^ 2 := by
    have e : y0 - γ = ((k : ℝ) ^ 2 * ρ - γ) - ρ := by rw [hy0]; ring
    rw [e]
    calc |((k : ℝ) ^ 2 * ρ - γ) - ρ| ≤ |(k : ℝ) ^ 2 * ρ - γ| + |ρ| := abs_sub _ _
      _ ≤ 6 * γ / (k : ℝ) ^ 2 + 2 * γ / (k : ℝ) ^ 2 := by
          rw [abs_of_nonneg hρ0]; linarith [hρ2, hρ1]
      _ = 8 * γ / (k : ℝ) ^ 2 := by ring
  have hyL : |y0 - γ| ≤ ηL := by
    refine le_trans hyγ ?_
    have h1 : 8 * γ / (k : ℝ) ^ 2 ≤ 8 * γ / (k : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hkpos hkk
    have h2 : 8 * γ / (k : ℝ) ≤ ηL := by
      rw [div_le_iff₀ hkpos]
      have h3 : 8 * γ / ηL ≤ k := by linarith
      rw [div_le_iff₀ hηL] at h3
      linarith
    linarith
  have hψ1 := hlip y0 hyL
  have hψ2 := psi_quad hη₁' hC₁ hloc (-ρ) (by rw [abs_neg, abs_of_nonneg hρ0]; exact hρη)
  -- Step 1: the spectrum is `(1 + y_j)/k²` with `y = (y0, -ρ)`
  have hspec : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      (![alphaB k t, betaB k t] : Fin 2 → ℝ) j
        = (fun j => (1 + (![y0, -ρ] : Fin 2 → ℝ) j) / (k : ℝ) ^ 2) j := by
    intro j _
    fin_cases j <;> simp [alphaB, betaB, ← hρ, hy0] <;> field_simp <;> ring
  rw [renyi_congr p _ _ _ _ hspec]
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      0 ≤ (![1, (k : ℝ) ^ 2 - 1] : Fin 2 → ℝ) j := by
    intro j _
    fin_cases j
    · norm_num
    · change 0 ≤ (k : ℝ) ^ 2 - 1
      nlinarith only [hk2]
  have hdM : ∑ j : Fin 2, (![1, (k : ℝ) ^ 2 - 1] : Fin 2 → ℝ) j = (k : ℝ) ^ 2 := by
    rw [Fin.sum_univ_two]; simp
  have hy : ∀ j ∈ (Finset.univ : Finset (Fin 2)), -1 < (![y0, -ρ] : Fin 2 → ℝ) j := by
    intro j _
    fin_cases j
    · change -1 < y0
      have hnonneg : 0 ≤ y0 := mul_nonneg hρ0 (by nlinarith only [hk2])
      linarith only [hnonneg]
    · change -1 < -ρ
      linarith only [hρη, hη₁']
  have hdy : ∑ j : Fin 2, (![1, (k : ℝ) ^ 2 - 1] : Fin 2 → ℝ) j * (![y0, -ρ] : Fin 2 → ℝ) j
      = 0 := by
    rw [Fin.sum_univ_two]; simp [hy0] <;> ring
  -- Step 2: exact expansion
  rw [exact_expansion p Finset.univ _ _ ((k : ℝ) ^ 2) (by positivity) hd hdM hy hdy]
  set X := (∑ j : Fin 2, (![1, (k : ℝ) ^ 2 - 1] : Fin 2 → ℝ) j
      * psi p ((![y0, -ρ] : Fin 2 → ℝ) j)) / (k : ℝ) ^ 2 with hX
  have hXval : X = (psi p y0 + ((k : ℝ) ^ 2 - 1) * psi p (-ρ)) / (k : ℝ) ^ 2 := by
    rw [hX, Fin.sum_univ_two]; simp
  -- Step 3: estimates
  have hXY : |X - psi p γ / (k : ℝ) ^ 2| ≤ E / (k : ℝ) ^ 4 := by
    rw [hXval]
    have e : (psi p y0 + ((k : ℝ) ^ 2 - 1) * psi p (-ρ)) / (k : ℝ) ^ 2 - psi p γ / (k : ℝ) ^ 2
        = (psi p y0 - psi p γ) / (k : ℝ) ^ 2
          + ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 * psi p (-ρ) := by ring
    rw [e]
    have h1 : |(psi p y0 - psi p γ) / (k : ℝ) ^ 2| ≤ 8 * γ * L / (k : ℝ) ^ 4 := by
      rw [abs_div, abs_of_pos (pow_pos hkpos 2), div_le_iff₀ (pow_pos hkpos 2)]
      calc |psi p y0 - psi p γ| ≤ L * |y0 - γ| := hψ1
        _ ≤ L * (8 * γ / (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hyγ hL
        _ = 8 * γ * L / (k : ℝ) ^ 4 * (k : ℝ) ^ 2 := by field_simp <;> ring
    have h2 : |((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 * psi p (-ρ)|
        ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by
      rw [abs_mul]
      have h3 : |((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2| ≤ 1 := by
        rw [abs_le]; constructor
        · have : 0 ≤ ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 :=
            div_nonneg (by nlinarith only [hk2]) (by positivity)
          linarith
        · rw [div_le_one (by positivity)]; linarith
      have h4 : |psi p (-ρ)| ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by
        refine le_trans hψ2 ?_
        rw [neg_sq]
        have h5 : ρ ^ 2 ≤ (2 * γ / (k : ℝ) ^ 2) ^ 2 := pow_le_pow_left hρ0 hρ1 2
        calc (|kappa p| + C₁) * ρ ^ 2 ≤ (|kappa p| + C₁) * (2 * γ / (k : ℝ) ^ 2) ^ 2 :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by rw [div_pow]; ring
      calc |((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2| * |psi p (-ρ)|
          ≤ 1 * ((|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4) :=
            mul_le_mul h3 h4 (abs_nonneg _) zero_le_one
        _ = (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 := one_mul _
    calc _ ≤ |(psi p y0 - psi p γ) / (k : ℝ) ^ 2|
          + |((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 * psi p (-ρ)| := abs_add _ _
      _ ≤ 8 * γ * L / (k : ℝ) ^ 4 + (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 :=
          add_le_add h1 h2
      _ = E / (k : ℝ) ^ 4 := by rw [hE]; ring
  have hXb : |X| ≤ (P0 + E) / (k : ℝ) ^ 2 := by
    have h1 : |X| ≤ |psi p γ / (k : ℝ) ^ 2| + E / (k : ℝ) ^ 4 := by
      have := abs_sub_abs_le_abs_sub X (psi p γ / (k : ℝ) ^ 2)
      linarith
    have h2 : |psi p γ / (k : ℝ) ^ 2| = P0 / (k : ℝ) ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
    have h3 : E / (k : ℝ) ^ 4 ≤ E / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hE0 (by positivity) (by nlinarith only [sq_nonneg ((k : ℝ)^2 - 1), hk2])
    have e : P0 / (k : ℝ) ^ 2 + E / (k : ℝ) ^ 2 = (P0 + E) / (k : ℝ) ^ 2 := by ring
    linarith
  have hX12 : |X| ≤ 1 / 2 := by
    refine le_trans hXb ?_
    rw [div_le_iff₀ (by positivity)]
    exact half_bound P0 E (k : ℝ) hkP hkk
  have hlog : Real.log ((k : ℝ) ^ 2) = 2 * Real.log k := by
    rw [Real.log_pow]; norm_num
  have hA : cp p * psi p γ = -Ap p t := by
    have h1 := B_identity p 1 γ one_ne_zero
    simp only [one_pow, div_one, one_mul] at h1
    rw [h1, hγ, B_one_eq_A p t ht0]
  have e : Real.log ((k : ℝ) ^ 2) + Fp p X - (2 * Real.log k - Ap p t / (k : ℝ) ^ 2)
      = Fp p X - cp p * (psi p γ / (k : ℝ) ^ 2) := by
    rw [hlog, mul_div_assoc', hA]; ring
  rw [e]
  calc |Fp p X - cp p * (psi p γ / (k : ℝ) ^ 2)|
      ≤ C₂ * X ^ 2 + |cp p| * (E / (k : ℝ) ^ 4) := final_step hF hXY hX12
    _ ≤ C₂ * ((P0 + E) / (k : ℝ) ^ 2) ^ 2 + |cp p| * (E / (k : ℝ) ^ 4) := by
        have h1 : X ^ 2 ≤ ((P0 + E) / (k : ℝ) ^ 2) ^ 2 := by
          rw [← sq_abs X]; exact pow_le_pow_left (abs_nonneg _) hXb 2
        have := mul_le_mul_of_nonneg_left h1 hC₂
        linarith
    _ = (C₂ * (P0 + E) ^ 2 + |cp p| * E) / (k : ℝ) ^ 4 := by
        rw [div_pow]; field_simp <;> ring

end AppendixB
end
