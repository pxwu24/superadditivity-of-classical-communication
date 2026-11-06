import Entropy.Analysis
import Entropy.Combinatorics
import Entropy.Localization
import Entropy.Spike

open Real Finset
noncomputable section
namespace AppendixB

set_option maxHeartbeats 1000000

/-- Prop. app-antisymmetric-single-entropy-asymptotics, eq. (65), at the level of spectra:
    the minimum of `S_p(𝓔_{k,r}(ρ))` over `ρ ∈ 𝒦_{k,t}` is
    `log C(k,r) - 2p(1-t)/(t r k²) + O(k^{-5/2})`. -/
theorem single_output {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      (∀ q ∈ Lam k t,
        Real.log (Nat.choose k r) - 2 * p * (1 - t) / (t * r * k ^ 2) - C / (k ^ 2 * Real.sqrt k)
          ≤ renyi p (subsets k r) (fun _ => 1) (shuffle k r q)) ∧
      (∃ q ∈ Lam k t,
        renyi p (subsets k r) (fun _ => 1) (shuffle k r q)
          ≤ Real.log (Nat.choose k r) - 2 * p * (1 - t) / (t * r * k ^ 2)
            + C / (k ^ 2 * Real.sqrt k)) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨η, Cu, hη, hη', hCu, hunif⟩ := uniform_expansion hp
  obtain ⟨CL, kL, hCL, hloc⟩ := localization ht0 ht1
  obtain ⟨CT, kT, hCT, htwo⟩ := two_spike ht0 ht1
  set γ := (1 - t) / t with hγ
  have hγ0 : 0 < γ := div_pos (by linarith) ht0
  set R : ℝ := ((r' + 1 : ℕ) : ℝ) with hR
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast (by omega : 1 ≤ r' + 1)
  have hR0 : (0 : ℝ) < R := by linarith
  set C : ℝ := p * CL + Cu * (2 * CL + 4 * γ) * (4 * γ + CL) + p * (CT + 8 * R * γ) with hC
  refine ⟨C, max (max kL kT) (max (4 * R + 4) ((CL / η) ^ 2 + 1)), fun k hk => ?_⟩
  have hkL : kL ≤ (k : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hkT : kT ≤ (k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkR : 4 * R + 4 ≤ (k : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkη : (CL / η) ^ 2 + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hRne : R ≠ 0 := ne_of_gt hR0
  have hkr : r' + 2 ≤ k := by
    have : ((r' + 2 : ℕ) : ℝ) ≤ k := by push_cast; rw [hR] at hkR; push_cast at hkR; linarith
    exact_mod_cast this
  set s := Real.sqrt k with hs_def
  have hs2 : s ^ 2 = k := Real.sq_sqrt hkpos.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hkpos
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hs1 : 1 ≤ s := by nlinarith
  have hsk : s ≤ (k : ℝ) := by nlinarith
  set e := CL / s with he
  have heη : e ≤ η := by
    rw [he, div_le_iff₀ hs0]
    have h1 : CL / η < s := by
      have h2 : (CL / η) ^ 2 < s ^ 2 := by rw [hs2]; linarith
      exact lt_of_pow_lt_pow_left₀ 2 hs0.le h2
    rw [div_lt_iff₀ hη] at h1
    linarith
  have he0 : 0 ≤ e := by positivity
  set D : ℝ := (Nat.choose k (r' + 1) : ℝ) with hD
  have hD0 : 0 < D := by rw [hD]; exact_mod_cast Nat.choose_pos (by omega)
  -- the uniform expansion applied to a point `q` of `Λ_{k,t}`
  have hgen : ∀ q, (∑ i, q i = 1) → (∀ i, |(k : ℝ) * q i - 1| ≤ e) →
      |renyi p (subsets k (r' + 1)) (fun _ => 1) (shuffle k (r' + 1) q) - Real.log D
          + p / 2 * (((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * ∑ i, ((k : ℝ) * q i - 1) ^ 2)|
        ≤ Cu * (e + ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * ∑ i, ((k : ℝ) * q i - 1) ^ 2)
            * (((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * ∑ i, ((k : ℝ) * q i - 1) ^ 2) := by
    intro q hq1 hqe
    set ε : Fin k → ℝ := fun i => (k : ℝ) * q i - 1 with hε
    have hεsum : ∑ i, ε i = 0 := by
      rw [hε]
      simp only
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hq1, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    set δ : Finset (Fin k) → ℝ := fun I => (∑ i ∈ I, ε i) / R with hδ
    have hrep : ∀ I ∈ subsets k (r' + 1), shuffle k (r' + 1) q I = (1 + δ I) / D := by
      intro I hI
      have hIc : I.card = r' + 1 := (Finset.mem_powersetCard.mp hI).2
      rw [shuffle_repr (by omega) (by omega) q I hIc]
    rw [renyi_congr p _ _ _ _ hrep]
    have hd : ∀ I ∈ subsets k (r' + 1), (0 : ℝ) ≤ (fun _ => (1 : ℝ)) I := fun _ _ => zero_le_one
    have hdM : ∑ I ∈ subsets k (r' + 1), (fun _ => (1 : ℝ)) I = D := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_subsets, hD]
    have hdy : ∑ I ∈ subsets k (r' + 1), (fun _ => (1 : ℝ)) I * δ I = 0 := by
      simp only [one_mul, hδ]
      rw [← Finset.sum_div, sum_over_subsets r' ε, hεsum, mul_zero, zero_div]
    have hye : ∀ I ∈ subsets k (r' + 1), |δ I| ≤ e := by
      intro I hI
      have hIc : I.card = r' + 1 := (Finset.mem_powersetCard.mp hI).2
      rw [hδ]
      simp only
      rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
      calc |∑ i ∈ I, ε i| ≤ ∑ i ∈ I, |ε i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ I, e := Finset.sum_le_sum (fun i _ => hqe i)
        _ = e * R := by
            rw [Finset.sum_const, hIc, nsmul_eq_mul, hR]; ring
    have hU := hunif (subsets k (r' + 1)) (fun _ => 1) δ D e hD0 hd hdM hdy hye heη
    have hQ : (∑ I ∈ subsets k (r' + 1), (fun _ => (1 : ℝ)) I * δ I ^ 2) / D
        = ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * ∑ i, ε i ^ 2 := by
      simp only [one_mul, hδ, div_pow]
      rw [← Finset.sum_div, quadratic_form r' ε hεsum, hD]
      rw [show ((k - 2).choose r' : ℝ) * (∑ i, ε i ^ 2) / R ^ 2 / (Nat.choose k (r' + 1) : ℝ)
          = ((k - 2).choose r' : ℝ) / (R ^ 2 * (Nat.choose k (r' + 1) : ℝ)) * ∑ i, ε i ^ 2 by
            field_simp]
      rw [hR, quad_coeff hkr]
    rw [hQ] at hU
    exact hU
  -- bounds on the coefficient `(k - R)/(R k (k-1))`
  have hcoef_hi : ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) ≤ 1 / (R * k) := by
    calc ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1))
        ≤ ((k : ℝ) - 1) / (R * k * ((k : ℝ) - 1)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / (R * k) := by field_simp <;> ring
  have hcoef_lo : 1 / (R * k) - 2 / k ^ 2 ≤ ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) := by
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have e1 : ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) ≥ ((k : ℝ) - R) / (R * k * k) := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      have : R * k * ((k : ℝ) - 1) ≤ R * k * k :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      exact this
    have e2 : ((k : ℝ) - R) / (R * k * k) = 1 / (R * k) - 1 / k ^ 2 := by
      field_simp <;> ring
    have e3 : (0 : ℝ) ≤ 1 / k ^ 2 := by positivity
    have e4 : (2 : ℝ) / k ^ 2 = 2 * (1 / k ^ 2) := by ring
    rw [e4]
    linarith only [e1, e2, e3]
  have hcoef0 : 0 ≤ ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) := by
    exact div_nonneg (by linarith) (by positivity)
  have hkone : (1 : ℝ) ≤ k := by linarith only [hk1]
  have hk2one : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkone
  have hkk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hkone]
  have hsk2 : s ≤ (k : ℝ) ^ 2 := hsk.trans hkk2
  have hden : (0 : ℝ) < (k : ℝ) ^ 2 * s := by positivity
  have hden3 : (k : ℝ) ^ 2 * s ≤ (k : ℝ) ^ 3 := by
    simpa only [pow_succ] using mul_le_mul_of_nonneg_left hsk (sq_nonneg (k : ℝ))
  set L : ℝ := 4 * γ / (R * k ^ 2) with hL
  set M : ℝ := 4 * γ + CL with hM
  set E : ℝ := Cu * (2 * CL + 4 * γ) * M with hE
  set Z : ℝ := CT + 8 * R * γ with hZ
  have hM0 : 0 ≤ M := by positivity
  have hZ0 : 0 ≤ Z := by positivity
  have hlead : 2 * p * (1 - t) / (t * R * k ^ 2) = p / 2 * L := by
    rw [hL, hγ]; field_simp <;> ring
  rw [hlead]
  have haux : ∀ (S2 : ℝ), 0 ≤ S2 → S2 ≤ 4 * γ / k + CL / (k * s) →
      let Q := ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * S2
      0 ≤ Q ∧ Q ≤ L + CL / (k ^ 2 * s) ∧
        Cu * (e + Q) * Q ≤ E / (k ^ 2 * s) := by
    intro S2 hS0 hS
    dsimp only
    set Q := ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * S2
    have hQ0 : 0 ≤ Q := mul_nonneg hcoef0 hS0
    have hQ1 : Q ≤ (4 * γ / k + CL / (k * s)) / (R * k) := by
      calc Q ≤ 1 / (R * k) * S2 := mul_le_mul_of_nonneg_right hcoef_hi hS0
        _ ≤ 1 / (R * k) * (4 * γ / k + CL / (k * s)) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
        _ = _ := by ring
    have hQ2 : Q ≤ L + CL / (k ^ 2 * s) := by
      have heq : (4 * γ / k + CL / (k * s)) / (R * k)
          = L + CL / (R * (k ^ 2 * s)) := by rw [hL]; field_simp <;> ring
      have hdiv : CL / (R * (k ^ 2 * s)) ≤ CL / (k ^ 2 * s) :=
        div_le_div_of_nonneg_left hCL hden (le_mul_of_one_le_left hden.le hR1)
      rw [heq] at hQ1
      exact hQ1.trans (add_le_add_left hdiv L)
    have hQ3 : Q ≤ M / k ^ 2 := by
      have hA : L ≤ 4 * γ / k ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (le_mul_of_one_le_left (sq_nonneg (k : ℝ)) hR1)
      have hB : CL / (k ^ 2 * s) ≤ CL / k ^ 2 :=
        div_le_div_of_nonneg_left hCL (by positivity)
          (le_mul_of_one_le_right (sq_nonneg (k : ℝ)) hs1)
      calc Q ≤ L + CL / (k ^ 2 * s) := hQ2
        _ ≤ 4 * γ / k ^ 2 + CL / k ^ 2 := add_le_add hA hB
        _ = M / k ^ 2 := by rw [hM]; ring
    have hEQ : e + Q ≤ (2 * CL + 4 * γ) / s := by
      have hQ4 := hQ3.trans (div_le_div_of_nonneg_left hM0 hs0 hsk2)
      calc e + Q ≤ CL / s + M / s := add_le_add_left hQ4 e
        _ = _ := by rw [hM]; ring
    refine ⟨hQ0, hQ2, ?_⟩
    calc Cu * (e + Q) * Q
        ≤ Cu * ((2 * CL + 4 * γ) / s) * (M / k ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hEQ hCu) hQ3 hQ0 (by positivity)
      _ = E / (k ^ 2 * s) := by rw [hE]; field_simp [hkne, hsne] <;> ring <;> simp
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨hq1, _, hqe, hq2⟩ := hloc k hkL q hq
    set Q := ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * ∑ i, ((k : ℝ) * q i - 1) ^ 2
    obtain ⟨hQ0, hQhi, herr⟩ := haux (∑ i, ((k : ℝ) * q i - 1) ^ 2)
      (Finset.sum_nonneg fun i _ => sq_nonneg _) hq2
    change Q ≤ L + CL / (k ^ 2 * s) at hQhi
    change Cu * (e + Q) * Q ≤ E / (k ^ 2 * s) at herr
    have hU := (abs_le.mp (hgen q hq1 hqe)).1
    change -(Cu * (e + Q) * Q) ≤
      renyi p (subsets k (r' + 1)) (fun _ => 1) (shuffle k (r' + 1) q) - Real.log D + p / 2 * Q at hU
    have hlin : p / 2 * Q ≤ p / 2 * L + p * CL / (k ^ 2 * s) := by
      have h1 := mul_le_mul_of_nonneg_left hQhi (by positivity : (0 : ℝ) ≤ p / 2)
      have h2 : p / 2 * (CL / (k ^ 2 * s)) ≤ p * CL / (k ^ 2 * s) := by
        calc p / 2 * (CL / (k ^ 2 * s))
            ≤ p * (CL / (k ^ 2 * s)) :=
              mul_le_mul_of_nonneg_right (by linarith only [hp]) (by positivity)
          _ = _ := by ring
      linarith only [h1, h2]
    have hCbig : p * CL / (k ^ 2 * s) + E / (k ^ 2 * s) ≤ C / (k ^ 2 * s) := by
      rw [div_add_div_same]
      apply div_le_div_of_nonneg_right _ hden.le
      dsimp only [C, E, M]
      exact le_add_of_nonneg_right (by positivity)
    change Real.log D - p / 2 * L - C / (k ^ 2 * s) ≤
      renyi p (subsets k (r' + 1)) (fun _ => 1) (shuffle k (r' + 1) q)
    linarith only [hU, herr, hlin, hCbig]
  · obtain ⟨q, hq, hqlo⟩ := htwo k hkT
    obtain ⟨hq1, _, hqe, hq2⟩ := hloc k hkL q hq
    refine ⟨q, hq, ?_⟩
    set S2 := ∑ i, ((k : ℝ) * q i - 1) ^ 2
    set Q := ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * S2
    have hS0 : 0 ≤ S2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    obtain ⟨hQ0, hQhi, herr⟩ := haux S2 hS0 hq2
    have hpos : 0 ≤ 1 / (R * k) - 2 / k ^ 2 := by
      have heq : 1 / (R * k) - 2 / k ^ 2 = ((k : ℝ) - 2 * R) / (R * k ^ 2) := by
        field_simp <;> ring
      rw [heq]
      exact div_nonneg (by linarith only [hkR, hR0]) (by positivity)
    have hQlo : L - Z / k ^ 3 ≤ Q := by
      have h1 : (1 / (R * k) - 2 / k ^ 2) * (4 * γ / k - CT / k ^ 2) ≤ Q :=
        (mul_le_mul_of_nonneg_left hqlo hpos).trans
          (mul_le_mul_of_nonneg_right hcoef_lo hS0)
      have heq : (1 / (R * k) - 2 / k ^ 2) * (4 * γ / k - CT / k ^ 2)
          = L - (CT / R + 8 * γ) / k ^ 3 + 2 * CT / k ^ 4 := by
        rw [hL]; field_simp <;> ring
      have h2 : (CT / R + 8 * γ) / k ^ 3 ≤ Z / k ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hct : CT / R ≤ CT := div_le_self hCT hR1
        have hg : 8 * γ ≤ 8 * R * γ := by
          nlinarith only [mul_le_mul_of_nonneg_right hR1 hγ0.le]
        exact add_le_add hct hg
      have h3 : 0 ≤ 2 * CT / k ^ 4 := by positivity
      rw [heq] at h1
      linarith only [h1, h2, h3]
    change Cu * (e + Q) * Q ≤ E / (k ^ 2 * s) at herr
    have hU := (abs_le.mp (hgen q hq1 hqe)).2
    change renyi p (subsets k (r' + 1)) (fun _ => 1) (shuffle k (r' + 1) q) - Real.log D + p / 2 * Q
      ≤ Cu * (e + Q) * Q at hU
    have hlin : p / 2 * L - p * Z / (k ^ 2 * s) ≤ p / 2 * Q := by
      have h1 := mul_le_mul_of_nonneg_left hQlo (by positivity : (0 : ℝ) ≤ p / 2)
      have h2 : p / 2 * (Z / k ^ 3) ≤ p * Z / (k ^ 2 * s) := by
        calc p / 2 * (Z / k ^ 3) ≤ p * (Z / k ^ 3) :=
            mul_le_mul_of_nonneg_right (by linarith only [hp]) (by positivity)
          _ = p * Z / k ^ 3 := by ring
          _ ≤ p * Z / (k ^ 2 * s) :=
            div_le_div_of_nonneg_left (mul_nonneg hp.le hZ0) hden hden3
      linarith only [h1, h2]
    have hCbig : p * Z / (k ^ 2 * s) + E / (k ^ 2 * s) ≤ C / (k ^ 2 * s) := by
      rw [div_add_div_same]
      apply div_le_div_of_nonneg_right _ hden.le
      dsimp only [C, E, M, Z]
      have hpc : 0 ≤ p * CL := mul_nonneg hp.le hCL
      linarith only [hpc]
    change renyi p (subsets k (r' + 1)) (fun _ => 1) (shuffle k (r' + 1) q)
      ≤ Real.log D - p / 2 * L + C / (k ^ 2 * s)
    linarith only [hU, herr, hlin, hCbig]

/-- Prop. app-single-entropy-asymptotics, eq. (26), at the level of spectra:
    `min_{σ ∈ 𝒦_{k,t}} S_p(σ) = log k - 2p(1-t)/(t k²) + O(k^{-5/2})`. -/
theorem single_output_r1 {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      (∀ q ∈ Lam k t,
        Real.log k - 2 * p * (1 - t) / (t * k ^ 2) - C / (k ^ 2 * Real.sqrt k)
          ≤ renyi p Finset.univ (fun _ => 1) q) ∧
      (∃ q ∈ Lam k t,
        renyi p Finset.univ (fun _ => 1) q
          ≤ Real.log k - 2 * p * (1 - t) / (t * k ^ 2) + C / (k ^ 2 * Real.sqrt k)) := by
  obtain ⟨C, k₀, h⟩ := single_output ht0 ht1 hp 1 le_rfl
  refine ⟨C, k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := h k hk
  simp only [Nat.choose_one_right, Nat.cast_one, mul_one, renyi_r1] at h1 h2
  exact ⟨h1, h2⟩

end AppendixB
end
