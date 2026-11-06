import Entropy.MainCoefficient
import Entropy.Infimum
import Entropy.BellGeneral

open Real Filter
noncomputable section
namespace AppendixB

/-- Comparing the proved entropy error bounds with a positive leading coefficient. -/
lemma strict_gap_from_errors (s b l a c C E K R : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hK : 0 < K) (hR : 0 < R)
    (hRK : R ≤ K) (hRs : R ≤ Real.sqrt K)
    (hgap : 2 * C + E < (c - 2 * a) * R)
    (hs : |s - (l - a / K ^ 2)| ≤ C / (K ^ 2 * Real.sqrt K))
    (hb : |b - (2 * l - c / K ^ 2)| ≤ E / K ^ 3) : b < 2 * s := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have h1 : 2 * C / Real.sqrt K ≤ 2 * C / R :=
    div_le_div_of_nonneg_left (by positivity) hR hRs
  have h2 : E / K ≤ E / R := div_le_div_of_nonneg_left hE hR hRK
  have h3 : 2 * C / R + E / R < c - 2 * a := by
    rw [← add_div, div_lt_iff₀ hR]
    exact hgap
  have he : 2 * (C / (K ^ 2 * Real.sqrt K)) + E / K ^ 3 <
      (c - 2 * a) / K ^ 2 := by
    have hsum : 2 * C / Real.sqrt K + E / K < c - 2 * a := by linarith
    have hm := (div_lt_div_iff_of_pos_right (by positivity : 0 < K ^ 2)).mpr hsum
    convert hm using 1 <;> field_simp <;> ring
  have hlo := (abs_le.mp hs).1
  have hhi := (abs_le.mp hb).2
  rw [sub_div, mul_div_assoc] at he
  linarith only [he, hlo, hhi]

/-- The limiting spectral bodies exhibit the Bell witness violation for every
positive Rényi order. The dimensions in this theorem may depend on `p`.
All asymptotic estimates used here are theorems of this project. -/
theorem spectral_nonadditivity_all_orders (p : ℝ) (hp : 0 < p) :
    ∃ k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      20 ≤ k ∧
      renyi p (Finset.range 6) (dm k) (bellNu k 5 (1 / 376)) <
        2 * infimumOutputEntropy p (1 / 376) k 5 := by
  obtain ⟨C, hC, kS, hS⟩ := single_output_infimum
    (t := (1 / 376 : ℝ)) (by norm_num) (by norm_num) hp 5 (by norm_num)
  obtain ⟨E, kB, hB⟩ := bell_output
    (t := (1 / 376 : ℝ)) (by norm_num) (by norm_num) hp 5 (by norm_num)
  let δ := Bpr p 5 375 - 300 * p
  have hδ : 0 < δ := sub_pos.mpr (main_coefficient_strict p hp)
  let R := (2 * C + |E|) / δ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨max (max kS kB) (max 20 (max R (R ^ 2))), fun k hk => ?_⟩
  have hkS : kS ≤ (k : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hkB : kB ≤ (k : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have hk20 : (20 : ℝ) ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkr : max R (R ^ 2) ≤ (k : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hkR : R ≤ (k : ℝ) := (le_max_left _ _).trans hkr
  have hkRsq : R ^ 2 ≤ (k : ℝ) := (le_max_right _ _).trans hkr
  have hkpos : (0 : ℝ) < k := by linarith only [hk20]
  have hRs : R ≤ Real.sqrt (k : ℝ) :=
    (Real.le_sqrt hR.le hkpos.le).mpr hkRsq
  refine ⟨by exact_mod_cast hk20, ?_⟩
  have hs := hS k hkS
  have hb := hB k hkB
  norm_num at hs hb
  have he : E / (k : ℝ) ^ 3 ≤ |E| / (k : ℝ) ^ 3 :=
    div_le_div_of_nonneg_right (le_abs_self E) (by positivity)
  have hgap : 2 * C + |E| < (Bpr p 5 375 - 2 * (150 * p)) * R := by
    have heq : (Bpr p 5 375 - 2 * (150 * p)) * R = 2 * C + |E| + δ := by
      dsimp [R]
      have hδeq : Bpr p 5 375 - 2 * (150 * p) = δ := by dsimp [δ]; ring
      rw [hδeq]
      field_simp
    rw [heq]
    linarith only [hδ]
  apply strict_gap_from_errors _ _ (Real.log (Nat.choose k 5)) (150 * p)
    (Bpr p 5 375) C |E| (k : ℝ) R hC (abs_nonneg E) hkpos hR hkR hRs hgap
  · convert hs using 1 <;> congr 1 <;> field_simp <;> ring
  · exact hb.trans he

/-- A strict limiting Bell witness yields finite-index nonadditivity.  This lemma
is a generic transport step: its application to actual channels supplies
the entropy limits and Bell-input bounds from the proved operator results. -/
theorem eventual_nonadditivity_from_limits
    (single bell product conjugate : ℕ → ℝ) (S B : ℝ)
    (hS : Tendsto single atTop (nhds S))
    (hB : Tendsto bell atTop (nhds B)) (hgap : B < 2 * S)
    (hBell : ∀ᶠ n in atTop, product n ≤ bell n)
    (hConjugate : ∀ᶠ n in atTop, conjugate n = single n) :
    ∀ᶠ n in atTop, product n < single n + conjugate n := by
  have h := hB.eventually_lt (tendsto_const_nhds.mul hS) hgap
  filter_upwards [h, hBell, hConjugate] with n hn hpn hcn
  rw [hcn]
  linarith

#print axioms eventual_nonadditivity_from_limits
#print axioms strict_gap_from_errors
#print axioms spectral_nonadditivity_all_orders

end AppendixB
