import Entropy.Localization

set_option maxHeartbeats 400000
open Real Finset
noncomputable section
namespace AppendixB

/-- Pure arithmetic: the last step of Prop. app-localization (ii). -/
lemma spike_final {t K N S : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hK : 2 ≤ K)
    (hN0 : 0 ≤ 4 * t * (1 - t) * K - 1) (hN : 4 * t * (1 - t) * K - 1 ≤ N)
    (hS0 : 0 < S) (hS : S ≤ K * t + 1 / K) :
    4 * ((1 - t) / t) / K - 8 / t ^ 3 / K ^ 2 ≤ N / S ^ 2 := by
  have hK0 : 0 < K := by linarith
  have ht0' := ht0.ne'
  have hK0' := hK0.ne'
  set A := 4 * t * (1 - t) * K - 1 with hA
  set D := (K * t + 1 / K) ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hDlo : t ^ 2 * K ^ 2 ≤ D := by
    rw [hD]
    have h1 : 0 ≤ 1 / K := by positivity
    nlinarith [sq_nonneg (1 / K), mul_nonneg (mul_nonneg hK0.le ht0.le) h1]
  have hDhi : D - t ^ 2 * K ^ 2 ≤ 3 := by
    rw [hD]
    have e : (K * t + 1 / K) ^ 2 - t ^ 2 * K ^ 2 = 2 * t + 1 / K ^ 2 := by
      field_simp <;> ring
    rw [e]
    have : 1 / K ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hAhi : A ≤ 4 * t * K := by
    rw [hA]; nlinarith [mul_pos (mul_pos ht0 ht0) hK0]
  have hAD : A / D ≤ N / S ^ 2 := by
    calc A / D ≤ N / D := div_le_div_of_nonneg_right hN hD0.le
      _ ≤ N / S ^ 2 :=
          div_le_div_of_nonneg_left (le_trans hN0 hN) (by positivity) (pow_le_pow_left hS0.le hS 2)
  have key : 4 * ((1 - t) / t) / K - A / D ≤ 8 / t ^ 3 / K ^ 2 := by
    have e1 : 4 * ((1 - t) / t) / K = (A + 1) / (t ^ 2 * K ^ 2) := by
      rw [hA]; field_simp <;> ring
    rw [e1, div_sub_div _ _ (by positivity) hD0.ne', div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (A + 1) * D - t ^ 2 * K ^ 2 * A ≤ 3 * A + D := by
      nlinarith [mul_le_mul_of_nonneg_left hDhi hN0]
    have h2 : 0 ≤ t ^ 3 * K ^ 2 := by positivity
    have h3 : ((A + 1) * D - t ^ 2 * K ^ 2 * A) * (t ^ 3 * K ^ 2)
        ≤ (3 * A + D) * (t ^ 3 * K ^ 2) := mul_le_mul_of_nonneg_right h1 h2
    have h4 : (3 * A + D) * (t ^ 3 * K ^ 2) ≤ (12 * t * K + D) * (t ^ 3 * K ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    have h7 : 12 * t ^ 2 * K ≤ (8 - t) * D := by
      have i1 : (8 - t) * (t ^ 2 * K ^ 2) ≤ (8 - t) * D :=
        mul_le_mul_of_nonneg_left hDlo (by linarith)
      have i2 : 7 * (t ^ 2 * K ^ 2) ≤ (8 - t) * (t ^ 2 * K ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have i3 : t ^ 2 * K * 2 ≤ t ^ 2 * K * K :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      have i4 : 0 ≤ t ^ 2 * K := by positivity
      nlinarith [i1, i2, i3, i4]
    have h5 : (12 * t * K + D) * (t ^ 3 * K ^ 2) ≤ 8 * (t ^ 2 * K ^ 2 * D) := by
      have h6 : 0 ≤ t ^ 2 * K ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h7 h6]
    linarith [h3, h4, h5]
  linarith [hAD, key]


end AppendixB
end
