import Dimension182.RevisionK182Compact
import Dimension182.RevisionK182RepeatedHigh

/-! Normalizing the one-high interior minimizer gives precisely the
probability vector used by the entropy certificate. -/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182

theorem normalization_one_high {k : ℕ} (hk : 2 ≤ k) {u : Fin k → ℝ}
    {i : Fin k} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hu : ∀ j, u j = if j=i then b else a) :
    ∃ x : ℝ, 1/(k:ℝ) < x ∧ x < 1 ∧
      ∀ j, u j / mass u = if j=i then x else (1-x)/((k:ℝ)-1) := by
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hk1 : 0 < (k:ℝ)-1 := by exact_mod_cast (show (0:ℤ)<(k:ℤ)-1 by omega)
  have hb : 0 < b := ha.trans hab
  have hmass : mass u = ((k:ℝ)-1)*a+b := by
    unfold mass
    have hcoord (j : Fin k) : u j = a + if j=i then b-a else 0 := by
      rw [hu j]
      split_ifs <;> ring
    simp_rw [hcoord]
    rw [Finset.sum_add_distrib]
    simp
    ring
  have hs : 0 < mass u := by rw [hmass]; positivity
  refine ⟨b/mass u,?_,?_,?_⟩
  · apply (div_lt_div_iff₀ hkpos hs).mpr
    rw [hmass]
    have hmul := mul_pos hk1 (sub_pos.mpr hab)
    nlinarith only [hmul]
  · apply (div_lt_one hs).mpr
    rw [hmass]
    have hmul := mul_pos hk1 ha
    linarith only [hmul]
  · intro j
    by_cases hji : j=i
    · simp only [hu j,if_pos hji]
    · simp only [hu j,if_neg hji]
      field_simp [ne_of_gt hk1,ne_of_gt hs]
      rw [hmass]
      ring

#print axioms normalization_one_high
end ProjectionChannels.RevisionK182
