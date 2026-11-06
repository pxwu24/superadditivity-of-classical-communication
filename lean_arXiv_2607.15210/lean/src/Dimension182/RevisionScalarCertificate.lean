import Dimension182.K182Dual
import Entropy.OutputSpaceBody

/-!
# Lemma C.2: the scalar eigenvalue certificate in every dimension

This is the general statement, not only the numerical instance at `k = 182`.
The hypotheses imply that every feasible vector has positive mass. No
minimizer-shape, random-channel, or free-probability assumption is used.
-/

namespace ProjectionChannels.ScalarCertificate
open scoped BigOperators
open AppendixB OutputSpaceVerification
noncomputable section

def upperBound (k : ℕ) (t L z : ℝ) : ℝ :=
  z / k + K182.q t (1 - L) z + ((k : ℝ) - 1) * K182.q t (-L) z

theorem q_paper_formula (t a z : ℝ) :
    K182.q t a z =
      (a - z + Real.sqrt (a ^ 2 - 2 * a * z * (1 - 2 * t) + z ^ 2)) / 2 := by
  unfold K182.q
  congr 3
  ring

theorem coordinate_le_mul_sum {k : ℕ} {t L z : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hz : 0 ≤ z)
    (hU : upperBound k t L z ≤ 0)
    {u : Fin k → ℝ} (hu : u ∈ Dset k t) (i : Fin k) :
    u i ≤ L * ∑ j, u j := by
  classical
  let a : Fin k → ℝ := fun j => if j = i then 1 - L else -L
  have heach (j : Fin k) :
      a j * u j - z * bernoulliCost t (u j) ≤ K182.q t (a j) z :=
    K182.scalar_upper_bound ht0 ht1 (hu.1 j).1 (hu.1 j).2 _ _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => heach j)
  have hlin : (∑ j, a j * u j) = u i - L * ∑ j, u j := by
    have heq (j : Fin k) : a j * u j = (if j = i then u j else 0) - L * u j := by
      dsimp [a]
      split_ifs <;> ring
    simp_rw [heq]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  have hq : (∑ j, K182.q t (a j) z) =
      K182.q t (1 - L) z + ((k : ℝ) - 1) * K182.q t (-L) z := by
    have heq (j : Fin k) : K182.q t (a j) z =
        K182.q t (-L) z +
          (if j = i then K182.q t (1 - L) z - K182.q t (-L) z else 0) := by
      dsimp [a]
      split_ifs <;> ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib]
    simp
    ring
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hlin, hq] at hsum
  have hcost : z * (∑ j, bernoulliCost t (u j)) ≤ z / k := by
    have hc : (∑ j, bernoulliCost t (u j)) ≤ 1 / (k : ℝ) := hu.2
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hc hz
  unfold upperBound at hU
  linarith

/-- Lemma C.2, coordinate form. The additional restrictions `0 < L < 1`
in the paper are unnecessary for this implication. -/
theorem lemma_C2 {k : ℕ} {t L z : ℝ} (hk : 0 < k)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hthreshold : 1 < (k : ℝ) ^ 2 * t)
    (hz : 0 ≤ z) (hU : upperBound k t L z ≤ 0)
    {lam : Fin k → ℝ} (hlam : lam ∈ Lam k t) (i : Fin k) :
    lam i ≤ L := by
  obtain ⟨u, hu, rfl⟩ := hlam
  exact (div_le_iff₀ (body_mass_pos hk ht0 hthreshold u hu)).mpr
    (coordinate_le_mul_sum ht0 ht1 hz hU hu i)

/-- The largest feasible eigenvalue, with the supremum taken over the actual
normalized body used in the entropy modules. -/
def largestEigenvalue (k : ℕ) (t : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ lam ∈ Lam k t, ∃ i : Fin k, x = lam i}

/-- Lemma C.2 in the paper's `L* ≤ L` form. -/
theorem lemma_C2_largestEigenvalue {k : ℕ} {t L z : ℝ} (hk : 0 < k)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hthreshold : 1 < (k : ℝ) ^ 2 * t)
    (hz : 0 ≤ z) (hU : upperBound k t L z ≤ 0) :
    largestEigenvalue k t ≤ L := by
  obtain ⟨u, hu⟩ := body_nonempty (k := k) ht0 ht1
  let lam : Fin k → ℝ := fun i => u i / ∑ j, u j
  have hlam : lam ∈ Lam k t := ⟨u, hu, rfl⟩
  apply csSup_le
  · exact ⟨lam ⟨0, hk⟩, lam, hlam, ⟨0, hk⟩, rfl⟩
  · rintro x ⟨lam', hlam', i, rfl⟩
    exact lemma_C2 hk ht0 ht1 hthreshold hz hU hlam' i

end
end ProjectionChannels.ScalarCertificate
