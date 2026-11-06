import HaarProjections.RevisionCanonicalEnsemble
import Mathlib.Tactic

/-! Quantitative floor-rank estimates for the canonical ensemble. -/
open Set
namespace ProjectionChannels.Canonical

lemma rankSequence_density_mem_Icc {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0≤t) (ht1 : t≤1) (n : ℕ) :
    (rankSequence k t n:ℝ)/(((n+1)*k:ℕ):ℝ) ∈ Icc (0:ℝ) 1 := by
  have hN : (0:ℝ)<(((n+1)*k:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hk
  refine ⟨by positivity, (div_le_one hN).mpr ?_⟩
  exact_mod_cast (show rankSequence k t n≤(n+1)*k from by
    simpa only [Index, Fintype.card_prod, Fintype.card_fin] using rankSequence_le ht0 ht1 n)

/-- Rounding a density to an integer rank costs at most one total-dimension unit. -/
lemma rankSequence_density_abs_sub_le {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht : 0≤t) (n : ℕ) :
    |(rankSequence k t n:ℝ)/(((n+1)*k:ℕ):ℝ)-t| ≤ 1/(((n+1)*k:ℕ):ℝ) := by
  let N : ℝ := (((n+1)*k:ℕ):ℝ)
  have hN : 0<N := by dsimp [N]; exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hk
  have harg : (k:ℝ)*(n+1)=N := by dsimp [N]; push_cast; ring
  have hlo : (rankSequence k t n:ℝ)≤t*N := by
    simpa only [rankSequence, harg] using Nat.floor_le (mul_nonneg ht hN.le)
  have hhi : t*N<(rankSequence k t n:ℝ)+1 := by
    simpa only [rankSequence, harg] using Nat.lt_floor_add_one (t*N)
  change |(rankSequence k t n:ℝ)/N-t|≤1/N
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hN).mpr hlo))]
  apply (le_div_iff₀ hN).mpr
  have heq : (t-(rankSequence k t n:ℝ)/N)*N=t*N-(rankSequence k t n:ℝ) := by
    field_simp
  rw [heq]
  linarith

#print axioms rankSequence_density_abs_sub_le
end ProjectionChannels.Canonical
