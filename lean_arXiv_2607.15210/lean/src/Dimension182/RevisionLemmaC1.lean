import Dimension182.RevisionK182EntropyMaximum
import Dimension182.RevisionCoordinateCap
import Entropy.Defs

/-!
# Lemma C.1: reduction of the entropy minimum

The hypotheses below are precisely those in the paper. The proof includes
compact minimization, exclusion of zero coordinates, the positive Lagrange
multiplier, the two-value reduction, and a concrete second-order feasible
perturbation excluding a repeated high coordinate. No shape, KKT, curvature,
or numerical result is assumed.

The equality for the minimum is stated as `IsLeast` of the actual entropy
image, so existence of a minimizing spectrum is included.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182

theorem normalizedBody_eq_Lam (k : ℕ) (t : ℝ) :
    normalizedBody k t = AppendixB.Lam k t := rfl

private theorem lemma_C1_parameters {k : ℕ} (hk : 2≤k) {t : ℝ}
    (htlo : 1/((k:ℝ)*((k:ℝ)-1)) < t) (hthi : t < 1-1/(k:ℝ))
    (hbar : (Real.sqrt (t*(1-1/(k:ℝ))) + Real.sqrt ((1-t)/k))^2 < 1/4) :
    0<t ∧ t<1 ∧ 1/(k:ℝ) < ((k:ℝ)-1)*t ∧
      ∀ u ∈ feasible (ι:=Fin k) t (1/(k:ℝ)), ∀ i, u i<1/4 := by
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hk1 : 0 < (k:ℝ)-1 := by exact_mod_cast (show (0:ℤ)<(k:ℤ)-1 by omega)
  have hq0 : 0 < 1/(k:ℝ) := div_pos zero_lt_one hkpos
  have hq1 : 1/(k:ℝ) < 1 := by
    apply (div_lt_one hkpos).mpr
    linarith only [hk1]
  have ht0 : 0<t := (div_pos zero_lt_one (mul_pos hkpos hk1)).trans htlo
  have ht1 : t<1 := by linarith only [hthi,hq0]
  have hcount : 1/(k:ℝ) < ((k:ℝ)-1)*t := by
    have hm := (div_lt_iff₀ (mul_pos hkpos hk1)).mp htlo
    apply (div_lt_iff₀ hkpos).mpr
    nlinarith only [hm]
  refine ⟨ht0,ht1,hcount,?_⟩
  intro u hu i
  have hcost : bernoulliCost t (u i) ≤ 1/(k:ℝ) :=
    (Finset.single_le_sum (fun j _=>bernoulliCost_nonneg t (u j)) (Finset.mem_univ i)).trans hu.2
  have hcap := bernoulliCost_coordinate_cap ht0 ht1 hq0 hq1
    (by linarith only [hthi]) (hu.1 i).1 (hu.1 i).2 hcost
  have hbar' : (Real.sqrt (t*(1-1/(k:ℝ))) + Real.sqrt ((1-t)*(1/(k:ℝ))))^2 < 1/4 := by
    simpa only [mul_one_div] using hbar
  exact hcap.trans_lt hbar'

/-- Lemma C.1, first assertion: every minimizing spectrum has one higher
coordinate and all other coordinates equal. -/
theorem lemma_C1_minimizer_shape {k : ℕ} (hk : 2≤k) {t : ℝ}
    (htlo : 1/((k:ℝ)*((k:ℝ)-1)) < t) (hthi : t < 1-1/(k:ℝ))
    (hbar : (Real.sqrt (t*(1-1/(k:ℝ))) + Real.sqrt ((1-t)/k))^2 < 1/4)
    {v : Fin k → ℝ} (hv : v ∈ AppendixB.Lam k t)
    (hmin : IsMinOn finiteShannon (AppendixB.Lam k t) v) :
    ∃ i : Fin k, ∃ x : ℝ, 1/(k:ℝ)<x ∧ x<1 ∧
      ∀ j, v j = if j=i then x else (1-x)/((k:ℝ)-1) := by
  obtain ⟨ht0,ht1,hcount,hupper⟩ := lemma_C1_parameters hk htlo hthi hbar
  exact normalized_minimum_one_high_of_coordinate_bound hk ht0 ht1 hcount hupper hv hmin

/-- Lemma C.1, equation (111), including existence and the lower bound
for every certified upper bound `L` on the largest coordinate. -/
theorem lemma_C1_entropy_minimum {k : ℕ} (hk : 2≤k) {t : ℝ}
    (htlo : 1/((k:ℝ)*((k:ℝ)-1)) < t) (hthi : t < 1-1/(k:ℝ))
    (hbar : (Real.sqrt (t*(1-1/(k:ℝ))) + Real.sqrt ((1-t)/k))^2 < 1/4)
    (i : Fin k) :
    IsLeast (finiteShannon '' AppendixB.Lam k t)
      (oneHighEntropy k (largestCoordinate k t i)) ∧
    ∀ L : ℝ, largestCoordinate k t i ≤ L → L ≤ 1 →
      ∀ v ∈ AppendixB.Lam k t, oneHighEntropy k L ≤ finiteShannon v := by
  obtain ⟨ht0,ht1,hcount,hupper⟩ := lemma_C1_parameters hk htlo hthi hbar
  exact entropy_minimum_eq_largestCoordinate hk ht0 ht1 hcount hupper i

#print axioms lemma_C1_minimizer_shape
#print axioms lemma_C1_entropy_minimum
#print axioms hasOneHighEntropyMinimizer_182
#print axioms certified_entropy_gap_182
end ProjectionChannels.RevisionK182
