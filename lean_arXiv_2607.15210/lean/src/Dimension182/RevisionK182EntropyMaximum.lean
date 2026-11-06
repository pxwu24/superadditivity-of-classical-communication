import Dimension182.RevisionK182Minimizer
import Mathlib.Analysis.Convex.Jensen

/-! With one probability coordinate fixed, making all other coordinates
uniform maximizes Shannon entropy. This supplies the final equality in
Appendix C.1 from an attained largest-coordinate bound. -/

open Set Filter Finset
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182

theorem finiteShannon_le_oneHighEntropy {k : ℕ} (hk : 2≤k)
    {v : Fin k → ℝ} (hv : ∀ i, 0≤v i) (hs : ∑ i, v i=1) (i : Fin k) :
    finiteShannon v ≤ oneHighEntropy k (v i) := by
  classical
  let S := (univ : Finset (Fin k)).erase i
  have hk1 : 0 < (k:ℝ)-1 := by exact_mod_cast (show (0:ℤ)<(k:ℤ)-1 by omega)
  have hcard : (S.card:ℝ)=(k:ℝ)-1 := by
    dsimp [S]
    rw [card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 1≤k)]
    simp
  have hweight : (∑ _j∈S, 1/((k:ℝ)-1))=1 := by
    simp only [sum_const,nsmul_eq_mul]
    rw [hcard]
    field_simp
  have hsum : (∑ j∈S, v j)=1-v i := by
    have h := sum_erase_add (univ : Finset (Fin k)) (fun j => v j) (mem_univ i)
    rw [hs] at h
    change (∑ j∈S, v j) + v i=1 at h
    linarith only [h]
  have hconv := Real.strictConvexOn_mul_log.convexOn.map_sum_le (t:=S)
    (w:=fun _=>1/((k:ℝ)-1)) (p:=v)
    (fun _ _ => (div_pos zero_lt_one hk1).le) hweight (fun j _=>hv j)
  simp only [smul_eq_mul] at hconv
  rw [← mul_sum,hsum,← mul_sum] at hconv
  have hc := mul_le_mul_of_nonneg_left hconv hk1.le
  have heq : ((k:ℝ)-1) *
      (((1/((k:ℝ)-1))*(1-v i)) * Real.log ((1/((k:ℝ)-1))*(1-v i))) =
      (1-v i)*Real.log ((1-v i)/((k:ℝ)-1)) := by
    field_simp
  have heq' : ((k:ℝ)-1)*((1/((k:ℝ)-1))*(∑ j∈S, v j*Real.log (v j))) =
      ∑ j∈S, v j*Real.log (v j) := by field_simp
  rw [heq,heq'] at hc
  have htotal := sum_erase_add (univ : Finset (Fin k)) (fun j=>v j*Real.log (v j)) (mem_univ i)
  change (∑ j∈S, v j*Real.log (v j)) + v i*Real.log (v i) = _ at htotal
  unfold finiteShannon oneHighEntropy
  linarith only [hc,htotal]

theorem normalizedBody_probability {k : ℕ} {t : ℝ} (ht0 : 0<t)
    (hcount : 1/(k:ℝ) < ((k:ℝ)-1)*t)
    {v : Fin k → ℝ} (hv : v ∈ normalizedBody k t) :
    (∀ i, 0≤v i) ∧ (∑ i, v i)=1 := by
  obtain ⟨u,hu,rfl⟩ := hv
  have hs := feasible_mass_pos ht0 hu (by simpa using hcount)
  constructor
  · exact fun i => div_nonneg (hu.1 i).1 hs.le
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hs)

theorem normalizedBody_permute {k : ℕ} {t : ℝ} {v : Fin k → ℝ}
    (hv : v ∈ normalizedBody k t) (e : Equiv.Perm (Fin k)) :
    (fun i => v (e i)) ∈ normalizedBody k t := by
  obtain ⟨u,hu,rfl⟩ := hv
  refine ⟨(fun i => u (e i)),⟨fun i => hu.1 (e i),?_⟩,?_⟩
  · change (∑ i, bernoulliCost t (u (e i))) ≤ _
    rw [Equiv.sum_comp e (fun i => bernoulliCost t (u i))]
    exact hu.2
  · ext i
    change u (e i)/mass u = u (e i)/(∑ j, u (e j))
    rw [Equiv.sum_comp e u]
    rfl

theorem normalizedBody_compact {k : ℕ} {t : ℝ} (ht0 : 0<t)
    (hcount : 1/(k:ℝ) < ((k:ℝ)-1)*t) : IsCompact (normalizedBody k t) := by
  have heq : normalizedBody k t =
      (fun u : Fin k → ℝ => fun i => u i/mass u) '' feasible t (1/(k:ℝ)) := by
    ext v
    simp only [normalizedBody,mem_setOf_eq,mem_image]
    constructor
    · rintro ⟨u,hu,h⟩
      exact ⟨u,hu,h.symm⟩
    · rintro ⟨u,hu,h⟩
      exact ⟨u,hu,h.symm⟩
  rw [heq]
  apply (feasible_compact t (1/(k:ℝ))).image_of_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact (continuous_apply i).continuousOn.div (by unfold mass; fun_prop)
    (fun u hu => ne_of_gt (feasible_mass_pos ht0 hu (by simpa using hcount)))

def largestCoordinate (k : ℕ) (t : ℝ) (i : Fin k) : ℝ :=
  sSup ((fun v : Fin k → ℝ => v i) '' normalizedBody k t)

/-- The final equality and monotone lower bound of C.1. The proof uses
the entropy maximum with a fixed coordinate; averaging a maximizing
vector is unnecessary. -/
theorem entropy_minimum_eq_largestCoordinate {k : ℕ} (hk : 2≤k)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1)
    (hcount : 1/(k:ℝ) < ((k:ℝ)-1)*t)
    (hupper : ∀ u ∈ feasible (ι:=Fin k) t (1/(k:ℝ)), ∀ i, u i<1/4)
    (i : Fin k) :
    IsLeast (finiteShannon '' normalizedBody k t)
      (oneHighEntropy k (largestCoordinate k t i)) ∧
    ∀ L : ℝ, largestCoordinate k t i ≤ L → L ≤ 1 →
      ∀ v ∈ normalizedBody k t, oneHighEntropy k L ≤ finiteShannon v := by
  have hshape := hasOneHighEntropyMinimizer_of_coordinate_bound hk ht0 ht1 hcount hupper
  have hne : (normalizedBody k t).Nonempty := by
    obtain ⟨v,hv,_⟩ := hshape
    exact ⟨v,hv⟩
  have hg : IsGreatest ((fun v : Fin k → ℝ => v i) '' normalizedBody k t)
      (largestCoordinate k t i) :=
    ((normalizedBody_compact ht0 hcount).image (continuous_apply i)).isGreatest_sSup
      (hne.image _)
  obtain ⟨v,hv,hvL⟩ := hg.1
  change v i = largestCoordinate k t i at hvL
  have hcap : ∀ v ∈ normalizedBody k t, ∀ j, v j ≤ largestCoordinate k t i := by
    intro w hw j
    have hp := normalizedBody_permute hw (Equiv.swap i j)
    have hm := hg.2 (mem_image_of_mem (fun v : Fin k → ℝ => v i) hp)
    simpa using hm
  have hprob := normalizedBody_probability ht0 hcount hv
  have hL1 : largestCoordinate k t i ≤ 1 := by
    rw [← hvL,← hprob.2]
    exact single_le_sum (fun j _=>hprob.1 j) (mem_univ i)
  have hlower := entropy_lower_bound_of_one_high_minimizer hk _ hshape
    (largestCoordinate k t i) hL1 hcap
  have heq : finiteShannon v = oneHighEntropy k (largestCoordinate k t i) := by
    have hh := finiteShannon_le_oneHighEntropy hk hprob.1 hprob.2 i
    rw [hvL] at hh
    exact le_antisymm hh (hlower v hv)
  constructor
  · refine ⟨⟨v,hv,heq⟩,?_⟩
    rintro s ⟨w,hw,rfl⟩
    exact hlower w hw
  · intro L hL hL1
    exact entropy_lower_bound_of_one_high_minimizer hk _ hshape L hL1
      (fun w hw j => (hcap w hw j).trans hL)

#print axioms finiteShannon_le_oneHighEntropy
#print axioms entropy_minimum_eq_largestCoordinate
end ProjectionChannels.RevisionK182
