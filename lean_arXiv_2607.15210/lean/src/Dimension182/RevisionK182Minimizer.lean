import Dimension182.RevisionK182Normalization
import Dimension182.RevisionK182BoundaryExclusion
import Dimension182.RevisionK182BoundaryEqual

/-!
# The minimizer shape and the unconditional dimension-182 body certificate

This file closes `HasOneHighEntropyMinimizer` for the actual feasible body
at the exact parameters used in Appendix C. The shape is proved from
compactness, zero-coordinate exclusion, Lagrange multipliers and explicit
second-order descent. It is not an assumption.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A local entropy minimum with at least two positive coordinates and
no coordinates at one must have every coordinate positive. -/
theorem feasible_local_minimum_positive {t q : ℝ} {u : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hu : u ∈ feasible t q)
    (hs : 0 < mass u) (hupper : ∀ i, u i < 1)
    (hcount : q < ((Fintype.card ι : ℝ)-1)*t)
    (hmin : IsLocalMinOn normalizedEntropy (feasible t q) u) :
    ∀ z, 0 < u z := by
  obtain ⟨i,j,hij,hi,hj⟩ := feasible_two_positive ht0.le (fun i => (hu.1 i).1) hs hu.2 hcount
  intro z
  by_contra hz
  have hz0 : u z=0 := le_antisymm (le_of_not_gt hz) (hu.1 z).1
  rcases lt_trichotomy (u i) (u j) with hlt | heq | hgt
  · exact no_zero_with_distinct_positive ht0 ht1 hu.1 hs hu.2 hi hlt (hupper j) hz0 hmin
  · exact no_zero_with_equal_positive ht0 ht1 hu.1 hs hu.2 hij hi heq (hupper j) hz0 hmin
  · exact no_zero_with_distinct_positive ht0 ht1 hu.1 hs hu.2 hj hgt (hupper i) hz0 hmin

/-- The general minimizer argument of C.1, once its elementary coordinate
bound has placed the body inside `[0,1/4)`. All minimization, boundary,
multiplier and second-order steps are proved here. -/
theorem feasible_minimum_one_high {k : ℕ} (hk : 2 ≤ k)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcount : 1/(k:ℝ) < ((k:ℝ)-1)*t)
    {u : Fin k → ℝ} (hu : u ∈ feasible t (1/(k:ℝ)))
    (hupper : ∀ i, u i < 1/4)
    (hmin : IsMinOn normalizedEntropy (feasible t (1/(k:ℝ))) u) :
    ∃ i : Fin k, ∃ a b : ℝ, 0<a ∧ a<b ∧ b<1/4 ∧
      ∀ j, u j = if j=i then b else a := by
  have hc : 1/(k:ℝ) < ((Fintype.card (Fin k):ℝ)-1)*t := by simpa using hcount
  have hs := feasible_mass_pos ht0 hu hc
  have hpos := feasible_local_minimum_positive ht0 ht1 hu hs
    (fun i => by linarith only [hupper i]) hc hmin.localize
  exact interior_minimum_one_high ht0 ht1 (fun i => ⟨hpos i,hupper i⟩)
    hs hu.2 (feasible_minimum_nonconstant hk ht0 ht1 hs hmin) hmin.localize

def normalizedBody (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  {v | ∃ u ∈ feasible t (1/(k:ℝ)), v = fun i => u i / mass u}

/-- The minimizer-shape result for the normalized spectral body. The
remaining scalar coordinate bound can be established independently of
all the variational analysis. -/
theorem hasOneHighEntropyMinimizer_of_coordinate_bound {k : ℕ} (hk : 2 ≤ k)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcount : 1/(k:ℝ) < ((k:ℝ)-1)*t)
    (hupper : ∀ u ∈ feasible (ι:=Fin k) t (1/(k:ℝ)), ∀ i, u i<1/4) :
    HasOneHighEntropyMinimizer (normalizedBody k t) := by
  obtain ⟨u,hu,hmin⟩ := feasible_minimum_exists hk ht0 ht1 hcount
  have hs := feasible_mass_pos ht0 hu (by simpa using hcount)
  obtain ⟨i,a,b,ha,hab,_,hshape⟩ :=
    feasible_minimum_one_high hk ht0 ht1 hcount hu (hupper u hu) hmin
  obtain ⟨x,hx0,hx1,hvshape⟩ := normalization_one_high hk ha hab hshape
  let v : Fin k → ℝ := fun i => u i/mass u
  refine ⟨v,⟨u,hu,rfl⟩,i,x,hx0.le,hx1.le,hvshape,?_⟩
  rintro w ⟨u',hu',rfl⟩
  have hsu' := feasible_mass_pos ht0 hu' (by simpa using hcount)
  have hh : normalizedEntropy u ≤ normalizedEntropy u' := hmin hu'
  rw [normalizedEntropy_eq_shannon_at_boundary u hs,
    normalizedEntropy_eq_shannon_at_boundary u' hsu'] at hh
  exact hh

/-- Every global minimizer, rather than merely a chosen one, has the
one-high probability spectrum. -/
theorem normalized_minimum_one_high_of_coordinate_bound {k : ℕ} (hk : 2≤k)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1)
    (hcount : 1/(k:ℝ) < ((k:ℝ)-1)*t)
    (hupper : ∀ u ∈ feasible (ι:=Fin k) t (1/(k:ℝ)), ∀ i, u i<1/4)
    {v : Fin k → ℝ} (hv : v ∈ normalizedBody k t)
    (hmin : IsMinOn finiteShannon (normalizedBody k t) v) :
    ∃ i : Fin k, ∃ x : ℝ, 1/(k:ℝ)<x ∧ x<1 ∧
      ∀ j, v j = if j=i then x else (1-x)/((k:ℝ)-1) := by
  obtain ⟨u,hu,rfl⟩ := hv
  have hs := feasible_mass_pos ht0 hu (by simpa using hcount)
  have hminu : IsMinOn normalizedEntropy (feasible t (1/(k:ℝ))) u := by
    intro u' hu'
    have hs' := feasible_mass_pos ht0 hu' (by simpa using hcount)
    have hm := hmin (show (fun i => u' i/mass u') ∈ normalizedBody k t from ⟨u',hu',rfl⟩)
    change finiteShannon (fun i=>u i/mass u) ≤ finiteShannon (fun i=>u' i/mass u') at hm
    rw [← normalizedEntropy_eq_shannon_at_boundary u hs,
      ← normalizedEntropy_eq_shannon_at_boundary u' hs'] at hm
    exact hm
  obtain ⟨i,a,b,ha,hab,_,hshape⟩ := feasible_minimum_one_high hk ht0 ht1 hcount hu
    (hupper u hu) hminu
  obtain ⟨x,hx0,hx1,hvshape⟩ := normalization_one_high hk ha hab hshape
  exact ⟨i,x,hx0,hx1,hvshape⟩

/-- Appendix C.1 instantiated at the certified parameters. This theorem
has no minimizer-shape, stationarity, or numerical hypothesis. -/
theorem hasOneHighEntropyMinimizer_182 :
    HasOneHighEntropyMinimizer K182.normalizedFeasible := by
  have ht0 : 0 < K182.t := by norm_num [K182.t]
  have ht1 : K182.t < 1 := by norm_num [K182.t]
  have hcount : (1:ℝ)/182 < ((182:ℝ)-1)*K182.t := by norm_num [K182.t]
  obtain ⟨u,hu,hmin⟩ := feasible_minimum_exists (k:=182) (by norm_num) ht0 ht1 hcount
  have hs : 0 < mass u := feasible_mass_pos ht0 hu (by simpa using hcount)
  have hupper : ∀ i, u i<1/4 := fun i => K182.coordinate_lt_quarter
    (fun i => (hu.1 i).1) (fun i => (hu.1 i).2) hu.2 i
  obtain ⟨i,a,b,ha,hab,_,hshape⟩ := feasible_minimum_one_high
    (by norm_num : 2≤182) ht0 ht1 hcount hu hupper hmin
  obtain ⟨x,hx0,hx1,hvshape⟩ := normalization_one_high (by norm_num : 2≤182) ha hab hshape
  let v : Fin 182 → ℝ := fun i => u i / mass u
  have hv : v ∈ K182.normalizedFeasible :=
    ⟨u,fun i => (hu.1 i).1,fun i => (hu.1 i).2,hu.2,rfl⟩
  refine ⟨v,hv,i,x,hx0.le,hx1.le,hvshape,?_⟩
  intro w hw
  obtain ⟨u',hu0',hu1',hcost',rfl⟩ := hw
  have hsu' : 0 < mass u' := K182.sum_pos hu0' hcost'
  have hh := hmin (show u' ∈ feasible K182.t (1/182) from
    ⟨fun i => ⟨hu0' i,hu1' i⟩,hcost'⟩)
  change normalizedEntropy u ≤ normalizedEntropy u' at hh
  rw [normalizedEntropy_eq_shannon_at_boundary u hs,
    normalizedEntropy_eq_shannon_at_boundary u' hsu'] at hh
  exact hh

/-- The rigorous exact-rational `k=182` limiting-body entropy gap.
All hypotheses of the previously conditional certificate are discharged. -/
theorem certified_entropy_gap_182 {v : Fin 182 → ℝ}
    (hv : v ∈ K182.normalizedFeasible) :
    (477:ℝ)/1000000 < 2*finiteShannon v - K182.bellEntropy :=
  K182.entropy_gap_of_one_high_minimizer hasOneHighEntropyMinimizer_182 hv

#print axioms feasible_local_minimum_positive
#print axioms feasible_minimum_one_high
#print axioms hasOneHighEntropyMinimizer_of_coordinate_bound
#print axioms normalized_minimum_one_high_of_coordinate_bound
#print axioms hasOneHighEntropyMinimizer_182
#print axioms certified_entropy_gap_182
end ProjectionChannels.RevisionK182
