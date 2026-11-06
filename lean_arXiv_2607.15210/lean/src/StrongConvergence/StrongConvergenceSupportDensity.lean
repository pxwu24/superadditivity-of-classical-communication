import RandomCompression.RevisionBernoulliHolomorphic
import RandomCompression.CompressionExtension
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

open Filter Set
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels

/-- Upper semicontinuity of the explicit Bernoulli support function in the
density. The compact feasible cube prevents support edges from jumping up. -/
theorem eventually_bernoulliSupport_lt {ι : Type*} [Fintype ι]
    {t k r : ℝ} (ht0 : 0<t) (ht1 : t<1) (hk : 0<k)
    (a : ι → ℝ) (hr : bernoulliSupport t k a < r) :
    ∀ᶠ s in 𝓝 t, bernoulliSupport s k a < r := by
  let Y := ι → Icc (0:ℝ) 1
  let E : Set (ℝ × Y) := {z | (∑i, bernoulliCost z.1 (z.2 i)) ≤ 1/k ∧
    r ≤ ∑i, a i*(z.2 i : ℝ)}
  have hc : Continuous (fun z : ℝ × Y => ∑i, bernoulliCost z.1 (z.2 i)) := by
    apply continuous_finset_sum
    intro i _
    dsimp [bernoulliCost]
    fun_prop
  have ho : Continuous (fun z : ℝ × Y => ∑i, a i*(z.2 i : ℝ)) := by
    apply continuous_finset_sum
    intro i _
    fun_prop
  have hE : IsClosed E := (isClosed_le hc continuous_const).inter
    (isClosed_le continuous_const ho)
  have hclosed : IsClosed (Prod.fst '' E) := isClosedMap_fst_of_compactSpace E hE
  have hnot : t ∉ Prod.fst '' E := by
    rintro ⟨⟨s,u⟩,hu,rfl⟩
    obtain ⟨M,hM,_⟩ := bernoulli_full_duality s k a ht0 ht1 hk
    have hu' : (fun i => (u i : ℝ)) ∈ bernoulliFeasible s k :=
      ⟨fun i => (u i).property.1, fun i => (u i).property.2, hu.1⟩
    have hm := hM.2 ⟨_,hu',rfl⟩
    rw [bernoulliSupport, hM.csSup_eq] at hr
    exact (not_lt_of_ge (hu.2.trans hm)) hr
  have hevent := hclosed.isOpen_compl.mem_nhds hnot
  filter_upwards [hevent, lt_mem_nhds ht0, gt_mem_nhds ht1] with s hs hs0 hs1
  obtain ⟨M,hM,_⟩ := bernoulli_full_duality s k a hs0 hs1 hk
  rw [bernoulliSupport, hM.csSup_eq]
  by_contra hn
  obtain ⟨u,hu,huM⟩ := hM.1
  change (∑i, a i*u i) = M at huM
  apply hs
  refine ⟨(s,fun i => ⟨u i,hu.1 i,hu.2.1 i⟩),?_,rfl⟩
  exact ⟨hu.2.2, by change r ≤ ∑i,a i*u i; rw [huM]; exact le_of_not_gt hn⟩

#print axioms eventually_bernoulliSupport_lt
end ProjectionChannels
