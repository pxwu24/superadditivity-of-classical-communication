import Dimension182.RevisionK182Nonuniform
import Dimension182.K182Dual

/-! Compact minimization, nonconstant minimizers, and the requirement of
at least two positive coordinates. These support Appendix C.1. -/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def feasible (t q : ℝ) : Set (ι → ℝ) :=
  {u | (∀ i, u i ∈ Icc 0 1) ∧ costSum t u ≤ q}

theorem feasible_compact (t q : ℝ) : IsCompact (feasible (ι:=ι) t q) := by
  have hbox : IsCompact {u : ι → ℝ | ∀ i, u i ∈ Icc (0:ℝ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  have hcost : Continuous (costSum (ι:=ι) t) := by
    unfold costSum bernoulliCost
    fun_prop
  exact hbox.inter_right (isClosed_le hcost continuous_const)

theorem normalizedEntropy_continuousOn (C : Set (ι → ℝ))
    (hC : ∀ u ∈ C, 0 < mass u) : ContinuousOn normalizedEntropy C := by
  have hm : Continuous (mass (ι:=ι)) := by unfold mass; fun_prop
  have hl : Continuous (logMoment (ι:=ι)) := by
    unfold logMoment
    apply continuous_finset_sum
    intro i _
    exact Real.continuous_mul_log.comp (continuous_apply i)
  exact (hm.continuousOn.log (fun u hu => ne_of_gt (hC u hu))).sub
    (hl.continuousOn.div hm.continuousOn (fun u hu => ne_of_gt (hC u hu)))

theorem normalizedEntropy_eq_shannon_at_boundary {k : ℕ} (u : Fin k → ℝ)
    (hs : 0 < mass u) :
    normalizedEntropy u = finiteShannon (fun i => u i / mass u) := by
  unfold finiteShannon
  have hterm (i : Fin k) : u i / mass u * Real.log (u i / mass u) =
      u i / mass u * (Real.log (u i)-Real.log (mass u)) := by
    by_cases hz : u i=0
    · simp [hz]
    · rw [Real.log_div hz (ne_of_gt hs)]
  simp_rw [hterm]
  simp only [mul_sub,Finset.sum_sub_distrib]
  have h₁ : (∑ i, u i / mass u * Real.log (u i)) = logMoment u / mass u := by
    unfold logMoment
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h₂ : (∑ i, u i / mass u * Real.log (mass u)) = Real.log (mass u) := by
    rw [← Finset.sum_mul,← Finset.sum_div]
    change (mass u / mass u)*Real.log (mass u) = _
    rw [div_self (ne_of_gt hs),one_mul]
  rw [h₁,h₂]
  unfold normalizedEntropy
  ring

theorem feasible_two_positive {t q : ℝ} {u : ι → ℝ}
    (ht : 0 ≤ t) (hu : ∀ i, 0 ≤ u i) (hs : 0 < mass u)
    (hq : costSum t u ≤ q) (hcount : q < ((Fintype.card ι : ℝ)-1)*t) :
    ∃ i j, i≠j ∧ 0 < u i ∧ 0 < u j := by
  have hex : ∃ i, 0 < u i := by
    by_contra h
    push_neg at h
    have hsum : mass u ≤ 0 := Finset.sum_nonpos fun i _ => h i
    exact (not_lt_of_ge hsum) hs
  obtain ⟨i,hi⟩ := hex
  by_contra hn
  have hz (j : ι) (hji : j≠i) : u j=0 := by
    by_contra hne
    have hj : 0 < u j := lt_of_le_of_ne (hu j) (Ne.symm hne)
    exact hn ⟨i,j,hji.symm,hi,hj⟩
  have hc0 : bernoulliCost t 0=t := bernoulliCost_zero ht
  have heq (j : ι) : bernoulliCost t (u j) =
      t + if j=i then bernoulliCost t (u i)-t else 0 := by
    by_cases hji : j=i
    · simp [hji]
    · simp [hji,hz j hji,hc0]
  have hsum : costSum t u = (Fintype.card ι : ℝ)*t + bernoulliCost t (u i)-t := by
    unfold costSum
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => heq j)]
    rw [Finset.sum_add_distrib]
    simp
    ring
  rw [hsum] at hq
  have hc := bernoulliCost_nonneg t (u i)
  nlinarith only [hc,hq,hcount]

theorem feasible_mass_pos {t q : ℝ} {u : ι → ℝ}
    (ht : 0 < t) (hu : u ∈ feasible t q)
    (hcount : q < ((Fintype.card ι : ℝ)-1)*t) : 0 < mass u := by
  have hn : 0 ≤ mass u := Finset.sum_nonneg fun i _ => (hu.1 i).1
  by_contra h
  have hs : mass u = 0 := le_antisymm (le_of_not_gt h) hn
  have hui : ∀ i, u i=0 := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      (hu.1 i).1)).mp hs
    exact fun i => hz i (Finset.mem_univ i)
  have hcost := hu.2
  simp only [costSum,hui,bernoulliCost_zero ht.le,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] at hcost
  nlinarith only [hcost,hcount,ht]

theorem feasible_minimum_exists {k : ℕ} (hk : 2 ≤ k)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcount : 1/(k:ℝ) < ((k:ℝ)-1)*t) :
    ∃ u ∈ feasible (ι:=Fin k) t (1/(k:ℝ)),
      IsMinOn normalizedEntropy (feasible t (1/(k:ℝ))) u := by
  have hnonempty : (feasible (ι:=Fin k) t (1/(k:ℝ))).Nonempty := by
    refine ⟨fun _ => t,fun _ => ⟨ht0.le,ht1.le⟩,?_⟩
    simp only [costSum,bernoulliCost_self,Finset.sum_const_zero]
    positivity
  exact (feasible_compact t (1/(k:ℝ))).exists_isMinOn hnonempty
    (normalizedEntropy_continuousOn _ (fun u hu =>
      feasible_mass_pos ht0 hu (by simpa using hcount)))

theorem feasible_minimum_nonconstant {k : ℕ} (hk : 2 ≤ k)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {u : Fin k → ℝ}
    (hs : 0 < mass u)
    (hmin : IsMinOn normalizedEntropy (feasible t (1/(k:ℝ))) u) :
    ∃ i j, u i ≠ u j := by
  by_contra h
  push_neg at h
  let i0 : Fin k := ⟨0,by omega⟩
  have heq : u = fun _ => u i0 := funext fun i => h i i0
  have hpos : 0 < u i0 := by
    have hkpos : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
    rw [heq] at hs
    simp only [mass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    exact (mul_pos_iff_of_pos_left hkpos).mp hs
  have hfu : normalizedEntropy u = Real.log (k:ℝ) := by
    rw [heq]
    exact normalizedEntropy_const (by omega) hpos
  obtain ⟨v,hv,hvc,hvf⟩ := exists_feasible_entropy_lt_log hk ht0 ht1
  have hvfeas : v ∈ feasible t (1/(k:ℝ)) :=
    ⟨fun i => ⟨(hv i).1.le,(hv i).2.le⟩,hvc.le⟩
  have hm := hmin hvfeas
  rw [hfu] at hm
  exact (not_lt_of_ge hm) hvf

end ProjectionChannels.RevisionK182
