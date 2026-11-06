import Dimension182.RevisionK182Multiplier
import Dimension182.RevisionK182BoundaryTools
import Mathlib.Analysis.Convex.Jensen

/-! The entropy minimizer cannot be the uniform vector (Appendix C.1, Step 1). -/
namespace ProjectionChannels.RevisionK182
open Set Filter Finset
open scoped Topology BigOperators
noncomputable section

theorem normalizedEntropy_lt_log_of_nonconstant {k : ℕ} (hk : 0 < k)
    (u : Fin k → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : 0 < mass u)
    (hne : ∃ i j, u i ≠ u j) : normalizedEntropy u < Real.log (k : ℝ) := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hj := Real.strictConvexOn_mul_log.map_sum_lt (t := univ)
    (w := fun _ : Fin k => 1/(k:ℝ)) (p := u)
    (fun _ _ => div_pos zero_lt_one hkpos)
    (by simp [hkpos.ne']) (fun i _ => hu i)
    (by obtain ⟨i,j,hij⟩ := hne; exact ⟨i,mem_univ i,j,mem_univ j,hij⟩)
  simp only [smul_eq_mul] at hj
  rw [← mul_sum, ← mul_sum] at hj
  change ((1/(k:ℝ))*mass u)*Real.log ((1/(k:ℝ))*mass u) <
    (1/(k:ℝ))*logMoment u at hj
  rw [show (1/(k:ℝ))*mass u = mass u/(k:ℝ) by ring,
    Real.log_div hs.ne' hkpos.ne'] at hj
  have hmul := (mul_lt_mul_left hkpos).mpr hj
  have heq : (k:ℝ) * (mass u/(k:ℝ)*(Real.log (mass u)-Real.log (k:ℝ))) =
      mass u*(Real.log (mass u)-Real.log (k:ℝ)) := by field_simp
  have heq2 : (k:ℝ)*((1/(k:ℝ))*logMoment u)=logMoment u := by field_simp
  rw [heq,heq2] at hmul
  have h := (lt_div_iff₀ hs).mpr (by nlinarith only [hmul] :
    (Real.log (mass u)-Real.log (k:ℝ))*mass u < logMoment u)
  unfold normalizedEntropy
  linarith

theorem normalizedEntropy_const {k : ℕ} (hk : 0 < k) {c : ℝ} (hc : 0 < c) :
    normalizedEntropy (fun _ : Fin k => c) = Real.log (k:ℝ) := by
  have hk0 : (k:ℝ) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
  simp only [normalizedEntropy, mass, logMoment, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Real.log_mul hk0 hc.ne']
  field_simp
  <;> ring

/-- A genuinely feasible positive nonconstant vector exists in every dimension
at least two; no asymptotic dimension restriction is required. -/
theorem exists_feasible_entropy_lt_log {k : ℕ} (hk : 2 ≤ k)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ u : Fin k → ℝ, (∀ i, u i ∈ Set.Ioo 0 1) ∧
      costSum t u < 1/(k:ℝ) ∧ normalizedEntropy u < Real.log (k:ℝ) := by
  classical
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  let i0 : Fin k := ⟨0,by omega⟩
  let i1 : Fin k := ⟨1,by omega⟩
  let u : ℝ → Fin k → ℝ := fun e i => t + if i=i0 then e else 0
  have hu0 : u 0 = fun _ => t := by ext i; simp [u]
  have hc : Continuous (fun e => costSum t (u e)) := by
    unfold costSum bernoulliCost
    apply continuous_finset_sum
    intro i _
    dsimp [u]
    split_ifs <;> fun_prop
  have hz : costSum t (u 0) = 0 := by
    rw [hu0]
    simp [costSum, bernoulliCost_self]
  have hcost : ∀ᶠ e : ℝ in 𝓝 0, costSum t (u e) < 1/(k:ℝ) :=
    hc.continuousAt.eventually (Iio_mem_nhds (by change costSum t (u 0) < _; rw [hz]; positivity))
  have hbox : ∀ᶠ e : ℝ in 𝓝 0, ∀ i, u e i ∈ Set.Ioo 0 1 := by
    apply Filter.eventually_all.mpr
    intro i
    have hui : ContinuousAt (fun e => u e i) 0 := by
      dsimp [u]
      split_ifs <;> fun_prop
    exact hui.eventually (isOpen_Ioo.mem_nhds (by simpa [u] using And.intro ht0 ht1))
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp (hbox.and hcost)
  let e := δ/2
  have he : 0 < e := by dsimp [e]; positivity
  have hem : dist e 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos he]; dsimp [e]; linarith
  have hv := hd hem
  refine ⟨u e,hv.1,hv.2,normalizedEntropy_lt_log_of_nonconstant (by omega) _
    (fun i => (hv.1 i).1.le) ?_ ?_⟩
  · unfold mass
    exact sum_pos (fun i _ => (hv.1 i).1) ⟨i0, mem_univ i0⟩
  · refine ⟨i0,i1,?_⟩
    have hi : i1 ≠ i0 := by
      intro h
      have hh := congrArg Fin.val h
      norm_num [i1,i0] at hh
    simp only [u, if_pos rfl, if_neg hi, if_true, add_zero]
    linarith

end
end ProjectionChannels.RevisionK182
