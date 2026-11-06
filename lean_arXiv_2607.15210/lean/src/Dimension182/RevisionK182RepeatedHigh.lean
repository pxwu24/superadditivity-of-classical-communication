import Dimension182.RevisionK182Curve
import Dimension182.RevisionK182Descent

/-!
A concrete parabolic curve rules out a repeated high coordinate at an
interior nonconstant entropy minimizer. Cost and objective both decrease
strictly; no constrained second-order condition is assumed.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem not_minimum_of_parabolic_direction
    {t q : ℝ} {u d w : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hu : ∀ i, u i ∈ Ioo 0 1)
    (hs : 0 < mass u) (hq : costSum t u ≤ q)
    (hd : mass d = 0) (hdlog : ∑ i, d i * Real.log (u i) = 0)
    (hdcost : ∑ i, deriv (bernoulliCost t) (u i) * d i = 0)
    (hF : 2 * weightedSum
      (fun i => -(Real.log (u i) - logMoment u / mass u) / mass u) w -
      (∑ i, (d i)^2/u i) / mass u < 0)
    (hC : (∑ i, (costCurvature t (u i) * (d i)^2 +
      deriv (bernoulliCost t) (u i) * (2*w i))) < 0) :
    ¬ IsLocalMinOn normalizedEntropy
      {v | (∀ i, v i ∈ Icc 0 1) ∧ costSum t v ≤ q} u := by
  have hbox : ∀ᶠ x in 𝓝 (0 : ℝ), ∀ i, parabola u d w x i ∈ Ioo 0 1 := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := (hasDerivAt_parabola u d w 0 i).continuousAt
    apply hi.eventually
    simpa only [parabola_zero] using Ioo_mem_nhds (hu i).1 (hu i).2
  have hmass : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < mass (parabola u d w x) := by
    apply (hasDerivAt_curveMass u d w 0).continuousAt.eventually
    simpa only [parabola_zero] using lt_mem_nhds hs
  have hfe : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt
      (fun y => normalizedEntropy (parabola u d w y)) (curveEntropySlope u d w x) x := by
    filter_upwards [hbox,hmass] with x hx hmx
    exact hasDerivAt_curveEntropy u d w x (fun i => (hx i).1) (ne_of_gt hmx)
  have hce : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt
      (fun y => costSum t (parabola u d w y)) (curveCostSlope t u d w x) x := by
    filter_upwards [hbox] with x hx
    exact hasDerivAt_curveCost t u d w x ht0 ht1 hx
  have hfzero : curveEntropySlope u d w 0 = 0 := by
    simp only [curveEntropySlope,curveLogSlope,parabola_zero,parabolaSlope_zero,hdlog,hd]
    ring
  have hczero : curveCostSlope t u d w 0 = 0 := by
    simpa only [curveCostSlope,parabola_zero,parabolaSlope_zero] using hdcost
  have hbox' : ∀ᶠ x in 𝓝 (0 : ℝ), parabola u d w x ∈ {v | ∀ i, v i ∈ Icc 0 1} := by
    filter_upwards [hbox] with x hx
    exact fun i => ⟨(hx i).1.le,(hx i).2.le⟩
  have hn := not_sublevel_localMin_of_negative_curvatures
    (continuous_parabola u d w).continuousAt hbox' (by simpa using hq)
    hfe hce hfzero hczero
    (hasDerivAt_curveEntropySlope_zero u d w (fun i => (hu i).1) (ne_of_gt hs) hd hdlog)
    (hasDerivAt_curveCostSlope_zero t u d w ht0 ht1 hu) hF hC
  simpa only [parabola_zero] using hn

def transferDirection (i j : ι) : ι → ℝ := fun l => if l=i then 1 else if l=j then -1 else 0

theorem weighted_transfer (a : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    (∑ l, a l * transferDirection i j l) = a i - a j := by
  classical
  have hid (l : ι) : a l * transferDirection i j l =
      (if l=i then a i else 0) - (if l=j then a j else 0) := by
    by_cases hli : l=i
    · subst l
      simp [transferDirection,hij]
    · by_cases hlj : l=j
      · subst l
        simp [transferDirection,hij.symm]
      · simp [transferDirection,hli,hlj]
  simp_rw [hid]
  rw [Finset.sum_sub_distrib]
  simp

theorem weighted_transfer_sq (a : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    (∑ l, a l * (transferDirection i j l)^2) = a i + a j := by
  classical
  have hid (l : ι) : a l * (transferDirection i j l)^2 =
      (if l=i then a i else 0) + (if l=j then a j else 0) := by
    by_cases hli : l=i
    · subst l
      simp [transferDirection,hij]
    · by_cases hlj : l=j
      · subst l
        simp [transferDirection,hij.symm]
      · simp [transferDirection,hli,hlj]
  simp_rw [hid]
  rw [Finset.sum_add_distrib]
  simp

/-- The higher root of the stationarity equation cannot occur twice at
an interior constrained local entropy minimum. The proof constructs a
quadratic perturbation decreasing both cost and entropy. -/
theorem high_coordinate_unique {t q μ b : ℝ} {u : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hμ : 0 < μ)
    (hu : ∀ l, u l ∈ Ioo 0 (1/4 : ℝ)) (hs : 0 < mass u)
    (hq : costSum t u ≤ q)
    (hstationary : ∀ l, stationary t μ (u l) = logMoment u / mass u)
    (hhigh : 0 < stationarySlope t μ b)
    (hgrad : ∃ l, deriv (bernoulliCost t) (u l) ≠ 0)
    (hmin : IsLocalMinOn normalizedEntropy
      {v | (∀ l, v l ∈ Icc 0 1) ∧ costSum t v ≤ q} u)
    {i j : ι} (hi : u i = b) (hj : u j = b) : i = j := by
  by_contra hij
  have hb : 0 < b := hi ▸ (hu i).1
  obtain ⟨l,hl⟩ := hgrad
  let z : ℝ := costCurvature t b + stationarySlope t μ b / (2*μ)
  have hz : costCurvature t b < z := by
    have hpos : 0 < stationarySlope t μ b / (2*μ) := div_pos hhigh (by positivity)
    dsimp [z]
    linarith only [hpos]
  have hzF : μ*z < b⁻¹ := by
    have heq : μ*z = μ*costCurvature t b + stationarySlope t μ b / 2 := by
      dsimp [z]
      field_simp [ne_of_gt hμ]
      ring
    rw [heq]
    have hdef : stationarySlope t μ b = b⁻¹ - μ*costCurvature t b := rfl
    linarith only [hdef,hhigh]
  let d := transferDirection i j
  let w : ι → ℝ := Pi.single l (-z / deriv (bernoulliCost t) (u l))
  have hwC : (∑ a, deriv (bernoulliCost t) (u a) * w a) = -z := by
    simp only [w,Pi.single_apply,mul_ite,mul_zero]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    field_simp [hl]
    ring
  have hwF : weightedSum
      (fun a => -(Real.log (u a) - logMoment u / mass u) / mass u) w = μ*z/mass u := by
    rw [weightedSum_apply]
    simp only [w,Pi.single_apply,mul_ite,mul_zero]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    have hstat := hstationary l
    unfold stationary at hstat
    have heq : Real.log (u l) - logMoment u / mass u =
        μ * deriv (bernoulliCost t) (u l) := by linarith only [hstat]
    rw [heq]
    field_simp [hl,ne_of_gt hs]
    ring
  have hd : mass d = 0 := by
    have hh := weighted_transfer (fun _ : ι => (1 : ℝ)) hij
    simpa only [one_mul,sub_self,mass,d] using hh
  have hdlog : (∑ a, d a * Real.log (u a)) = 0 := by
    have hh := weighted_transfer (fun a => Real.log (u a)) hij
    simpa only [hi,hj,sub_self,mul_comm,d] using hh
  have hdC : (∑ a, deriv (bernoulliCost t) (u a) * d a) = 0 := by
    have hh := weighted_transfer (fun a => deriv (bernoulliCost t) (u a)) hij
    simpa only [hi,hj,sub_self,d] using hh
  have hd2 : (∑ a, (d a)^2 / u a) = 2/b := by
    have hh := weighted_transfer_sq (fun a => (u a)⁻¹) hij
    simpa only [hi,hj,div_eq_mul_inv,mul_comm,d,← two_mul] using hh
  have hdc2 : (∑ a, costCurvature t (u a) * (d a)^2) = 2*costCurvature t b := by
    have hh := weighted_transfer_sq (fun a => costCurvature t (u a)) hij
    simpa only [hi,hj,d,← two_mul] using hh
  have hC : (∑ a, (costCurvature t (u a) * (d a)^2 +
      deriv (bernoulliCost t) (u a) * (2*w a))) < 0 := by
    rw [Finset.sum_add_distrib,hdc2]
    have heq : (∑ a, deriv (bernoulliCost t) (u a) * (2*w a)) =
        2 * ∑ a, deriv (bernoulliCost t) (u a) * w a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [heq,hwC]
    linarith only [hz]
  have hF : 2 * weightedSum
      (fun a => -(Real.log (u a) - logMoment u / mass u) / mass u) w -
      (∑ a, (d a)^2/u a) / mass u < 0 := by
    rw [hwF,hd2]
    have hbase : 2*(μ*z-b⁻¹)/mass u < 0 := div_neg_of_neg_of_pos (by linarith only [hzF]) hs
    convert hbase using 1 <;> ring
  exact not_minimum_of_parabolic_direction ht0 ht1
    (fun a => ⟨(hu a).1,by linarith only [(hu a).2]⟩) hs hq
    hd hdlog hdC hF hC hmin

/-- The full smooth part of Lemma C.1: a nonconstant interior local
minimum has a unique higher coordinate and all remaining coordinates
equal. Neither stationarity nor a second-order condition is assumed. -/
theorem interior_minimum_one_high {t q : ℝ} {u : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hu : ∀ i, u i ∈ Ioo 0 (1/4 : ℝ)) (hs : 0 < mass u)
    (hq : costSum t u ≤ q) (hnonconstant : ∃ i j, u i ≠ u j)
    (hmin : IsLocalMinOn normalizedEntropy
      {v | (∀ i, v i ∈ Icc 0 1) ∧ costSum t v ≤ q} u) :
    ∃ i : ι, ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1/4 ∧
      ∀ j, u j = if j=i then b else a := by
  have hu1 : ∀ i, u i ∈ Ioo 0 1 := fun i =>
    ⟨(hu i).1,by linarith only [(hu i).2]⟩
  obtain ⟨μ,hμ,hstat⟩ := level_minimum_stationary ht0 ht1 hu hs hnonconstant
    (sublevel_minimum_is_level_minimum hu1 hq hmin)
  obtain ⟨a,b,ha,hb,hab,huab,⟨ia,hia⟩,⟨ib,hib⟩,_,hbpos⟩ :=
    stationary_vector_two_values ht0 ht1 hμ hu
      (fun i j => (hstat i).trans (hstat j).symm) hnonconstant
  have hgrad : ∃ l, deriv (bernoulliCost t) (u l) ≠ 0 := by
    by_cases hz : deriv (bernoulliCost t) (u ia) = 0
    · refine ⟨ib, ?_⟩
      have hlt : deriv (bernoulliCost t) (u ia) < deriv (bernoulliCost t) (u ib) :=
        strictMonoOn_deriv_bernoulliCost ht0 ht1 (hu1 ia) (hu1 ib)
          (by simpa only [hia,hib] using hab)
      rw [hz] at hlt
      exact ne_of_gt hlt
    · exact ⟨ia,hz⟩
  refine ⟨ib,a,b,ha.1,hab,hb.2,?_⟩
  intro j
  by_cases hji : j=ib
  · simpa only [hji,if_true] using hib
  · rw [if_neg hji]
    exact (huab j).resolve_right fun hj => hji
      (high_coordinate_unique ht0 ht1 hμ hu hs hq hstat hbpos hgrad hmin hj hib)

#print axioms not_minimum_of_parabolic_direction
#print axioms high_coordinate_unique
#print axioms interior_minimum_one_high

end ProjectionChannels.RevisionK182
