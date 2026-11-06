import Dimension182.RevisionK182Stationarity
import Dimension182.K182Entropy
import Mathlib.Analysis.Calculus.LagrangeMultipliers

/-!
The differentiable multiplier step of Appendix C.1. This file derives
stationarity from a genuine local minimum on a cost level set, using
Mathlib's Lagrange-multiplier theorem. It does not assume stationarity,
a two-value shape, or a multiplier as input.

Passing from the original feasible body to such an interior level-set
minimum requires the boundary-coordinate exclusion and the proof that
the cost constraint is active. Those are not claimed here.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weightedSum (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousLinearMap.proj i

@[simp] theorem weightedSum_apply (a v : ι → ℝ) :
    weightedSum a v = ∑ i, a i * v i := by
  simp [weightedSum, ContinuousLinearMap.sum_apply]

@[simp] theorem weightedSum_single (a : ι → ℝ) (i : ι) :
    weightedSum a (Pi.single i 1) = a i := by
  simp [weightedSum_apply, Pi.single_apply]

def mass (u : ι → ℝ) : ℝ := ∑ i, u i
def logMoment (u : ι → ℝ) : ℝ := ∑ i, u i * Real.log (u i)
def normalizedEntropy (u : ι → ℝ) : ℝ := Real.log (mass u) - logMoment u / mass u
def costSum (t : ℝ) (u : ι → ℝ) : ℝ := ∑ i, bernoulliCost t (u i)

/-- The smooth entropy expression is exactly the Shannon entropy of the
normalized vector, not a surrogate objective. -/
theorem normalizedEntropy_eq_shannon {k : ℕ} (u : Fin k → ℝ)
    (hu : ∀ i, 0 < u i) (hs : 0 < mass u) :
    normalizedEntropy u = finiteShannon (fun i => u i / mass u) := by
  unfold finiteShannon
  simp_rw [Real.log_div (ne_of_gt (hu _)) (ne_of_gt hs)]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have h₁ : (∑ i, u i / mass u * Real.log (u i)) = logMoment u / mass u := by
    unfold logMoment
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h₂ : (∑ i, u i / mass u * Real.log (mass u)) = Real.log (mass u) := by
    rw [← Finset.sum_mul, ← Finset.sum_div]
    change (mass u / mass u) * Real.log (mass u) = _
    rw [div_self (ne_of_gt hs), one_mul]
  rw [h₁,h₂]
  unfold normalizedEntropy
  ring

theorem hasStrictDerivAt_cost {t v : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hv0 : 0 < v) (hv1 : v < 1) :
    HasStrictDerivAt (bernoulliCost t) (deriv (bernoulliCost t) v) v := by
  have hid := hasStrictDerivAt_id v
  have ha : t * (1-v) ≠ 0 := ne_of_gt (mul_pos ht0 (sub_pos.mpr hv1))
  have hb : (1-t) * v ≠ 0 := ne_of_gt (mul_pos (sub_pos.mpr ht1) hv0)
  have h := (((hid.const_sub 1).const_mul t).sqrt ha).sub
    ((hid.const_mul (1-t)).sqrt hb)
  have hp := h.mul h
  simp only [← sq] at hp
  change HasStrictDerivAt (bernoulliCost t) _ v at hp
  convert hp using 1
  exact hp.hasDerivAt.deriv

theorem hasStrictFDerivAt_mass (u : ι → ℝ) :
    HasStrictFDerivAt mass (weightedSum fun _ => 1) u := by
  unfold mass weightedSum
  apply HasStrictFDerivAt.sum
  intro i _
  simpa only [one_smul] using hasStrictFDerivAt_apply (𝕜 := ℝ) i u

theorem hasStrictFDerivAt_logMoment (u : ι → ℝ) (hu : ∀ i, 0 < u i) :
    HasStrictFDerivAt logMoment (weightedSum fun i => Real.log (u i) + 1) u := by
  unfold logMoment weightedSum
  apply HasStrictFDerivAt.sum
  intro i _
  have hi := hasStrictFDerivAt_apply (𝕜 := ℝ) i u
  convert hi.mul (hi.log (ne_of_gt (hu i))) using 1
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  field_simp [ne_of_gt (hu i)]
  ring

theorem hasStrictFDerivAt_costSum (t : ℝ) (u : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hu : ∀ i, u i ∈ Ioo 0 1) :
    HasStrictFDerivAt (costSum t) (weightedSum fun i => deriv (bernoulliCost t) (u i)) u := by
  unfold costSum weightedSum
  apply HasStrictFDerivAt.sum
  intro i _
  exact (hasStrictDerivAt_cost ht0 ht1 (hu i).1 (hu i).2).comp_hasStrictFDerivAt u
    (hasStrictFDerivAt_apply (𝕜 := ℝ) i u)

theorem hasStrictFDerivAt_normalizedEntropy (u : ι → ℝ)
    (hu : ∀ i, 0 < u i) (hs : mass u ≠ 0) :
    HasStrictFDerivAt normalizedEntropy
      (weightedSum fun i => -(Real.log (u i) - logMoment u / mass u) / mass u) u := by
  have hm := hasStrictFDerivAt_mass u
  have hl := hasStrictFDerivAt_logMoment u hu
  have hinv := (hasStrictDerivAt_inv hs).comp_hasStrictFDerivAt u hm
  have hh := (hm.log hs).sub (hl.mul hinv)
  convert hh using 1
  ext v
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, weightedSum_apply, one_mul]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hs]
  ring

/-- Genuine Lagrange-multiplier consequence for the actual normalized
entropy and Bernoulli cost. The inputs are an interior, nonconstant
local minimum on a cost level set, not stationarity or a shape claim. -/
theorem level_minimum_stationary {t : ℝ} {u : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hu : ∀ i, u i ∈ Ioo 0 (1/4 : ℝ))
    (hs : 0 < mass u)
    (hnonconstant : ∃ i j, u i ≠ u j)
    (hmin : IsLocalMinOn normalizedEntropy {v | costSum t v = costSum t u} u) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ i, stationary t μ (u i) = logMoment u / mass u := by
  have hu1 : ∀ i, u i ∈ Ioo 0 1 := fun i =>
    ⟨(hu i).1, by linarith only [(hu i).2]⟩
  let C : (ι → ℝ) →L[ℝ] ℝ := weightedSum fun i => deriv (bernoulliCost t) (u i)
  let F : (ι → ℝ) →L[ℝ] ℝ :=
    weightedSum fun i => -(Real.log (u i) - logMoment u / mass u) / mass u
  have hC : C ≠ 0 := by
    intro hc
    have hzero (i : ι) : deriv (bernoulliCost t) (u i) = 0 := by
      have h := congrArg (fun f : (ι → ℝ) →L[ℝ] ℝ => f (Pi.single i 1)) hc
      simpa only [C, weightedSum_single, ContinuousLinearMap.zero_apply] using h
    obtain ⟨i,j,hij⟩ := hnonconstant
    exact hij ((strictMonoOn_deriv_bernoulliCost ht0 ht1).injOn (hu1 i) (hu1 j)
      ((hzero i).trans (hzero j).symm))
  have hextr : IsLocalExtrOn normalizedEntropy {v | costSum t v = costSum t u} u := Or.inl hmin
  obtain ⟨a,b,hab,hEq⟩ :=
    hextr.exists_multipliers_of_hasStrictFDerivAt_1d
        (hasStrictFDerivAt_costSum t u ht0 ht1 hu1)
        (hasStrictFDerivAt_normalizedEntropy u (fun i => (hu i).1) (ne_of_gt hs))
  change a • C + b • F = 0 at hEq
  have hb : b ≠ 0 := by
    intro hb
    have ha : a ≠ 0 := by
      intro ha
      exact hab (by simp [ha,hb])
    have hc : a • C = 0 := by simpa only [hb, zero_smul, add_zero] using hEq
    exact hC ((smul_eq_zero.mp hc).resolve_left ha)
  let μ : ℝ := a * mass u / b
  have hstationary (i : ι) : stationary t μ (u i) = logMoment u / mass u := by
    have hi := congrArg (fun f : (ι → ℝ) →L[ℝ] ℝ => f (Pi.single i 1)) hEq
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply, C,F,weightedSum_single, smul_eq_mul] at hi
    unfold stationary μ
    field_simp [hb,ne_of_gt hs] at hi ⊢
    nlinarith only [hi]
  refine ⟨μ, ?_, hstationary⟩
  obtain ⟨i,j,hij⟩ := hnonconstant
  rcases lt_or_gt_of_ne hij with h | h
  · exact multiplier_pos_of_equal_level ht0 ht1 (hu i) (hu j) h
      ((hstationary i).trans (hstationary j).symm)
  · exact multiplier_pos_of_equal_level ht0 ht1 (hu j) (hu i) h
      ((hstationary j).trans (hstationary i).symm)

/-- Interior local minima on the original Bernoulli sublevel body are
also local minima on the corresponding cost level. Activity of the cost
constraint is not needed for this implication. -/
theorem sublevel_minimum_is_level_minimum {t q : ℝ} {u : ι → ℝ}
    (hu : ∀ i, u i ∈ Ioo 0 1) (hq : costSum t u ≤ q)
    (hmin : IsLocalMinOn normalizedEntropy
      {v | (∀ i, v i ∈ Icc 0 1) ∧ costSum t v ≤ q} u) :
    IsLocalMinOn normalizedEntropy {v | costSum t v = costSum t u} u := by
  have hbox : ∀ᶠ v in 𝓝 u, ∀ i, v i ∈ Ioo 0 1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuous_apply i).continuousAt.eventually
      (Ioo_mem_nhds (hu i).1 (hu i).2)
  change ∀ᶠ v in 𝓝[{v | (∀ i, v i ∈ Icc 0 1) ∧ costSum t v ≤ q}] u,
    normalizedEntropy u ≤ normalizedEntropy v at hmin
  change ∀ᶠ v in 𝓝[{v | costSum t v = costSum t u}] u,
    normalizedEntropy u ≤ normalizedEntropy v
  rw [eventually_nhdsWithin_iff] at hmin ⊢
  filter_upwards [hmin,hbox] with v hv hbox heq
  apply hv
  exact ⟨fun i => ⟨(hbox i).1.le,(hbox i).2.le⟩, heq ▸ hq⟩

/-- The interior part of Lemma C.1: every nonconstant positive-coordinate
local minimum on the Bernoulli body has exactly two coordinate values.
The assumptions refer to the original minimization problem; no
stationarity or two-value hypothesis occurs. -/
theorem interior_minimum_two_values {t q : ℝ} {u : ι → ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hu : ∀ i, u i ∈ Ioo 0 (1/4 : ℝ)) (hs : 0 < mass u)
    (hq : costSum t u ≤ q) (hnonconstant : ∃ i j, u i ≠ u j)
    (hmin : IsLocalMinOn normalizedEntropy
      {v | (∀ i, v i ∈ Icc 0 1) ∧ costSum t v ≤ q} u) :
    ∃ a b : ℝ, a ∈ Ioo 0 (1/4 : ℝ) ∧ b ∈ Ioo 0 (1/4 : ℝ) ∧
      a < b ∧ (∀ i, u i = a ∨ u i = b) ∧
      (∃ i, u i = a) ∧ (∃ i, u i = b) := by
  have hu1 : ∀ i, u i ∈ Ioo 0 1 := fun i =>
    ⟨(hu i).1, by linarith only [(hu i).2]⟩
  obtain ⟨μ,hμ,hstat⟩ := level_minimum_stationary ht0 ht1 hu hs hnonconstant
    (sublevel_minimum_is_level_minimum hu1 hq hmin)
  obtain ⟨a,b,ha,hb,hab,huab,haocc,hbocc,_⟩ :=
    stationary_vector_two_values ht0 ht1 hμ hu
      (fun i j => (hstat i).trans (hstat j).symm) hnonconstant
  exact ⟨a,b,ha,hb,hab,huab,haocc,hbocc⟩

#print axioms hasStrictDerivAt_cost
#print axioms hasStrictFDerivAt_normalizedEntropy
#print axioms level_minimum_stationary
#print axioms normalizedEntropy_eq_shannon
#print axioms sublevel_minimum_is_level_minimum
#print axioms interior_minimum_two_values

end ProjectionChannels.RevisionK182
