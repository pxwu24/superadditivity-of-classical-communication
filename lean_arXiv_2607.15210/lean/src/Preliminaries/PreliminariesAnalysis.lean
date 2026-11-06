import Preliminaries.PreliminariesLegendre
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Deterministic analysis for the preliminaries

This file proves the extension from a dense set of parameters to all
parameters and the elementary Legendre bound used in the appendix.
The free-probability convergence theorems themselves are not formalized here.
-/

open Filter Finset
open scoped Topology BigOperators

namespace ProjectionChannels

/-- A common Lipschitz estimate extends convergence from an approximating
set to the whole parameter space. This is the deterministic part of the simultaneous
almost-sure convergence argument. -/
theorem convergence_of_dense_lipschitz
    {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hdense : Dense s)
    (hf : ∀ n x y, dist (f n x) (f n y) ≤ dist x y)
    (hg : ∀ x y, dist (g x) (g y) ≤ dist x y)
    (hconv : ∀ q ∈ s, Tendsto (fun n => f n q) atTop (𝓝 (g q)))
    (x : X) : Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨q, hqs, hq⟩ := hdense.exists_dist_lt x (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv q hqs) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hmiddle := hN n hn
  have hleft := hf n x q
  have hright := hg q x
  have hqx : dist q x < ε / 3 := by simpa [dist_comm] using hq
  calc
    dist (f n x) (g x) ≤ dist (f n x) (f n q) + dist (f n q) (g x) :=
      dist_triangle _ _ _
    _ ≤ dist (f n x) (f n q) + (dist (f n q) (g q) + dist (g q) (g x)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε := by linarith

/-- Countably many almost-sure limits on a dense set give a single
probability-one event on which convergence holds for every parameter.
No measurability of the parameter map is needed for this argument. -/
theorem ae_simultaneous_convergence_of_dense_lipschitz
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (μ : MeasureTheory.Measure Ω) (s : Set X)
    (f : Ω → ℕ → X → ℝ) (g : X → ℝ)
    (hcount : s.Countable) (hdense : Dense s)
    (hf : ∀ ω n x y, dist (f ω n x) (f ω n y) ≤ dist x y)
    (hg : ∀ x y, dist (g x) (g y) ≤ dist x y)
    (hconv : ∀ q ∈ s, ∀ᵐ ω ∂μ,
      Tendsto (fun n => f ω n q) atTop (𝓝 (g q))) :
    ∀ᵐ ω ∂μ, ∀ x, Tendsto (fun n => f ω n x) atTop (𝓝 (g x)) := by
  letI : Countable s := hcount.to_subtype
  have hsim : ∀ᵐ ω ∂μ, ∀ q : s,
      Tendsto (fun n => f ω n q) atTop (𝓝 (g q)) :=
    MeasureTheory.ae_all_iff.2 (fun q => hconv q q.property)
  filter_upwards [hsim] with ω hω
  intro x
  exact convergence_of_dense_lipschitz s (f ω) g hdense (hf ω) hg
    (fun q hq => hω ⟨q, hq⟩) x

/-- The finite-dimensional weak-duality estimate in Step 3 of the
Bernoulli spectral-edge proof. -/
theorem bernoulli_support_upper_bound
    {ι : Type*} [Fintype ι]
    (t k w : ℝ) (a u : ι → ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hk : 0 < k) (hw : 0 < w)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hbudget : ∑ i, bernoulliCost t (u i) ≤ 1 / k) :
    ∑ i, a i * u i ≤
      (1 + k * ∑ i, bernoulliDual t (a i * w / k)) / w := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => bernoulli_legendre_inequality ht0 ht1 (hu0 i) (hu1 i) (a i * w / k))
  have hfactor : (∑ i, (a i * w / k) * u i) =
      (w / k) * ∑ i, a i * u i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_sub_distrib, hfactor] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum (le_of_lt hk)
  have hidentity : k * ((w / k) * (∑ i, a i * u i) -
      ∑ i, bernoulliCost t (u i)) =
      w * (∑ i, a i * u i) - k * ∑ i, bernoulliCost t (u i) := by
    field_simp [ne_of_gt hk]
  rw [hidentity] at hscaled
  have hbudget' := (le_div_iff₀ hk).mp hbudget
  apply (le_div_iff₀ hw).2
  nlinarith

/-- The feasible region used for the support function. -/
def bernoulliFeasible {ι : Type*} [Fintype ι] (t k : ℝ) : Set (ι → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ (∀ i, u i ≤ 1) ∧
    (∑ i, bernoulliCost t (u i)) ≤ 1 / k}

/-- When the explicit scalar maximizers saturate the constraint, they
attain the finite-dimensional support bound. This is Step 4 in the
finite-critical-point case, with the saturation condition explicit. -/
theorem bernoulli_support_attainment
    {ι : Type*} [Fintype ι]
    (t k w : ℝ) (a : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) (hw : 0 < w)
    (hsat : ∑ i, bernoulliCost t (bernoulliMaximizer t (a i * w / k)) = 1 / k) :
    IsGreatest
      ((fun u : ι → ℝ => ∑ i, a i * u i) '' bernoulliFeasible t k)
      ((1 + k * ∑ i, bernoulliDual t (a i * w / k)) / w) := by
  let u : ι → ℝ := fun i => bernoulliMaximizer t (a i * w / k)
  have hu0 : ∀ i, 0 ≤ u i :=
    fun i => (bernoulliMaximizer_mem_Ioo ht0 ht1 (a i * w / k)).1.le
  have hu1 : ∀ i, u i ≤ 1 :=
    fun i => (bernoulliMaximizer_mem_Ioo ht0 ht1 (a i * w / k)).2.le
  have hcost : ∑ i, bernoulliCost t (u i) = 1 / k := hsat
  have hsum : (∑ i, ((a i * w / k) * u i - bernoulliCost t (u i))) =
      ∑ i, bernoulliDual t (a i * w / k) := by
    apply Finset.sum_congr rfl
    intro i _
    exact bernoulli_legendre_equality ht0 ht1 (a i * w / k)
  have hfactor : (∑ i, (a i * w / k) * u i) =
      (w / k) * ∑ i, a i * u i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_sub_distrib, hfactor, hcost] at hsum
  have hscaled := congrArg (fun z : ℝ => k * z) hsum
  dsimp only at hscaled
  have hidentity : k * ((w / k) * (∑ i, a i * u i) - 1 / k) =
      w * (∑ i, a i * u i) - 1 := by
    field_simp [ne_of_gt hk]
  rw [hidentity] at hscaled
  have hvalue : (∑ i, a i * u i) =
      (1 + k * ∑ i, bernoulliDual t (a i * w / k)) / w := by
    apply (eq_div_iff (ne_of_gt hw)).2
    nlinarith
  constructor
  · exact ⟨u, ⟨hu0, hu1, hcost.le⟩, hvalue⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact bernoulli_support_upper_bound t k w a v ht0.le ht1.le hk hw
      hv.1 hv.2.1 hv.2.2

/-- Coordinatewise maximizer of the linear objective on the cube; a zero
coefficient is assigned t, the zero-cost point. -/
noncomputable def bernoulliEndpoint (t a : ℝ) : ℝ :=
  if 0 < a then 1 else if a < 0 then 0 else t

/-- If the coordinatewise cube maximizer is feasible, the support value
is the sum of the positive coefficients. This proves attainment in the
endpoint regime without any random-matrix assumptions. -/
theorem bernoulli_endpoint_support
    {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hbudget : ∑ i, bernoulliCost t (bernoulliEndpoint t (a i)) ≤ 1 / k) :
    IsGreatest
      ((fun u : ι → ℝ => ∑ i, a i * u i) '' bernoulliFeasible t k)
      (∑ i, max (a i) 0) := by
  have hu0 : ∀ i, 0 ≤ bernoulliEndpoint t (a i) := by
    intro i
    unfold bernoulliEndpoint
    split_ifs <;> linarith
  have hu1 : ∀ i, bernoulliEndpoint t (a i) ≤ 1 := by
    intro i
    unfold bernoulliEndpoint
    split_ifs <;> linarith
  have hvalue : (∑ i, a i * bernoulliEndpoint t (a i)) = ∑ i, max (a i) 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : 0 < a i
    · simp [bernoulliEndpoint, hp, max_eq_left hp.le]
    · by_cases hn : a i < 0
      · simp [bernoulliEndpoint, hp, hn, max_eq_right hn.le]
      · have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
        simp [hz]
  constructor
  · exact ⟨(fun i => bernoulliEndpoint t (a i)), ⟨hu0, hu1, hbudget⟩, hvalue⟩
  · rintro _ ⟨v, hv, rfl⟩
    apply Finset.sum_le_sum
    intro i _
    by_cases ha : 0 ≤ a i
    · rw [max_eq_left ha]
      exact mul_le_of_le_one_right ha (hv.2.1 i)
    · rw [max_eq_right (le_of_not_ge ha)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) (hv.1 i)

end ProjectionChannels

