import Entropy.OutputSpace

/-! # Compactness and normalization of the concrete spectral body

This module closes the elementary feasible-body hypotheses used by the
output-space support convergence argument. The remaining matrix identifications
and probabilistic compression theorem stay outside its scope.
-/
open Filter Set Finset
open scoped Topology BigOperators

namespace OutputSpaceVerification
open AppendixB

lemma cost_continuous (t : ℝ) : Continuous (ct t) := by
  unfold ct
  fun_prop

lemma body_nonempty {k : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (Dset k t).Nonempty := by
  refine ⟨fun _ => t, ?_⟩
  constructor
  · exact fun _ => ⟨ht, ht1⟩
  · have hz : ct t t = 0 := by simp [ct, mul_comm]
    simp only [hz, sum_const_zero]
    positivity

lemma body_compact (k : ℕ) (t : ℝ) : IsCompact (Dset k t) := by
  have hcube : IsCompact {u : Fin k → ℝ | ∀ i, u i ∈ Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hcost : Continuous (fun u : Fin k → ℝ => ∑ i, ct t (u i)) := by
    apply continuous_finset_sum
    intro i _
    exact (cost_continuous t).comp (continuous_apply i)
  have hclosed : IsClosed {u : Fin k → ℝ | (∑ i, ct t (u i)) ≤ 1 / (k : ℝ)} :=
    isClosed_le hcost continuous_const
  exact hcube.inter_right hclosed

lemma body_mass_pos {k : ℕ} {t : ℝ} (hk : 0 < k) (ht : 0 ≤ t)
    (hthreshold : 1 < (k : ℝ) ^ 2 * t) (u : Fin k → ℝ) (hu : u ∈ Dset k t) :
    0 < ∑ i, u i := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnonneg : 0 ≤ ∑ i, u i := sum_nonneg (fun i _ => (hu.1 i).1)
  by_contra h
  have hzero : ∑ i, u i = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hui : ∀ i, u i = 0 := fun i =>
    (sum_eq_zero_iff_of_nonneg (fun i _ => (hu.1 i).1)).mp hzero i (mem_univ i)
  have hct : ct t 0 = t := by
    simp only [ct, sub_zero, mul_one, mul_zero, Real.sqrt_zero, zero_sub, sub_zero]
    exact Real.sq_sqrt ht
  have hbudget := hu.2
  simp only [hui, hct, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hbudget
  have hmul := (le_div_iff₀ hkpos).mp hbudget
  nlinarith

lemma body_mass_uniformly_positive {k : ℕ} {t : ℝ} (hk : 0 < k) (ht : 0 ≤ t)
    (hthreshold : 1 < (k : ℝ) ^ 2 * t) :
    ∃ m > 0, ∀ u ∈ Dset k t, m ≤ ∑ i, u i := by
  apply (body_compact k t).exists_forall_le'
  · exact (continuous_finset_sum _ (fun i _ => continuous_apply i)).continuousOn
  · exact body_mass_pos hk ht hthreshold

noncomputable def bodySupport (k : ℕ) (t : ℝ) (a : Fin k → ℝ) : ℝ :=
  sSup ((fun u : Fin k → ℝ => ∑ i, a i * u i) '' Dset k t)

noncomputable def normalizedBodySupport (k : ℕ) (t : ℝ) (a : Fin k → ℝ) : ℝ :=
  sSup ((fun u : Fin k → ℝ => (∑ i, a i * u i) / ∑ i, u i) '' Dset k t)

lemma bodySupport_isGreatest {k : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (a : Fin k → ℝ) :
    IsGreatest ((fun u : Fin k → ℝ => ∑ i, a i * u i) '' Dset k t)
      (bodySupport k t a) := by
  have hc : Continuous (fun u : Fin k → ℝ => ∑ i, a i * u i) := by fun_prop
  exact ((body_compact k t).image hc).isGreatest_sSup ((body_nonempty ht ht1).image _)

lemma normalizedBodySupport_isGreatest {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hthreshold : 1 < (k : ℝ) ^ 2 * t)
    (a : Fin k → ℝ) :
    IsGreatest ((fun u : Fin k → ℝ => (∑ i, a i * u i) / ∑ i, u i) '' Dset k t)
      (normalizedBodySupport k t a) := by
  have hnum : Continuous (fun u : Fin k → ℝ => ∑ i, a i * u i) := by fun_prop
  have hden : Continuous (fun u : Fin k → ℝ => ∑ i, u i) := by fun_prop
  have hc := hnum.continuousOn.div hden.continuousOn
    (fun u hu => (body_mass_pos hk ht hthreshold u hu).ne')
  exact ((body_compact k t).image_of_continuousOn hc).isGreatest_sSup
    ((body_nonempty ht ht1).image _)

/-- Concrete scalar version of Step 2 of the output-space theorem: the
random compression limit plus the channel's threshold identity implies
convergence to the support function of the normalized body `Λ_{k,t}`.
The positive marginal gap and both maximum-attainment statements are proved
from `Dset`; they are not extra hypotheses. -/
theorem concrete_normalized_support_tendsto
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hthreshold : 1 < (k : ℝ) ^ 2 * t) (a : Fin k → ℝ)
    (f : ℕ → ℝ → ℝ) (h : ℕ → ℝ)
    (hcut : ∀ n z, h n ≤ z ↔ f n z ≤ 0)
    (hconv : ∀ z, Tendsto (fun n => f n z) atTop
      (𝓝 (bodySupport k t (fun i => a i - z)))) :
    Tendsto h atTop (𝓝 (normalizedBodySupport k t a)) := by
  obtain ⟨m, hm, hmass⟩ := body_mass_uniformly_positive hk ht hthreshold
  apply normalized_support_tendsto (Dset k t) (fun u => ∑ i, a i * u i)
    (fun u => ∑ i, u i) f (fun z => bodySupport k t (fun i => a i - z)) h
    (normalizedBodySupport k t a) m hm hmass
    (normalizedBodySupport_isGreatest hk ht ht1 hthreshold a) _ hcut hconv
  intro z
  convert bodySupport_isGreatest ht ht1 (fun i => a i - z) using 1
  funext u
  simp only [sub_mul, sum_sub_distrib, mul_sum]

end OutputSpaceVerification
