import Entropy.Infimum
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Real Finset Set
noncomputable section
namespace AppendixB

lemma continuous_ct (t : ℝ) : Continuous (ct t) := by
  unfold ct
  fun_prop

lemma isCompact_Dset (k : ℕ) (t : ℝ) : IsCompact (Dset k t) := by
  have heq : Dset k t = Icc (fun _ => 0) (fun _ => 1) ∩
      {u : Fin k → ℝ | (∑ i, ct t (u i)) ≤ 1 / (k : ℝ)} := by
    ext u
    simp only [Dset, mem_setOf_eq, mem_inter_iff, Set.mem_Icc, Pi.le_def]
    aesop
  rw [heq]
  exact isCompact_Icc.inter_right (isClosed_le (by exact continuous_finset_sum _ (fun i _ => (continuous_ct t).comp (continuous_apply i))) continuous_const)

lemma Dset_sum_pos {k : ℕ} {t : ℝ} (hk : 0 < k) (ht : 0 ≤ t)
    (hkt : 1 < (k : ℝ) ^ 2 * t) {u : Fin k → ℝ} (hu : u ∈ Dset k t) :
    0 < ∑ i, u i := by
  have hnonneg : 0 ≤ ∑ i, u i := sum_nonneg (fun i _ => (hu.1 i).1)
  by_contra hpos
  have hzero : ∑ i, u i = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
  have hui : ∀ i, u i = 0 := by
    have h := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (univ : Finset (Fin k))) => (hu.1 i).1)).mp hzero
    exact fun i => h i (mem_univ i)
  have hct0 : ct t 0 = t := by simp [ct, Real.sq_sqrt ht]
  have hcost : (k : ℝ) * t ≤ 1 / (k : ℝ) := by
    simpa only [hui, hct0, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using hu.2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hc := (le_div_iff₀ hkpos).mp hcost
  nlinarith only [hc, hkt]

lemma isCompact_Lam {k : ℕ} {t : ℝ} (hk : 0 < k) (ht : 0 ≤ t)
    (hkt : 1 < (k : ℝ) ^ 2 * t) : IsCompact (Lam k t) := by
  have heq : Lam k t = (fun u : Fin k → ℝ => fun i => u i / ∑ j, u j) '' Dset k t := by
    ext q
    simp only [Lam, mem_setOf_eq, mem_image]
    aesop
  rw [heq]
  apply (isCompact_Dset k t).image_of_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact (continuous_apply i).continuousOn.div (by fun_prop)
    (fun u hu => ne_of_gt (Dset_sum_pos hk ht hkt hu))

lemma continuousAt_renyi_positive {α ι : Type*} [TopologicalSpace α]
    (p : ℝ) (s : Finset ι) (hs : s.Nonempty) (f : α → ι → ℝ) (x : α)
    (hf : ∀ i ∈ s, ContinuousAt (fun y => f y i) x)
    (hpos : ∀ i ∈ s, 0 < f x i) :
    ContinuousAt (fun y => renyi p s (fun _ => 1) (f y)) x := by
  unfold renyi
  by_cases hp : p = 1
  · simp only [hp, if_pos, one_mul]
    apply ContinuousAt.neg
    exact tendsto_finset_sum _ (fun i hi => (hf i hi).mul ((hf i hi).log (ne_of_gt (hpos i hi))))
  · simp only [hp, if_false, one_mul]
    have hc : ContinuousAt (fun y => ∑ i ∈ s, f y i ^ p) x :=
      tendsto_finset_sum _ (fun i hi => (hf i hi).rpow_const (Or.inl (ne_of_gt (hpos i hi))))
    have hv : 0 < ∑ i ∈ s, f x i ^ p := sum_pos (fun i hi => Real.rpow_pos_of_pos (hpos i hi) p) hs
    exact (hc.log (ne_of_gt hv)).div_const (1 - p)

lemma shuffle_pos {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    {q : Fin k → ℝ} (hq : ∀ i, 0 < q i) {I : Finset (Fin k)}
    (hI : I ∈ subsets k r) : 0 < shuffle k r q I := by
  have hcard : I.card = r := (Finset.mem_powersetCard.mp hI).2
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hN : 0 < (Nat.choose (k - 1) (r - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : r - 1 ≤ k - 1)
  exact div_pos (sum_pos (fun i _ => hq i) hne) hN

lemma continuousAt_shuffled_entropy {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    (p : ℝ) {q : Fin k → ℝ} (hq : ∀ i, 0 < q i) :
    ContinuousAt (fun q => renyi p (subsets k r) (fun _ => 1) (shuffle k r q)) q := by
  have hs : (subsets k r).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_subsets]
    exact Nat.choose_pos hrk
  apply continuousAt_renyi_positive p (subsets k r) hs (shuffle k r) q
  · intro I _
    unfold shuffle
    fun_prop
  · exact fun I hI => shuffle_pos hr hrk hq hI

lemma Lam_nonempty {k : ℕ} {t : ℝ} (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Lam k t).Nonempty := by
  refine ⟨(fun i => (fun _ : Fin k => t) i / ∑ j : Fin k, t), (fun _ => t), ?_, rfl⟩
  refine ⟨fun _ => ⟨ht0, ht1⟩, ?_⟩
  have hzero : ct t t = 0 := by simp [ct, mul_comm]
  simp only [hzero, sum_const_zero]
  positivity

/-- At positive normalized spectra the compact feasible body attains the entropy minimum. -/
theorem shuffled_entropy_attains_minimum {k r : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hkt : 1 < (k : ℝ)^2*t)
    (hr : 1 ≤ r) (hrk : r ≤ k) (p : ℝ)
    (hpos : ∀ q ∈ Lam k t, ∀ i, 0 < q i) :
    ∃ q ∈ Lam k t, ∀ q' ∈ Lam k t,
      renyi p (subsets k r) (fun _ => 1) (shuffle k r q) ≤
        renyi p (subsets k r) (fun _ => 1) (shuffle k r q') := by
  exact (isCompact_Lam hk ht0 hkt).exists_isMinOn (Lam_nonempty hk ht0 ht1)
    (fun q hq => (continuousAt_shuffled_entropy hr hrk p (hpos q hq)).continuousWithinAt)

/-- For every fixed body parameter and exterior power, the minimum exists for all
sufficiently large dimensions. This removes the infimum/minimum distinction in
the large-dimension single-output statements. -/
theorem shuffled_entropy_eventually_attains_minimum {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (p : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∃ k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      ∃ q ∈ Lam k t, ∀ q' ∈ Lam k t,
        renyi p (subsets k r) (fun _ => 1) (shuffle k r q) ≤
          renyi p (subsets k r) (fun _ => 1) (shuffle k r q') := by
  obtain ⟨C, kL, hC, hloc⟩ := localization ht0 ht1
  refine ⟨max kL (max (r : ℝ) (max 2 (max (2 / t) ((C + 1)^2)))), fun k hk => ?_⟩
  have hkL : kL ≤ (k : ℝ) := (le_max_left _ _).trans hk
  have hkrest := (le_max_right _ _).trans hk
  have hrkR : (r : ℝ) ≤ k := (le_max_left _ _).trans hkrest
  have hkrest2 := (le_max_right _ _).trans hkrest
  have hk2 : (2 : ℝ) ≤ k := (le_max_left _ _).trans hkrest2
  have hkrest3 := (le_max_right _ _).trans hkrest2
  have hktwo : 2 / t ≤ (k : ℝ) := (le_max_left _ _).trans hkrest3
  have hkC : (C+1)^2 ≤ (k : ℝ) := (le_max_right _ _).trans hkrest3
  have hkpos : (0 : ℝ) < k := by linarith only [hk2]
  have hkt0 : 2 ≤ (k : ℝ)*t := (div_le_iff₀ ht0).mp hktwo
  have hkt : 1 < (k : ℝ)^2*t := by
    have h := mul_le_mul_of_nonneg_left hkt0 hkpos.le
    nlinarith only [h, hk2]
  apply shuffled_entropy_attains_minimum (by exact_mod_cast hkpos) ht0.le ht1.le hkt hr
    (by exact_mod_cast hrkR) p
  intro q hq i
  have he := (hloc k hkL q hq).2.2.1 i
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  have hs2 : Real.sqrt (k : ℝ)^2 = k := Real.sq_sqrt hkpos.le
  have hCs : C < Real.sqrt (k : ℝ) := by
    nlinarith only [hC, hkC, hs2, hs]
  have hfrac : C / Real.sqrt (k : ℝ) < 1 := (div_lt_one hs).mpr hCs
  have hlow := (abs_le.mp he).1
  nlinarith only [hlow, hfrac, hkpos]

/-- The paper's minimum version of the single-output asymptotics, with an attained
minimum and an explicit O(k^(-5/2)) error. Its objects are the concrete spectra. -/
theorem single_output_minimum {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      ∃ q ∈ Lam k t,
        (∀ q' ∈ Lam k t,
          renyi p (subsets k r) (fun _ => 1) (shuffle k r q) ≤
            renyi p (subsets k r) (fun _ => 1) (shuffle k r q')) ∧
        |renyi p (subsets k r) (fun _ => 1) (shuffle k r q) -
          (Real.log (Nat.choose k r) - 2*p*(1-t)/(t*r*k^2))| ≤
          C/(k^2*Real.sqrt k) := by
  obtain ⟨C, hC, k₁, hbound⟩ := single_output_infimum ht0 ht1 hp r hr
  obtain ⟨k₂, hmin⟩ := shuffled_entropy_eventually_attains_minimum ht0 ht1 p r hr
  refine ⟨C, hC, max k₁ k₂, fun k hk => ?_⟩
  obtain ⟨q, hq, hminimal⟩ := hmin k ((le_max_right _ _).trans hk)
  refine ⟨q, hq, hminimal, ?_⟩
  have heq : infimumOutputEntropy p t k r =
      renyi p (subsets k r) (fun _ => 1) (shuffle k r q) := by
    let v := renyi p (subsets k r) (fun _ => 1) (shuffle k r q)
    have hv : v ∈ outputEntropyValues p t k r := ⟨q, hq, rfl⟩
    have hl : ∀ x ∈ outputEntropyValues p t k r, v ≤ x := by
      rintro x ⟨q', hq', rfl⟩
      exact hminimal q' hq'
    exact le_antisymm (csInf_le ⟨v, hl⟩ hv) (le_csInf ⟨v, hv⟩ hl)
  simpa only [heq] using hbound k ((le_max_left _ _).trans hk)

/-- The r = 1 specialization, stated directly for the original probability list. -/
theorem single_output_r1_minimum {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      ∃ q ∈ Lam k t,
        (∀ q' ∈ Lam k t,
          renyi p Finset.univ (fun _ => 1) q ≤ renyi p Finset.univ (fun _ => 1) q') ∧
        |renyi p Finset.univ (fun _ => 1) q -
          (Real.log k - 2*p*(1-t)/(t*k^2))| ≤ C/(k^2*Real.sqrt k) := by
  simpa only [renyi_r1, Nat.choose_one_right, Nat.cast_one, mul_one]
    using single_output_minimum ht0 ht1 hp 1 le_rfl

end AppendixB
end
