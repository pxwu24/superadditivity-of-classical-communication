import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-! Volume packing and quantitative nets on a finite-dimensional sphere. -/
open MeasureTheory Metric Set Module
open scoped ENNReal Function
noncomputable section
namespace StrongConvergence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Disjoint balls give the dimension-sharp packing bound. -/
theorem separated_unit_ball_card_le (s : Finset E) {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ dist x y) :
    (s.card : ℝ) ≤ (1 + 2/ε) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ := ε/2
  let ρ := 1+ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ c ∈ s, ball (c : E) δ
  have hd : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    convert hsep c hc d hd hcd using 1
    dsimp [δ]
    ring
  have ha : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    dsimp [ρ, δ]
    linarith [hs x hx]
  have hi : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        change _ = μ (⋃ c ∈ s, ball (c : E) δ)
        rw [measure_biUnion_finset hd fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono ha
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hj := (ENNReal.mul_le_mul_right (measure_ball_pos μ (0:E) zero_lt_one).ne'
    (measure_ball_lt_top (μ := μ)).ne).mp hi
  have hk := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hj
  have hk' : (s.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using hk
  have hratio : ρ / δ = 1 + 2/ε := by dsimp [ρ,δ]; field_simp; ring
  rw [← hratio, div_pow]
  exact (le_div_iff₀ (pow_pos hδ _)).mpr hk'

/-- For every positive radius there is a sphere net with at most
`(1 + 2/ε)^dim` points. This includes the zero-dimensional empty sphere. -/
theorem exists_sphere_net (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset E,
      (∀ x ∈ s, ‖x‖ = 1) ∧
      (s.card : ℝ) ≤ (1 + 2/ε) ^ finrank ℝ E ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, dist x y < ε := by
  classical
  let B : ℝ := (1+2/ε)^finrank ℝ E
  let P : ℕ → Prop := fun n => ∃ s : Finset E, s.card = n ∧
    (∀ x ∈ s, ‖x‖ = 1) ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ dist x y
  have hp0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  have hbound : ∀ n, P n → n ≤ ⌊B⌋₊ := by
    intro n ⟨s, hcard, hs, hsep⟩
    apply Nat.le_floor
    rw [← hcard]
    exact separated_unit_ball_card_le s hε (fun x hx => (hs x hx).le) hsep
  obtain ⟨s, hcard, hs, hsep⟩ := Nat.findGreatest_spec (Nat.zero_le ⌊B⌋₊) hp0
  refine ⟨s, hs, separated_unit_ball_card_le s hε (fun x hx => (hs x hx).le) hsep, ?_⟩
  intro x hx
  by_contra hn
  push_neg at hn
  have hxs : x ∉ s := by
    intro hxmem
    have h := hn x hxmem
    rw [dist_self] at h
    exact (not_le_of_gt hε) h
  have hinsert : P (s.card+1) := by
    refine ⟨insert x s, Finset.card_insert_of_not_mem hxs, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs y hy
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with hyx | hyS
      · subst y
        rcases Finset.mem_insert.mp hz with hzx | hzS
        · exact (hyz hzx.symm).elim
        · exact hn z hzS
      · rcases Finset.mem_insert.mp hz with hzx | hzS
        · subst z
          simpa only [dist_comm] using hn y hyS
        · exact hsep y hyS z hzS hyz
  have hle := Nat.le_findGreatest (hbound _ hinsert) hinsert
  rw [← hcard] at hle
  omega


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Upper bounds on an `ε`-net control the full operator norm. -/
theorem opNorm_le_of_sphere_net (T : E →L[ℝ] F) (s : Finset E)
    {ε B : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (hB : 0 ≤ B)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, dist x y < ε)
    (hT : ∀ y ∈ s, ‖T y‖ ≤ B) : ‖T‖ ≤ B/(1-ε) := by
  have hb : ‖T‖ ≤ B + ε*‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    have ht := T.le_opNorm (x-y)
    rw [map_sub] at ht
    have he : ‖T‖ * dist x y ≤ ‖T‖ * ε :=
      mul_le_mul_of_nonneg_left hxy.le (norm_nonneg T)
    rw [dist_eq_norm] at he
    have triangle := norm_add_le (T x-T y) (T y)
    simp only [sub_add_cancel] at triangle
    linarith [hT y hy]
  apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
  nlinarith

/-- A lower bound on a sphere net loses at most `ε * ‖T‖`. -/
theorem lower_norm_of_sphere_net (T : E →L[ℝ] F) (s : Finset E)
    {ε A : ℝ}
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, dist x y < ε)
    (hT : ∀ y ∈ s, A ≤ ‖T y‖) (x : E) :
    (A - ε*‖T‖) * ‖x‖ ≤ ‖T x‖ := by
  have hunit : ∀ v : E, ‖v‖ = 1 → A - ε*‖T‖ ≤ ‖T v‖ := by
    intro v hv
    obtain ⟨y, hy, hvy⟩ := hnet v hv
    have ht := T.le_opNorm (v-y)
    rw [map_sub] at ht
    have he : ‖T‖ * dist v y ≤ ‖T‖ * ε :=
      mul_le_mul_of_nonneg_left hvy.le (norm_nonneg T)
    rw [dist_eq_norm] at he
    have triangle := norm_add_le (T y-T v) (T v)
    simp only [sub_add_cancel, norm_sub_rev (T y) (T v)] at triangle
    linarith [hT y hy]
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hb := hunit _ hu
  rwa [map_smul, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
    le_div_iff₀ hn] at hb

#print axioms opNorm_le_of_sphere_net
#print axioms lower_norm_of_sphere_net
#print axioms separated_unit_ball_card_le
#print axioms exists_sphere_net
end StrongConvergence
