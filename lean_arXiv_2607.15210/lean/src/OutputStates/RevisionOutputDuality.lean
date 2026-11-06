import Entropy.OutputSpace
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.NormedSpace.OperatorNorm.NNNorm
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Support functions and Hausdorff distance

The support characterization and the support/Hausdorff duality are proved
for arbitrary real normed proper spaces. No separation, minimax, or duality
formula is an additional hypothesis. `hausdorffDist_eq_supportDistance` is
the normed-space statement underlying Lemma III.3. Its exact trace/operator
norm specialization is proved in `RevisionOutputHausdorff.lean`.
-/

open Set Metric
open scoped Pointwise Topology
set_option maxHeartbeats 500000
namespace RevisionOutput
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Support function in the continuous real dual. -/
def support (K : Set E) (f : E →L[ℝ] ℝ) : ℝ := sSup (f '' K)

lemma support_isGreatest {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →L[ℝ] ℝ) : IsGreatest (f '' K) (support K f) :=
  (hK.image f.continuous).isGreatest_sSup (hne.image f)

lemma le_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →L[ℝ] ℝ) {x : E} (hx : x ∈ K) : f x ≤ support K f :=
  (support_isGreatest hK hne f).2 ⟨x, hx, rfl⟩

/-- A compact convex set is exactly the intersection of its supporting
half-spaces. -/
theorem mem_iff_le_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) (x : E) :
    x ∈ K ↔ ∀ f : E →L[ℝ] ℝ, f x ≤ support K f := by
  constructor
  · exact fun hx f => le_support hK hne f hx
  · intro hx
    by_contra hnot
    obtain ⟨f, u, huK, hux⟩ := geometric_hahn_banach_closed_point hconv hK.isClosed hnot
    obtain ⟨y, hy, hyf⟩ := (support_isGreatest hK hne f).1
    have h := huK y hy
    have hx' := hx f
    rw [← hyf] at hx'
    linarith

/-- Equality of support functions implies equality of nonempty compact
convex sets. -/
theorem eq_of_support_eq {C K : Set E} (hC : IsCompact C) (hK : IsCompact K)
    (hneC : C.Nonempty) (hneK : K.Nonempty) (hcC : Convex ℝ C) (hcK : Convex ℝ K)
    (h : ∀ f : E →L[ℝ] ℝ, support C f = support K f) : C = K := by
  ext x
  rw [mem_iff_le_support hC hneC hcC, mem_iff_le_support hK hneK hcK]
  simp only [h]

variable [ProperSpace E]

/-- A real continuous functional attains its positive operator norm on
the closed unit ball. This includes the zero functional. -/
lemma exists_unit_norming (f : E →L[ℝ] ℝ) :
    ∃ v : E, ‖v‖ ≤ 1 ∧ f v = ‖f‖ := by
  have hc := (isCompact_closedBall (0 : E) 1).image (f.continuous.norm)
  have hn : (closedBall (0 : E) 1).Nonempty := nonempty_closedBall.mpr zero_le_one
  have hg := hc.isGreatest_sSup (hn.image (fun x => ‖f x‖))
  rw [f.sSup_unitClosedBall_eq_norm] at hg
  obtain ⟨v, hv, heq⟩ := hg.1
  by_cases hvf : 0 ≤ f v
  · exact ⟨v, mem_closedBall_zero_iff.mp hv, by simpa [Real.norm_eq_abs, abs_of_nonneg hvf] using heq⟩
  · refine ⟨-v, by simpa using mem_closedBall_zero_iff.mp hv, ?_⟩
    simpa [Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hvf)] using heq

/-- The support inequalities with an additive radius imply membership
in the closed radius-neighborhood. The separating functional and its
normalization are constructed in the proof. -/
lemma mem_add_closedBall_of_support_le {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hc : Convex ℝ K) {r : ℝ} (hr : 0 ≤ r) (x : E)
    (h : ∀ f : E →L[ℝ] ℝ, ‖f‖ ≤ 1 → f x ≤ support K f + r) :
    x ∈ K + closedBall 0 r := by
  by_contra hx
  have hc' := hc.add (convex_closedBall (0 : E) r)
  have hk' := hK.add (isCompact_closedBall (0 : E) r)
  obtain ⟨f, u, hfK, hfx⟩ := geometric_hahn_banach_closed_point hc' hk'.isClosed hx
  obtain ⟨a, ha⟩ := hne
  have hfa : f a < u := by
    exact hfK a ⟨a, ha, 0, mem_closedBall_self hr, add_zero a⟩
  have hfne : f ≠ 0 := by
    intro he
    simp only [he, ContinuousLinearMap.zero_apply] at hfa hfx
    linarith
  have hfn : 0 < ‖f‖ := norm_pos_iff.mpr hfne
  let g : E →L[ℝ] ℝ := ‖f‖⁻¹ • f
  have hgn : ‖g‖ ≤ 1 := by
    calc
      ‖g‖ ≤ ‖‖f‖⁻¹‖ * ‖f‖ := ContinuousLinearMap.opNorm_smul_le (‖f‖⁻¹) f
      _ = 1 := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfn), inv_mul_cancel₀ hfn.ne']
  obtain ⟨b, hb, hbg⟩ := (support_isGreatest hK ⟨a, ha⟩ g).1
  have hh := h g hgn
  rw [← hbg] at hh
  change ‖f‖⁻¹ * f x ≤ ‖f‖⁻¹ * f b + r at hh
  have hmul := mul_le_mul_of_nonneg_left hh hfn.le
  have hbound : f x ≤ f b + r * ‖f‖ := by
    field_simp at hmul
    nlinarith only [hmul]
  obtain ⟨v, hv, hvf⟩ := exists_unit_norming f
  have hrv : r • v ∈ closedBall (0 : E) r := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left hv hr).trans_eq (mul_one r)
  have hsep := hfK (b + r • v) ⟨b, hb, r • v, hrv, rfl⟩
  rw [map_add, map_smul, hvf, smul_eq_mul] at hsep
  linarith

/-- Uniform support-function errors bound the Hausdorff distance. -/
theorem hausdorffDist_le_of_support_le {C K : Set E}
    (hC : IsCompact C) (hK : IsCompact K) (hneC : C.Nonempty) (hneK : K.Nonempty)
    (hcC : Convex ℝ C) (hcK : Convex ℝ K) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ f : E →L[ℝ] ℝ, ‖f‖ ≤ 1 → |support C f - support K f| ≤ r) :
    hausdorffDist C K ≤ r := by
  apply hausdorffDist_le_of_mem_dist hr
  · intro x hx
    have hm := mem_add_closedBall_of_support_le hK hneK hcK hr x (by
      intro f hf
      have hh := (abs_le.mp (h f hf)).2
      have hx' := le_support hC hneC f hx
      linarith)
    obtain ⟨y, hy, z, hz, hyz⟩ := hm
    refine ⟨y, hy, ?_⟩
    rw [← hyz, dist_eq_norm, add_sub_cancel_left]
    exact mem_closedBall_zero_iff.mp hz
  · intro y hy
    have hm := mem_add_closedBall_of_support_le hC hneC hcC hr y (by
      intro f hf
      have hh := (abs_le.mp (h f hf)).1
      have hy' := le_support hK hneK f hy
      linarith)
    obtain ⟨x, hx, z, hz, hxz⟩ := hm
    refine ⟨x, hx, ?_⟩
    rw [← hxz, dist_eq_norm, add_sub_cancel_left]
    exact mem_closedBall_zero_iff.mp hz

/-- The reverse bound needs only compactness, not convexity. -/
lemma support_sub_le_hausdorffDist {C K : Set E} (hC : IsCompact C)
    (hK : IsCompact K) (hneC : C.Nonempty) (hneK : K.Nonempty)
    (f : E →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) :
    support C f - support K f ≤ hausdorffDist C K := by
  obtain ⟨x, hx, hxf⟩ := (support_isGreatest hC hneC f).1
  obtain ⟨y, hy, hxy⟩ := hK.exists_infDist_eq_dist hneK x
  have hfin := hausdorffEdist_ne_top_of_nonempty_of_bounded hneC hneK hC.isBounded hK.isBounded
  have hd := infDist_le_hausdorffDist_of_mem hx hfin
  rw [hxy] at hd
  have hb := le_support hK hneK f hy
  have hn := f.le_opNorm (x - y)
  have hn' : f x - f y ≤ dist x y := by
    have hle : f (x - y) ≤ ‖f (x - y)‖ := le_abs_self _
    have hmult := mul_le_mul_of_nonneg_right hf (norm_nonneg (x - y))
    rw [map_sub] at hle hn
    rw [dist_eq_norm]
    linarith
  rw [← hxf]
  linarith

lemma abs_support_sub_le_hausdorffDist {C K : Set E} (hC : IsCompact C)
    (hK : IsCompact K) (hneC : C.Nonempty) (hneK : K.Nonempty)
    (f : E →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) :
    |support C f - support K f| ≤ hausdorffDist C K := by
  have hu := support_sub_le_hausdorffDist hC hK hneC hneK f hf
  have hl := support_sub_le_hausdorffDist hK hC hneK hneC f hf
  rw [hausdorffDist_comm] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- The actual supremum of support-function differences over the dual
unit ball. -/
def supportDistance (C K : Set E) : ℝ :=
  sSup ((fun f : E →L[ℝ] ℝ => |support C f - support K f|) '' closedBall 0 1)

/-- Hausdorff/support duality, with both sides defined as their genuine
suprema. No duality identity is assumed. -/
theorem hausdorffDist_eq_supportDistance {C K : Set E}
    (hC : IsCompact C) (hK : IsCompact K) (hneC : C.Nonempty) (hneK : K.Nonempty)
    (hcC : Convex ℝ C) (hcK : Convex ℝ K) :
    hausdorffDist C K = supportDistance C K := by
  let S := (fun f : E →L[ℝ] ℝ => |support C f - support K f|) '' closedBall 0 1
  have hneS : S.Nonempty := (nonempty_closedBall.mpr zero_le_one).image _
  have hbdd : BddAbove S := ⟨hausdorffDist C K, by
    rintro _ ⟨f, hf, rfl⟩
    exact abs_support_sub_le_hausdorffDist hC hK hneC hneK f (mem_closedBall_zero_iff.mp hf)⟩
  have hnonneg : 0 ≤ supportDistance C K := by
    obtain ⟨x, hx⟩ := hneS
    have hxn : 0 ≤ x := by
      obtain ⟨f, hf, rfl⟩ := hx
      exact abs_nonneg _
    exact hxn.trans (le_csSup hbdd hx)
  apply le_antisymm
  · apply hausdorffDist_le_of_support_le hC hK hneC hneK hcC hcK hnonneg
    intro f hf
    exact le_csSup hbdd ⟨f, mem_closedBall_zero_iff.mpr hf, rfl⟩
  · apply csSup_le hneS
    rintro _ ⟨f, hf, rfl⟩
    exact abs_support_sub_le_hausdorffDist hC hK hneC hneK f (mem_closedBall_zero_iff.mp hf)

end
end RevisionOutput
