import RandomCompression.CauchyBernoulli
import RandomCompression.BernoulliDuality
import RandomCompression.SpectralEdge
import Mathlib.MeasureTheory.Function.EssSup

/-!
# The Bernoulli law and the inverse-Cauchy germ used by free convolution

All transforms in this file are integrals against actual measures. The
finite-sum free-convolution law is specified by its usual additive R-transform
germ, not by any spectral-edge or support-function formula. Existence of the
limiting law and strong convergence to it belong to the block-modification
input; this file does not postulate either as a new axiom.
-/

open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels

/-- The removable value at zero is the mean of the Bernoulli law. -/
def bernoulliR (t w : ℝ) : ℝ :=
  if w = 0 then t else bernoulliDual t w / w

lemma bernoulliDual_quadratic {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (w : ℝ) :
    bernoulliDual t w ^ 2 + (1-w)*bernoulliDual t w - t*w = 0 := by
  have hd := bernoulliDelta_sq ht0 ht1 w
  unfold bernoulliDual
  nlinarith

lemma bernoulliDual_eq_of_quadratic {t w g : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hg : g^2 + (1-w)*g - t*w = 0) (hbranch : 0 ≤ 2*g-w+1) :
    bernoulliDual t w = g := by
  have hd := bernoulliDelta_sq ht0 ht1 w
  have hd0 : 0 ≤ bernoulliDelta t w := Real.sqrt_nonneg _
  have heq : bernoulliDelta t w = 2*g-w+1 := by
    nlinarith [sq_nonneg (bernoulliDelta t w - (2*g-w+1))]
  unfold bernoulliDual
  rw [heq]
  ring

lemma bernoulliR_mul (t w : ℝ) : w * bernoulliR t w = bernoulliDual t w := by
  by_cases hw : w = 0
  · subst w
    have hd : bernoulliDelta t 0 = 1 := by
      unfold bernoulliDelta
      rw [show (0 + 2*t-1)^2+4*t*(1-t) = 1 by ring, Real.sqrt_one]
    simp [bernoulliR, bernoulliDual, hd]
  · simp [bernoulliR, hw, mul_div_cancel₀ _ hw]

/-- The real transform follows from the already proved atomic Bochner integral. -/
theorem realCauchyTransform_bernoulli {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : ℝ) :
    realCauchyTransform (bernoulliMeasure t) x = (1-t)/x + t/(x-1) := by
  have h := cauchyTransform_bernoulli ht0 ht1 (x : ℂ)
  rw [cauchyTransform_ofReal] at h
  exact_mod_cast h

/-- Dilation, including the zero dilation, evaluated as an actual measure map. -/
theorem realCauchyTransform_dilated_bernoulli {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c x : ℝ) :
    realCauchyTransform (Measure.map (fun y : ℝ => c*y) (bernoulliMeasure t)) x =
      (1-t)/x + t/(x-c) := by
  have heq : cauchyTransform (Measure.map (fun y : ℝ => c*y) (bernoulliMeasure t)) (x : ℂ) =
      ((1-t)/x + t/(x-c) : ℝ) := by
    unfold cauchyTransform
    have hm : StronglyMeasurable (fun y : ℝ => ((x : ℂ) - (y : ℂ))⁻¹) :=
      (show Measurable (fun y : ℝ => ((x : ℂ) - (y : ℂ))⁻¹) by fun_prop).stronglyMeasurable
    rw [integral_map_of_stronglyMeasurable (by fun_prop) hm,
      integral_bernoulliMeasure ht0 ht1]
    simp [Complex.real_smul, div_eq_mul_inv]
  rw [cauchyTransform_ofReal] at heq
  exact_mod_cast heq

/-- The R-transform scaling law for every real dilation, proved directly
from the two-point probability measure. This is an actual inverse identity
at every point to the right of both atoms, not an assumed inversion formula. -/
theorem dilated_bernoulli_inverse_right {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (c x : ℝ) (hx0 : 0 < x) (hxc : c < x) :
    let w := realCauchyTransform
      (Measure.map (fun y : ℝ => c*y) (bernoulliMeasure t)) x
    w⁻¹ + c * bernoulliR t (c*w) = x := by
  dsimp
  rw [realCauchyTransform_dilated_bernoulli ht0.le ht1.le]
  let w : ℝ := (1-t)/x + t/(x-c)
  change w⁻¹ + c * bernoulliR t (c*w) = x
  have hx : x ≠ 0 := ne_of_gt hx0
  have hxc0 : 0 < x-c := sub_pos.mpr hxc
  have hxcne : x-c ≠ 0 := ne_of_gt hxc0
  have hw : 0 < w := add_pos (div_pos (sub_pos.mpr ht1) hx0) (div_pos ht0 hxc0)
  have hwid : w*x*(x-c) = x - (1-t)*c := by
    dsimp [w]
    field_simp
    <;> ring
  have hg : (w*x-1)^2 + (1-c*w)*(w*x-1) - t*(c*w) = 0 := by
    calc
      _ = w * (w*x*(x-c) - (x-(1-t)*c)) := by ring
      _ = 0 := by rw [hwid]; ring
  have hb : 0 < 2*(w*x-1)-c*w+1 := by
    have hid : 2*(w*x-1)-c*w+1 =
        (1-t)*(x-c)/x + t*x/(x-c) := by
      dsimp [w]
      field_simp
      <;> ring
    rw [hid]
    exact add_pos (div_pos (mul_pos (sub_pos.mpr ht1) hxc0) hx0)
      (div_pos (mul_pos ht0 hx0) hxc0)
  have hd := bernoulliDual_eq_of_quadratic ht0.le ht1.le hg hb.le
  have hr := bernoulliR_mul t (c*w)
  rw [hd] at hr
  have h : w * (w⁻¹ + c * bernoulliR t (c*w)) = w*x := by
    rw [mul_add, mul_inv_cancel₀ hw.ne']
    nlinarith only [hr]
  exact (mul_left_cancel₀ hw.ne') h

/-- The same branch is the inverse to the left of both atoms. -/
theorem dilated_bernoulli_inverse_left {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (c x : ℝ) (hx0 : x < 0) (hxc : x < c) :
    let w := realCauchyTransform
      (Measure.map (fun y : ℝ => c*y) (bernoulliMeasure t)) x
    w⁻¹ + c * bernoulliR t (c*w) = x := by
  dsimp
  rw [realCauchyTransform_dilated_bernoulli ht0.le ht1.le]
  let w : ℝ := (1-t)/x + t/(x-c)
  change w⁻¹ + c * bernoulliR t (c*w) = x
  have hx : x ≠ 0 := ne_of_lt hx0
  have hxc0 : x-c < 0 := sub_neg.mpr hxc
  have hxcne : x-c ≠ 0 := ne_of_lt hxc0
  have hw : w < 0 := add_neg (div_neg_of_pos_of_neg (sub_pos.mpr ht1) hx0)
    (div_neg_of_pos_of_neg ht0 hxc0)
  have hwid : w*x*(x-c) = x - (1-t)*c := by
    dsimp [w]
    field_simp
    <;> ring
  have hg : (w*x-1)^2 + (1-c*w)*(w*x-1) - t*(c*w) = 0 := by
    calc
      _ = w * (w*x*(x-c) - (x-(1-t)*c)) := by ring
      _ = 0 := by rw [hwid]; ring
  have hb : 0 < 2*(w*x-1)-c*w+1 := by
    have hid : 2*(w*x-1)-c*w+1 =
        (1-t)*(x-c)/x + t*x/(x-c) := by
      dsimp [w]
      field_simp
      <;> ring
    rw [hid]
    exact add_pos (div_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hxc0) hx0)
      (div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ht0 hx0) hxc0)
  have hd := bernoulliDual_eq_of_quadratic ht0.le ht1.le hg hb.le
  have hr := bernoulliR_mul t (c*w)
  rw [hd] at hr
  have h : w * (w⁻¹ + c * bernoulliR t (c*w)) = w*x := by
    rw [mul_add, mul_inv_cancel₀ hw.ne]
    nlinarith only [hr]
  exact (mul_left_cancel₀ hw.ne) h

/-- The actual resolvent is integrable strictly to the left of the support. -/
theorem integrable_realCauchyKernel_left (μ : Measure ℝ) [IsFiniteMeasure μ]
    (l x : ℝ) (hbound : ∀ᵐ y ∂μ, l ≤ y) (hx : x < l) :
    Integrable (fun y : ℝ => (x-y)⁻¹) μ := by
  have hm : AEStronglyMeasurable (fun y : ℝ => (x-y)⁻¹) μ :=
    (show Measurable (fun y : ℝ => (x-y)⁻¹) by fun_prop).aestronglyMeasurable
  apply (integrable_const ((l-x)⁻¹)).mono' hm
  filter_upwards [hbound] with y hy
  have hxy : 0 < y-x := by linarith
  rw [norm_inv, Real.norm_eq_abs, abs_of_neg (by linarith : x-y < 0)]
  simp only [neg_sub]
  simpa only [one_div] using one_div_le_one_div_of_le
    (show 0 < l-x by linarith) (show l-x ≤ y-x by linarith)

/-- The actual Cauchy transform of a probability law is strictly negative
on the left-hand complement of its support. -/
theorem realCauchyTransform_neg_left (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (l x : ℝ) (hbound : ∀ᵐ y ∂μ, l ≤ y) (hx : x < l) :
    realCauchyTransform μ x < 0 := by
  have hp : ∀ᵐ y ∂μ, 0 < -(x-y)⁻¹ := by
    filter_upwards [hbound] with y hy
    have hxy : x-y < 0 := by linarith
    exact neg_pos.mpr (inv_lt_zero.mpr hxy)
  have hn : 0 ≤ᵐ[μ] (fun y : ℝ => -(x-y)⁻¹) := hp.mono fun _ h => h.le
  have hi := (integrable_realCauchyKernel_left μ l x hbound hx).neg
  have hg : 0 < ∫ y : ℝ, -(x-y)⁻¹ ∂μ := by
    apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
    intro heq
    have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp heq.symm
    obtain ⟨y, hyp, hyz⟩ := (hp.and hz).exists
    exact (ne_of_gt hyp) hyz
  rw [integral_neg] at hg
  exact neg_pos.mp hg

/-- The usual additive R-transform of k copies of each dilated Bernoulli law. -/
def bernoulliFreeSumR (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (w : ℝ) : ℝ :=
  ∑ i, (k : ℝ) * ((a i / k) * bernoulliR t ((a i / k)*w))

/-- The finite repeated/dilated R-transform sum is exactly the scalar branch
whose edge is analyzed in the paper. No spectral claim occurs in this identity. -/
theorem bernoulliFreeSum_inverse_formula {k : ℕ} (hk : 0 < k)
    (t : ℝ) (a : Fin k → ℝ) {w : ℝ} (hw : w ≠ 0) :
    w⁻¹ + bernoulliFreeSumR k t a w = bernoulliK t (k : ℝ) a w := by
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  have heach (i : Fin k) :
      (k : ℝ) * ((a i / k) * bernoulliR t ((a i / k)*w)) =
        (k : ℝ) * bernoulliDual t (a i*w/k) / w := by
    have h := bernoulliR_mul t ((a i / k)*w)
    have heq : (a i / (k : ℝ))*w = a i*w/k := by ring
    rw [heq] at h
    apply (eq_div_iff hw).mpr
    rw [heq]
    calc
      _ = (k : ℝ) * ((a i*w/k) * bernoulliR t (a i*w/k)) := by ring
      _ = _ := congrArg (fun v : ℝ => (k : ℝ)*v) h
  unfold bernoulliFreeSumR bernoulliK
  simp_rw [heach]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  field_simp
  <;> ring

/-- An actual compact probability law with the conventional R-transform germ
of the displayed free sum. The block-modified strong-convergence theorem is
the permitted source of such a law. This record contains no support endpoint,
variational formula, or random-compression conclusion. -/
structure IsBernoulliFreeSumLaw (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (μ : Measure ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  compactlySupported : ∃ M : ℝ, ∀ᵐ x ∂μ, |x| ≤ M
  inverseGerm : ∀ᶠ x : ℝ in atTop,
    (realCauchyTransform μ x)⁻¹ +
      bernoulliFreeSumR k t a (realCauchyTransform μ x) = x
  inverseGermLeft : ∀ᶠ x : ℝ in atBot,
    (realCauchyTransform μ x)⁻¹ +
      bernoulliFreeSumR k t a (realCauchyTransform μ x) = x

/-- Conversion from the additive R-transform germ to the branch formula
required by the spectral-edge theorem. Positivity of the actual Cauchy
transform follows from the probability law and its support bound. -/
theorem IsBernoulliFreeSumLaw.bernoulliK_germ {k : ℕ} {t : ℝ}
    {a : Fin k → ℝ} {μ : Measure ℝ} (h : IsBernoulliFreeSumLaw k t a μ)
    (hk : 0 < k) :
    ∀ᶠ x : ℝ in atTop,
      bernoulliK t (k : ℝ) a (realCauchyTransform μ x) = x := by
  letI := h.probability
  obtain ⟨M, hM⟩ := h.compactlySupported
  have hu : ∀ᵐ x ∂μ, x ≤ M := hM.mono fun x hx => (le_abs_self x).trans hx
  filter_upwards [h.inverseGerm, eventually_gt_atTop M] with x hx hxM
  rw [← bernoulliFreeSum_inverse_formula hk t a
    (ne_of_gt (realCauchyTransform_pos μ M x hu hxM))]
  exact hx


/-- Left-hand conversion of the same additive R-transform germ. -/
theorem IsBernoulliFreeSumLaw.bernoulliK_germ_left {k : ℕ} {t : ℝ}
    {a : Fin k → ℝ} {μ : Measure ℝ} (h : IsBernoulliFreeSumLaw k t a μ)
    (hk : 0 < k) :
    ∀ᶠ x : ℝ in atBot,
      bernoulliK t (k : ℝ) a (realCauchyTransform μ x) = x := by
  letI := h.probability
  obtain ⟨M, hM⟩ := h.compactlySupported
  have hl : ∀ᵐ x ∂μ, -M ≤ x := hM.mono fun x hx => (abs_le.mp hx).1
  filter_upwards [h.inverseGermLeft, eventually_lt_atBot (-M)] with x hx hxM
  rw [← bernoulliFreeSum_inverse_formula hk t a
    (ne_of_lt (realCauchyTransform_neg_left μ (-M) x hl hxM))]
  exact hx

/-- An actual compactly supported probability measure has a rightmost support
point. We construct it from the essential supremum and prove membership in
the topological support, rather than assume an edge exists. -/
theorem compact_probability_right_edge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcompact : ∃ M : ℝ, ∀ᵐ x ∂μ, |x| ≤ M) :
    ∃ r : ℝ, r ∈ realMeasureSupport μ ∧ (∀ᵐ x ∂μ, x ≤ r) ∧
      r = sSup (realMeasureSupport μ) := by
  obtain ⟨M, hM⟩ := hcompact
  have hu : ∀ᵐ x ∂μ, x ≤ M := hM.mono fun x hx => (le_abs_self x).trans hx
  have hl : ∀ᵐ x ∂μ, -M ≤ x := hM.mono fun x hx => (abs_le.mp hx).1
  let r := essSup (fun x : ℝ => x) μ
  have hrbound : ∀ᵐ x ∂μ, x ≤ r := ae_le_essSup (isBoundedUnder_of_eventually_le hu)
  have hcob : (ae μ).IsCoboundedUnder (· ≤ ·) (fun x : ℝ => x) :=
    (isBoundedUnder_of_eventually_ge hl).isCoboundedUnder_le
  have hr : r ∈ realMeasureSupport μ := by
    intro U hU hrU hzero
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU r hrU
    have hnot : ∀ᵐ x ∂μ, x ∉ U := by
      simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hzero
    have hsmall : ∀ᵐ x ∂μ, x ≤ r-ε := by
      filter_upwards [hrbound, hnot] with x hx hxU
      by_contra h
      have hdist : dist x r < ε := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx)]
        linarith
      exact hxU (hball hdist)
    have hle : r ≤ r-ε := limsup_le_of_le hcob hsmall
    linarith
  have hupper : ∀ x ∈ realMeasureSupport μ, x ≤ r := by
    intro x hx
    by_contra h
    have hxgt : r < x := lt_of_not_ge h
    have hzero : μ (Set.Ioi r) = 0 := by
      simpa only [ae_iff, not_le, Set.Ioi] using hrbound
    exact hx (Set.Ioi r) isOpen_Ioi hxgt hzero
  refine ⟨r, hr, hrbound, ?_⟩
  apply le_antisymm
  · exact le_csSup ⟨r, hupper⟩ hr
  · exact csSup_le ⟨r, hr⟩ hupper

/-- Support hypotheses needed by the spectral-edge theorem follow from the
law's probability and compactness fields. -/
theorem IsBernoulliFreeSumLaw.right_edge {k : ℕ} {t : ℝ}
    {a : Fin k → ℝ} {μ : Measure ℝ} (h : IsBernoulliFreeSumLaw k t a μ) :
    sSup (realMeasureSupport μ) ∈ realMeasureSupport μ ∧
      (∀ᵐ x ∂μ, x ≤ sSup (realMeasureSupport μ)) := by
  letI := h.probability
  obtain ⟨r, hr, hbound, heq⟩ := compact_probability_right_edge μ h.compactlySupported
  simpa only [heq] using And.intro hr hbound

end ProjectionChannels
