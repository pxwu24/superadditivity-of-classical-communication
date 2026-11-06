import RandomCompression.RevisionBernoulliEdge
import RandomCompression.RevisionBernoulliLaw
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Holomorphic continuation of the explicit Bernoulli inverse branch

The positive real radicands select the principal square-root branch. All
analyticity and conjugation assertions used in the spectral-edge proof are
proved here for the formula in the paper.
-/

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate BigOperators

noncomputable section
namespace ProjectionChannels

def bernoulliComplexRadicand (t : ℝ) (z : ℂ) : ℂ :=
  (z + 2 * (t : ℂ) - 1)^2 + 4 * (t : ℂ) * (1 - (t : ℂ))

def bernoulliComplexDelta (t : ℝ) (z : ℂ) : ℂ :=
  bernoulliComplexRadicand t z ^ (1 / 2 : ℂ)

def bernoulliComplexDual (t : ℝ) (z : ℂ) : ℂ :=
  (z - 1 + bernoulliComplexDelta t z) / 2

def bernoulliComplexK {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (z : ℂ) : ℂ :=
  (1 + (k : ℂ) * ∑ i, bernoulliComplexDual t ((a i : ℂ) * z / (k : ℂ))) / z

theorem bernoulliComplexRadicand_ofReal (t y : ℝ) :
    bernoulliComplexRadicand t (y : ℂ) =
      (((y+2*t-1)^2+4*t*(1-t) : ℝ) : ℂ) := by
  simp [bernoulliComplexRadicand]

theorem bernoulliComplexRadicand_mem_slitPlane {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    bernoulliComplexRadicand t (y : ℂ) ∈ Complex.slitPlane := by
  rw [bernoulliComplexRadicand_ofReal, Complex.ofReal_mem_slitPlane]
  have ht : 0 < 1-t := sub_pos.mpr ht1
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)

theorem bernoulliComplexDelta_ofReal {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    bernoulliComplexDelta t (y : ℂ) = (bernoulliDelta t y : ℂ) := by
  rw [bernoulliComplexDelta, bernoulliComplexRadicand_ofReal]
  have ht : 0 < 1-t := sub_pos.mpr ht1
  have hp : 0 ≤ (y+2*t-1)^2+4*t*(1-t) := by positivity
  have hex : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hex, ← Complex.ofReal_cpow hp, ← Real.sqrt_eq_rpow]
  rfl

theorem bernoulliComplexDual_ofReal {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    bernoulliComplexDual t (y : ℂ) = (bernoulliDual t y : ℂ) := by
  simp only [bernoulliComplexDual, bernoulliComplexDelta_ofReal ht0 ht1,
    bernoulliDual, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_ofNat]

theorem bernoulliComplexK_ofReal {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (w : ℝ) :
    bernoulliComplexK t k a (w : ℂ) = (bernoulliK t k a w : ℂ) := by
  unfold bernoulliComplexK bernoulliK
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div,
    bernoulliComplexDual_ofReal ht0 ht1]
  push_cast
  rfl

theorem analyticAt_bernoulliComplexRadicand (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ (bernoulliComplexRadicand t) z := by
  unfold bernoulliComplexRadicand
  fun_prop

theorem analyticAt_bernoulliComplexDelta {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    AnalyticAt ℂ (bernoulliComplexDelta t) (y : ℂ) := by
  exact (analyticAt_bernoulliComplexRadicand t (y : ℂ)).cpow analyticAt_const
    (bernoulliComplexRadicand_mem_slitPlane ht0 ht1 y)

theorem analyticAt_bernoulliComplexDual {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    AnalyticAt ℂ (bernoulliComplexDual t) (y : ℂ) := by
  exact ((analyticAt_id.sub analyticAt_const).add
    (analyticAt_bernoulliComplexDelta ht0 ht1 y)).div analyticAt_const (by norm_num)

theorem analyticAt_bernoulliComplexK_ne {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (w : ℝ) (hw : w ≠ 0) :
    AnalyticAt ℂ (bernoulliComplexK t k a) (w : ℂ) := by
  have hs : AnalyticAt ℂ
      (fun z => ∑ i, bernoulliComplexDual t ((a i : ℂ) * z / (k : ℂ))) (w : ℂ) := by
    apply Finset.analyticAt_sum
    intro i _
    have hh := analyticAt_bernoulliComplexDual ht0 ht1 (a i*w/k)
    push_cast at hh
    have hc : AnalyticAt ℂ (fun z : ℂ => (a i : ℂ)*z/(k : ℂ)) (w : ℂ) := by
      simp only [div_eq_mul_inv]
      fun_prop
    exact hh.comp (f := fun z : ℂ => (a i : ℂ)*z/(k : ℂ)) (x := (w : ℂ)) hc
  exact (analyticAt_const.add (analyticAt_const.mul hs)).div analyticAt_id
    (by exact_mod_cast hw)

theorem analyticAt_bernoulliComplexK {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (w : ℝ) (hw : 0 < w) :
    AnalyticAt ℂ (bernoulliComplexK t k a) (w : ℂ) :=
  analyticAt_bernoulliComplexK_ne t k a ht0 ht1 w hw.ne'

theorem bernoulliComplexRadicand_conj (t : ℝ) (z : ℂ) :
    bernoulliComplexRadicand t (conj z) = conj (bernoulliComplexRadicand t z) := by
  simp [bernoulliComplexRadicand, map_ofNat]

theorem bernoulliComplexDelta_conj (t : ℝ) (z : ℂ)
    (hz : bernoulliComplexRadicand t z ∈ Complex.slitPlane) :
    bernoulliComplexDelta t (conj z) = conj (bernoulliComplexDelta t z) := by
  unfold bernoulliComplexDelta
  rw [bernoulliComplexRadicand_conj]
  simpa only [map_div₀, map_one, map_ofNat] using Complex.conj_cpow (bernoulliComplexRadicand t z) (1 / 2 : ℂ)
    (Complex.slitPlane_arg_ne_pi hz)

theorem bernoulliComplexDual_conj (t : ℝ) (z : ℂ)
    (hz : bernoulliComplexRadicand t z ∈ Complex.slitPlane) :
    bernoulliComplexDual t (conj z) = conj (bernoulliComplexDual t z) := by
  simp [bernoulliComplexDual, bernoulliComplexDelta_conj t z hz, map_ofNat]

/-- Local Schwarz symmetry for every real point of the inverse branch. -/
theorem bernoulliComplexK_eventually_conj {ι : Type*} [Fintype ι]
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (w : ℝ) :
    ∀ᶠ z in 𝓝 (w : ℂ),
      bernoulliComplexK t k a (conj z) = conj (bernoulliComplexK t k a z) := by
  have hm : ∀ i, ∀ᶠ z in 𝓝 (w : ℂ),
      bernoulliComplexRadicand t ((a i : ℂ)*z/(k : ℂ)) ∈ Complex.slitPlane := by
    intro i
    have hc : ContinuousAt (fun z : ℂ =>
        bernoulliComplexRadicand t ((a i : ℂ)*z/(k : ℂ))) (w : ℂ) := by
      unfold bernoulliComplexRadicand
      fun_prop
    apply hc.eventually (Complex.isOpen_slitPlane.mem_nhds _)
    have hh := bernoulliComplexRadicand_mem_slitPlane ht0 ht1 (a i*w/k)
    simpa using hh
  filter_upwards [Filter.eventually_all.mpr hm] with z hz
  unfold bernoulliComplexK
  simp only [map_div₀, map_add, map_one, map_mul, Complex.conj_ofReal, map_sum]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  have hh := bernoulliComplexDual_conj t ((a i : ℂ)*z/(k : ℂ)) (hz i)
  simpa using hh

/-- Lemma A.1 for an actual compactly supported probability law with the
standard inverse-Cauchy characterization of the Bernoulli free convolution.
All continuation and edge arguments are included in the proof. -/
theorem bernoulli_edge_from_cauchy_characterization
    {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ)
    (hr : r ∈ realMeasureSupport μ) (hbound : ∀ᵐ s : ℝ ∂μ, s ≤ r)
    (t k : ℝ) (a : ι → ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k)
    (hgerm : ∀ᶠ x : ℝ in atTop,
      bernoulliK t k a (realCauchyTransform μ x) = x) :
    IsGLB (bernoulliKValues t k a) r ∧
      r = sSup (bernoulliObjectiveValues t k a) := by
  apply bernoulli_right_edge_of_inverse_cauchy_germ μ r hr hbound t k a ht0 ht1 hk
    (bernoulliComplexK t k a)
    (analyticAt_bernoulliComplexK t k a ht0 ht1)
    (fun w _ => bernoulliComplexK_ofReal t k a ht0 ht1 w)
    (fun w _ => bernoulliComplexK_eventually_conj t k a ht0 ht1 w)
  filter_upwards [hgerm] with x hx
  rw [bernoulliComplexK_ofReal t k a ht0 ht1, hx]

/-- **Lemma A.1.** The right edge of the actual Bernoulli free-sum law
is the support function of the explicitly defined feasible body. The law is
specified by its standard additive R-transform germ; no edge identity is assumed. -/
theorem bernoulli_free_sum_right_edge {k : ℕ} (hk : 0 < k)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : Fin k → ℝ)
    (μ : Measure ℝ) (hμ : IsBernoulliFreeSumLaw k t a μ) :
    sSup (realMeasureSupport μ) =
      sSup (bernoulliObjectiveValues t (k : ℝ) a) := by
  letI := hμ.probability
  exact (bernoulli_edge_from_cauchy_characterization μ (sSup (realMeasureSupport μ))
    hμ.right_edge.1 hμ.right_edge.2 t (k : ℝ) a ht0 ht1 (Nat.cast_pos.mpr hk)
    (hμ.bernoulliK_germ hk)).2

end ProjectionChannels
