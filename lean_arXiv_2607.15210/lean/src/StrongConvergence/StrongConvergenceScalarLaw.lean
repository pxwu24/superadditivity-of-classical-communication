import RandomCompression.RevisionBernoulliLaw

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

noncomputable section
namespace ProjectionChannels

/-- The actual Bernoulli probability law under an arbitrary real dilation. -/
def scalarBernoulliMeasure (t a : ℝ) : Measure ℝ :=
  Measure.map (fun x : ℝ => a * x) (bernoulliMeasure t)

theorem scalarBernoulliMeasure_eq (t a : ℝ) :
    scalarBernoulliMeasure t a =
      ENNReal.ofReal (1-t) • Measure.dirac 0 + ENNReal.ofReal t • Measure.dirac a := by
  have hm : Measurable (fun x : ℝ => a*x) := by fun_prop
  simp [scalarBernoulliMeasure, bernoulliMeasure, Measure.map_add _ _ hm,
    Measure.map_dirac hm]

theorem scalarBernoulliMeasure_isProbability {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : ℝ) :
    IsProbabilityMeasure (scalarBernoulliMeasure t a) := by
  letI := bernoulliMeasure_isProbability ht0 ht1
  exact isProbabilityMeasure_map (by fun_prop)

theorem ae_scalarBernoulliMeasure_zero_or_a (t a : ℝ) :
    ∀ᵐ x ∂scalarBernoulliMeasure t a, x = 0 ∨ x = a := by
  rw [scalarBernoulliMeasure_eq, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    simp [ae_dirac_eq]
  · apply Measure.ae_smul_measure
    simp [ae_dirac_eq]

theorem scalarBernoulliMeasure_isFreeSumLaw {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (a : ℝ) :
    IsBernoulliFreeSumLaw 1 t (fun _ : Fin 1 => a) (scalarBernoulliMeasure t a) := by
  refine ⟨scalarBernoulliMeasure_isProbability ht0.le ht1.le a, ?_, ?_, ?_⟩
  · refine ⟨|a|, (ae_scalarBernoulliMeasure_zero_or_a t a).mono ?_⟩
    intro x hx
    rcases hx with rfl | rfl <;> simp
  · filter_upwards [eventually_gt_atTop (max 0 a)] with x hx
    have h := dilated_bernoulli_inverse_right ht0 ht1 a x
      (lt_of_le_of_lt (le_max_left _ _) hx) (lt_of_le_of_lt (le_max_right _ _) hx)
    simpa [scalarBernoulliMeasure, bernoulliFreeSumR] using h
  · filter_upwards [eventually_lt_atBot (min 0 a)] with x hx
    have h := dilated_bernoulli_inverse_left ht0 ht1 a x
      (lt_of_lt_of_le hx (min_le_left _ _)) (lt_of_lt_of_le hx (min_le_right _ _))
    simpa [scalarBernoulliMeasure, bernoulliFreeSumR] using h

theorem integral_scalarBernoulliMeasure {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂scalarBernoulliMeasure t a) = (1-t) * f 0 + t * f a := by
  rw [scalarBernoulliMeasure_eq, integral_add_measure
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)]
  simp [ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal (sub_nonneg.mpr ht1)]

theorem scalarBernoulliMeasure_support {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (a : ℝ) :
    realMeasureSupport (scalarBernoulliMeasure t a) = {0, a} := by
  ext x
  constructor
  · intro hx
    by_contra hxnot
    have hopen : IsOpen ({0, a}ᶜ : Set ℝ) :=
      (isClosed_singleton.union isClosed_singleton).isOpen_compl
    have hnonzero := hx ({0,a}ᶜ) hopen hxnot
    apply hnonzero
    rw [scalarBernoulliMeasure_eq]
    simp
  · intro hx U hU hxU
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · rw [scalarBernoulliMeasure_eq]
      simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem hxU,
        ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr ht1)]
    · have hxa : x = a := Set.mem_singleton_iff.mp hx
      subst x
      rw [scalarBernoulliMeasure_eq]
      simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem hxU,
        ENNReal.ofReal_eq_zero, not_le.mpr ht0]

theorem scalarBernoulliMeasure_abs_sSup {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (a c : ℝ) :
    sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport (scalarBernoulliMeasure t a)) =
      max |c| |c+a| := by
  rw [scalarBernoulliMeasure_support ht0 ht1]
  rw [Set.image_pair, add_zero, csSup_pair]

end ProjectionChannels
