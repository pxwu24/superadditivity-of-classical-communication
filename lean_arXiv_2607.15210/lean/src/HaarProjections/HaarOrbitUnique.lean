import HaarProjections.HaarMeasure
import Mathlib.MeasureTheory.Integral.Prod

open scoped BigOperators ENNReal
open Matrix MeasureTheory Set

namespace HaarProjection
noncomputable section
set_option maxHeartbeats 800000

variable {E : Type*} [Fintype E] [DecidableEq E]


/-- The unitary conjugacy orbit is compact, hence Borel. -/
theorem measurableSet_unitary_orbit (P₀ : Matrix E E ℂ) :
    MeasurableSet {P : Matrix E E ℂ | ∃ U : Matrix.unitaryGroup E ℂ,
      P = (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose} := by
  have hc := isCompact_range (continuous_unitary_orbit P₀)
  have he : {P : Matrix E E ℂ | ∃ U : Matrix.unitaryGroup E ℂ,
      P = (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose} =
      Set.range (fun U : Matrix.unitaryGroup E ℂ =>
        (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose) := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]
  rw [he]
  exact hc.isClosed.measurableSet

/-- A conjugation-invariant probability measure concentrated on one unitary orbit
is exactly the normalized Haar orbit measure. The proof is the Haar-averaging
argument with Tonelli's theorem. -/
theorem eq_haarProjectionLaw_of_invariant
    (μ : Measure (Matrix E E ℂ)) [IsProbabilityMeasure μ] (P₀ : Matrix E E ℂ)
    (hinv : ∀ U : Matrix.unitaryGroup E ℂ,
      μ.map (fun P => (U : Matrix E E ℂ) * P * (U : Matrix E E ℂ).conjTranspose) = μ)
    (horbit : ∀ᵐ P ∂μ, ∃ U : Matrix.unitaryGroup E ℂ,
      P = (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose) :
    μ = haarProjectionLaw P₀ := by
  apply Measure.ext
  intro s hs
  let f : Matrix.unitaryGroup E ℂ → Matrix E E ℂ → ℝ≥0∞ :=
    fun U P => s.indicator (fun _ => 1)
      ((U : Matrix E E ℂ) * P * (U : Matrix E E ℂ).conjTranspose)
  have hind : Measurable (s.indicator (fun _ : Matrix E E ℂ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hs
  have hC (U : Matrix.unitaryGroup E ℂ) : Measurable (fun P : Matrix E E ℂ =>
      (U : Matrix E E ℂ) * P * (U : Matrix E E ℂ).conjTranspose) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have hf : Measurable (Function.uncurry f) := by
    apply hind.comp
    exact ((continuous_fst.subtype_val.matrix_mul continuous_snd).matrix_mul
      continuous_fst.subtype_val.matrix_conjTranspose).measurable
  have hL (U : Matrix.unitaryGroup E ℂ) : ∫⁻ P, f U P ∂μ = μ s := by
    change (∫⁻ P, s.indicator (fun _ => 1)
      ((U : Matrix E E ℂ) * P * (U : Matrix E E ℂ).conjTranspose) ∂μ) = _
    rw [← lintegral_map hind (hC U), hinv U]
    simpa only [one_mul] using lintegral_indicator_const (μ := μ) hs (1 : ℝ≥0∞)
  have hR (P : Matrix E E ℂ) :
      ∫⁻ U, f U P ∂(unitaryHaar (E := E)) = haarProjectionLaw P s := by
    change (∫⁻ U : Matrix.unitaryGroup E ℂ, s.indicator (fun _ => 1)
      ((U : Matrix E E ℂ) * P * (U : Matrix E E ℂ).conjTranspose) ∂unitaryHaar) = _
    rw [← lintegral_map hind (continuous_unitary_orbit P).measurable]
    simpa only [haarProjectionLaw, one_mul] using
      lintegral_indicator_const (μ := haarProjectionLaw P) hs (1 : ℝ≥0∞)
  calc
    μ s = ∫⁻ U, ∫⁻ P, f U P ∂μ ∂(unitaryHaar (E := E)) := by simp_rw [hL]; simp
    _ = ∫⁻ P, ∫⁻ U, f U P ∂(unitaryHaar (E := E)) ∂μ :=
      lintegral_lintegral_swap hf.aemeasurable
    _ = ∫⁻ P, haarProjectionLaw P s ∂μ := by simp_rw [hR]
    _ = ∫⁻ _P, haarProjectionLaw P₀ s ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [horbit] with P hP
      obtain ⟨U, rfl⟩ := hP
      rw [haarProjectionLaw_conjugate_base]
    _ = haarProjectionLaw P₀ s := by simp

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Gaussian left-unitary invariance is carried by whitening to invariance of
its projection law under unitary conjugation. -/
theorem whitenedLaw_conjugation_invariant
    (ν : Measure (Matrix E D ℂ))
    (hinv : ∀ U : Matrix.unitaryGroup E ℂ,
      ν.map (fun G => (U : Matrix E E ℂ) * G) = ν)
    (U : Matrix.unitaryGroup E ℂ) :
    (ν.map whitenedProjection).map
      (fun P => (U : Matrix E E ℂ) * P * (U : Matrix E E ℂ).conjTranspose) =
      ν.map whitenedProjection := by
  have hm : Measurable (fun G : Matrix E D ℂ => (U : Matrix E E ℂ) * G) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hc : Measurable (fun P : Matrix E E ℂ =>
      (U : Matrix E E ℂ) * P * (U : Matrix E E ℂ).conjTranspose) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  rw [Measure.map_map hc measurable_whitenedProjection]
  have he : (fun P : Matrix E E ℂ =>
      (U : Matrix E E ℂ) * P * (U : Matrix E E ℂ).conjTranspose) ∘ whitenedProjection =
      (whitenedProjection : Matrix E D ℂ → Matrix E E ℂ) ∘
        (fun G => (U : Matrix E E ℂ) * G) := by
    funext G
    exact (whitenedProjection_unitary_equivariant U G).symm
  rw [he, ← Measure.map_map measurable_whitenedProjection hm, hinv U]

/-- A measurable, unitary-invariant matrix law whose whitened samples lie on
one projection orbit realizes that orbit's Haar law. -/
theorem whitenedLaw_eq_haarProjectionLaw
    (ν : Measure (Matrix E D ℂ)) [IsProbabilityMeasure ν]
    (P₀ : Matrix E E ℂ)
    (hinv : ∀ U : Matrix.unitaryGroup E ℂ,
      ν.map (fun G => (U : Matrix E E ℂ) * G) = ν)
    (horbit : ∀ᵐ G ∂ν, ∃ U : Matrix.unitaryGroup E ℂ,
      whitenedProjection G =
        (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose) :
    ν.map whitenedProjection = haarProjectionLaw P₀ := by
  letI : IsProbabilityMeasure (ν.map (whitenedProjection : Matrix E D ℂ → Matrix E E ℂ)) :=
    MeasureTheory.isProbabilityMeasure_map measurable_whitenedProjection.aemeasurable
  apply eq_haarProjectionLaw_of_invariant _ P₀
  · exact whitenedLaw_conjugation_invariant ν hinv
  · exact (ae_map_iff measurable_whitenedProjection.aemeasurable
      (measurableSet_unitary_orbit P₀)).mpr horbit

/-- Equality of realization laws transfers each measurable almost-sure assertion
between whitened Gaussian matrices and Haar-conjugated projections. -/
theorem ae_haar_iff_ae_whitened_of_law_eq
    (ν : Measure (Matrix E D ℂ)) (P₀ : Matrix E E ℂ)
    (hlaw : ν.map whitenedProjection = haarProjectionLaw P₀)
    (q : Matrix E E ℂ → Prop) (hq : MeasurableSet {P | q P}) :
    (∀ᵐ U : Matrix.unitaryGroup E ℂ ∂(unitaryHaar (E := E)),
      q ((U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose)) ↔
      ∀ᵐ G ∂ν, q (whitenedProjection G) := by
  rw [← ae_map_iff (continuous_unitary_orbit P₀).measurable.aemeasurable hq]
  change (∀ᵐ P ∂haarProjectionLaw P₀, q P) ↔ _
  rw [← hlaw, ae_map_iff measurable_whitenedProjection.aemeasurable hq]

end
end HaarProjection

