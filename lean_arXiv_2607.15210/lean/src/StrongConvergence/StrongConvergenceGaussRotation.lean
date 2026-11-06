import HaarProjections.GaussianRadial
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

open MeasureTheory
open scoped NNReal ENNReal RealInnerProductSpace
noncomputable section
namespace ProjectionChannels.GaussConcentration
open GaussianRank
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Orthogonal reflection mixing two independent Gaussian vectors. -/
def gaussianRotation (θ : ℝ) : (V × V) →ₗ[ℝ] (V × V) :=
  ((Real.sin θ) • LinearMap.fst ℝ V V + (Real.cos θ) • LinearMap.snd ℝ V V).prod
    ((Real.cos θ) • LinearMap.fst ℝ V V - (Real.sin θ) • LinearMap.snd ℝ V V)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma gaussianRotation_apply (θ : ℝ) (p : V × V) :
    gaussianRotation θ p =
      (Real.sin θ • p.1 + Real.cos θ • p.2, Real.cos θ • p.1 - Real.sin θ • p.2) := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma gaussianRotation_involutive (θ : ℝ) : Function.Involutive (gaussianRotation (V := V) θ) := by
  intro p
  simp only [gaussianRotation_apply]
  ext
  · calc
      _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) • p.1 +
          (Real.sin θ * Real.cos θ - Real.cos θ * Real.sin θ) • p.2 := by module
      _ = p.1 := by rw [Real.sin_sq_add_cos_sq]; simp [mul_comm]
  · calc
      _ = (Real.cos θ * Real.sin θ - Real.sin θ * Real.cos θ) • p.1 +
          (Real.sin θ ^ 2 + Real.cos θ ^ 2) • p.2 := by module
      _ = p.2 := by rw [Real.sin_sq_add_cos_sq]; simp [mul_comm]

lemma gaussianRotation_det_abs (θ : ℝ) : |LinearMap.det (gaussianRotation (V := V) θ)| = 1 := by
  have hcomp : (gaussianRotation (V := V) θ).comp (gaussianRotation θ) = LinearMap.id := by
    apply LinearMap.ext
    intro p
    exact gaussianRotation_involutive (V := V) θ p
  have hdet : LinearMap.det (gaussianRotation (V := V) θ) *
      LinearMap.det (gaussianRotation (V := V) θ) = 1 := by
    rw [← LinearMap.det_comp, hcomp, LinearMap.det_id]
  have hsq := sq_abs (LinearMap.det (gaussianRotation (V := V) θ))
  have hn := abs_nonneg (LinearMap.det (gaussianRotation (V := V) θ))
  nlinarith

lemma gaussianRotation_energy (θ : ℝ) (p : V × V) :
    ‖(gaussianRotation θ p).1‖ ^ 2 + ‖(gaussianRotation θ p).2‖ ^ 2 =
      ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  rw [gaussianRotation_apply]
  dsimp only
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
    real_inner_smul_right]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Product Lebesgue measure is preserved; the product has its usual max norm. -/
theorem gaussianRotation_volume_preserving (θ : ℝ) :
    MeasurePreserving (gaussianRotation (V := V) θ)
      ((volume : Measure V).prod (volume : Measure V)) ((volume : Measure V).prod (volume : Measure V)) := by
  haveI : Measure.IsAddHaarMeasure ((volume : Measure V).prod (volume : Measure V)) := inferInstance
  refine ⟨(gaussianRotation (V := V) θ).continuous_of_finiteDimensional.measurable, ?_⟩
  have hd : LinearMap.det (gaussianRotation (V := V) θ) ≠ 0 := by
    intro hz
    have h := gaussianRotation_det_abs (V := V) θ
    simp [hz] at h
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hd,
    abs_inv, gaussianRotation_det_abs]
  simp

lemma radialDensity_rotation (θ : ℝ) (p : V × V) :
    radialDensity V (gaussianRotation θ p).1 * radialDensity V (gaussianRotation θ p).2 =
      radialDensity V p.1 * radialDensity V p.2 := by
  have hM : 0 ≤ (gaussianMass V)⁻¹ := inv_nonneg.mpr (gaussianMass_pos V).le
  unfold radialDensity
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    _ = (gaussianMass V)⁻¹ ^ 2 *
        Real.exp (-(‖(gaussianRotation θ p).1‖ ^ 2 + ‖(gaussianRotation θ p).2‖ ^ 2)) := by
      rw [neg_add, Real.exp_add]
      ring
    _ = (gaussianMass V)⁻¹ ^ 2 * Real.exp (-(‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)) := by
      rw [gaussianRotation_energy]
    _ = _ := by rw [neg_add, Real.exp_add]; ring

/-- Rotation preserves the actual product Gaussian law. -/
theorem gaussianRotation_measurePreserving (θ : ℝ) :
    MeasurePreserving (gaussianRotation (V := V) θ)
      ((radialGaussian V).prod (radialGaussian V))
      ((radialGaussian V).prod (radialGaussian V)) := by
  have hc := (gaussianRotation (V := V) θ).continuous_of_finiteDimensional
  let e : (V × V) ≃ᵐ (V × V) := MeasurableEquiv.ofInvolutive
    (gaussianRotation θ) (gaussianRotation_involutive θ) hc.measurable
  refine ⟨hc.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hc.measurable hs]
  simp only [radialGaussian, prod_withDensity (measurable_radialDensity V)
    (measurable_radialDensity V), withDensity_apply _ hs,
    withDensity_apply _ (hc.measurable hs)]
  have h := (gaussianRotation_volume_preserving (V := V) θ).setLIntegral_comp_preimage_emb
    e.measurableEmbedding (fun p : V × V => radialDensity V p.1 * radialDensity V p.2) s
  simpa only [radialDensity_rotation] using h

end ProjectionChannels.GaussConcentration
#print axioms ProjectionChannels.GaussConcentration.gaussianRotation_measurePreserving
