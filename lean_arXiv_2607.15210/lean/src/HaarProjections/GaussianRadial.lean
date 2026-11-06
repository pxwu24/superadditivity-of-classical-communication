import HaarProjections.GaussianRank
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.InnerProductSpace.LinearMap

open scoped ENNReal NNReal BigOperators
open MeasureTheory MeasureTheory.Measure

noncomputable section
namespace GaussianRank

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The Gaussian normalizing constant in an arbitrary finite-dimensional real Hilbert space. -/
def gaussianMass : ℝ := Real.pi ^ (Module.finrank ℝ V / 2 : ℝ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem gaussianMass_pos : 0 < gaussianMass V := Real.rpow_pos_of_pos Real.pi_pos _

/-- A radial Gaussian density with respect to Lebesgue measure. -/
def radialDensity (x : V) : ℝ≥0∞ :=
  ENNReal.ofReal ((gaussianMass V)⁻¹ * Real.exp (- ‖x‖ ^ 2))

/-- The actual radial Gaussian measure, not a predicate representing its expected properties. -/
def radialGaussian : Measure V := volume.withDensity (radialDensity V)

theorem integrable_radial_exp : Integrable (fun x : V => Real.exp (- ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := 1) (by norm_num) 0 (0 : V)).re
  simpa only [Complex.one_re, neg_mul, one_mul, zero_mul, add_zero,
    ← Complex.ofReal_pow, ← Complex.ofReal_neg, Complex.exp_ofReal_re] using h

theorem integral_radial_exp : ∫ x : V, Real.exp (- ‖x‖ ^ 2) = gaussianMass V := by
  simpa [gaussianMass] using
    (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) (b := 1) (by norm_num))

omit [FiniteDimensional ℝ V] in
theorem measurable_radialDensity : Measurable (radialDensity V) := by
  unfold radialDensity
  fun_prop

instance : IsProbabilityMeasure (radialGaussian V) where
  measure_univ := by
    rw [radialGaussian, withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ, radialDensity]
    rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_radial_exp V).const_mul _) (by
      filter_upwards [] with x
      exact mul_nonneg (inv_nonneg.mpr (gaussianMass_pos V).le) (Real.exp_pos _).le)]
    rw [integral_const_mul, integral_radial_exp V, inv_mul_cancel₀ (gaussianMass_pos V).ne']
    exact ENNReal.ofReal_one

/-- Every real linear isometry preserves this Gaussian law. -/
theorem radialGaussian_isometry_invariant (L : V ≃ₗᵢ[ℝ] V) :
    (radialGaussian V).map L = radialGaussian V := by
  ext s hs
  rw [Measure.map_apply L.continuous.measurable hs, radialGaussian,
    withDensity_apply _ (L.continuous.measurable hs), withDensity_apply _ hs]
  have h := L.measurePreserving.setLIntegral_comp_preimage_emb
    L.toHomeomorph.measurableEmbedding (radialDensity V) s
  simpa only [radialDensity, L.norm_map] using h

/-- Lebesgue-null sets remain null under the radial Gaussian law. -/
theorem radialGaussian_absolutelyContinuous : radialGaussian V ≪ volume :=
  withDensity_absolutelyContinuous _ _

end GaussianRank

