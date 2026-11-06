import HaarProjections.GaussianRadial
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

open MeasureTheory
open scoped NNReal ENNReal RealInnerProductSpace
noncomputable section
namespace ProjectionChannels.GaussConcentration
open GaussianRank
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integrable_exp_neg_sq_add_inner (c : ℝ) (w : V) :
    Integrable (fun x : V => Real.exp (-‖x‖ ^ 2 + c * ⟪w, x⟫)) volume := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := 1) (by norm_num) (c : ℂ) w).re
  simpa only [neg_mul, one_mul, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.exp_ofReal_re] using h

lemma integral_exp_neg_sq_add_inner (c : ℝ) (w : V) :
    (∫ x : V, Real.exp (-‖x‖ ^ 2 + c * ⟪w, x⟫)) =
      gaussianMass V * Real.exp (c ^ 2 * ‖w‖ ^ 2 / 4) := by
  apply Complex.ofReal_injective
  change Complex.ofRealLI (∫ x : V, Real.exp (-‖x‖ ^ 2 + c * ⟪w, x⟫)) = _
  rw [← Complex.ofRealLI.integral_comp_comm]
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := V) (b := 1) (by norm_num) (c : ℂ) w
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with x
    simp [Complex.ofRealLI]
  · simp [gaussianMass, Complex.ofReal_cpow Real.pi_pos.le]

lemma integral_radialGaussian_eq (f : V → ℝ) :
    (∫ x, f x ∂radialGaussian V) =
      (gaussianMass V)⁻¹ * ∫ x : V, Real.exp (-‖x‖ ^ 2) * f x := by
  rw [radialGaussian, integral_withDensity_eq_integral_toReal_smul
    (measurable_radialDensity V) (Filter.Eventually.of_forall (fun x => by
      simp [radialDensity]))]
  simp only [radialDensity, ENNReal.toReal_ofReal (mul_nonneg
    (inv_nonneg.mpr (gaussianMass_pos V).le) (Real.exp_pos _).le), smul_eq_mul,
    mul_assoc, integral_const_mul]

/-- Exact linear moment-generating function for the actual radial Gaussian,
with covariance `I/2`. -/
theorem radialGaussian_mgf_inner (c : ℝ) (w : V) :
    (∫ x, Real.exp (c * ⟪w, x⟫) ∂radialGaussian V) =
      Real.exp (c ^ 2 * ‖w‖ ^ 2 / 4) := by
  rw [integral_radialGaussian_eq]
  simp_rw [← Real.exp_add]
  rw [integral_exp_neg_sq_add_inner, ← mul_assoc,
    inv_mul_cancel₀ (gaussianMass_pos V).ne', one_mul]

theorem integrable_radialGaussian_exp_inner (c : ℝ) (w : V) :
    Integrable (fun x => Real.exp (c * ⟪w, x⟫)) (radialGaussian V) := by
  by_contra h
  have he := radialGaussian_mgf_inner c w
  rw [integral_undef h] at he
  exact (Real.exp_pos _).ne' he.symm

/-- Tonelli-ready version of the linear Gaussian MGF identity. -/
theorem radialGaussian_lintegral_exp_inner (c : ℝ) (w : V) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (c * ⟪w, x⟫)) ∂radialGaussian V) =
      ENNReal.ofReal (Real.exp (c ^ 2 * ‖w‖ ^ 2 / 4)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_radialGaussian_exp_inner c w)
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)), radialGaussian_mgf_inner]

/-- Riesz-form Gaussian MGF, as needed for a derivative evaluated on an independent Gaussian. -/
theorem radialGaussian_mgf_functional (c : ℝ) (L : V →L[ℝ] ℝ) :
    (∫ x, Real.exp (c * L x) ∂radialGaussian V) =
      Real.exp (c ^ 2 * ‖L‖ ^ 2 / 4) := by
  have h := radialGaussian_mgf_inner c ((InnerProductSpace.toDual ℝ V).symm L)
  simpa only [InnerProductSpace.toDual_symm_apply, LinearIsometryEquiv.norm_map] using h

end ProjectionChannels.GaussConcentration
#print axioms ProjectionChannels.GaussConcentration.radialGaussian_mgf_inner

#print axioms ProjectionChannels.GaussConcentration.radialGaussian_mgf_functional
