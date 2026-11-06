import StrongConvergence.StrongConvergenceGaussMGF
import HaarProjections.GaussianMatrixLaw
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Tactic

open MeasureTheory GaussianRank
open scoped NNReal ENNReal RealInnerProductSpace
noncomputable section
namespace ProjectionChannels.GaussConcentration

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem radialGaussian_mgf_norm_sq (s : ℝ) (hs : s < 1) :
    (∫ x : V, Real.exp (s * ‖x‖^2) ∂radialGaussian V) =
      (1-s) ^ (-(Module.finrank ℝ V / 2 : ℝ)) := by
  rw [integral_radialGaussian_eq]
  simp_rw [← Real.exp_add]
  have hex : (fun x : V => Real.exp (-‖x‖^2 + s * ‖x‖^2)) =
      fun x : V => Real.exp (-(1-s) * ‖x‖^2) := by
    funext x
    congr 1
    ring
  rw [hex, GaussianFourier.integral_rexp_neg_mul_sq_norm (by linarith)]
  rw [Real.div_rpow Real.pi_pos.le (by linarith), gaussianMass,
    ← div_eq_inv_mul, div_div, mul_comm ((1-s)^_), ← div_div,
    div_self (Real.rpow_pos_of_pos Real.pi_pos _).ne', one_div, Real.rpow_neg (by linarith)]

lemma complex_euclidean_finrank (E : Type*) [Fintype E] :
    Module.finrank ℝ (EuclideanSpace ℂ E) = 2 * Fintype.card E := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ E),
    Complex.finrank_real_complex, finrank_euclideanSpace]

theorem radialGaussian_complex_mgf_norm_sq (E : Type*) [Fintype E]
    (s : ℝ) (hs : s < 1) :
    (∫ x : EuclideanSpace ℂ E, Real.exp (s * ‖x‖^2) ∂radialGaussian _) =
      ((1-s)⁻¹)^Fintype.card E := by
  rw [radialGaussian_mgf_norm_sq s hs, complex_euclidean_finrank]
  push_cast
  rw [mul_div_cancel_left₀ _ (two_ne_zero : (2:ℝ) ≠ 0),
    Real.rpow_neg (by linarith), Real.rpow_natCast, inv_pow]

theorem integrable_radialGaussian_exp_norm_sq (s : ℝ) (hs : s < 1) :
    Integrable (fun x : V => Real.exp (s * ‖x‖^2)) (radialGaussian V) := by
  by_contra h
  have he := radialGaussian_mgf_norm_sq (V := V) s hs
  rw [integral_undef h] at he
  exact (Real.rpow_pos_of_pos (by linarith : 0 < 1-s) _).ne' he.symm

/-- Chernoff's inequality applied to the exact Gaussian norm-square MGF. -/
theorem radialGaussian_norm_sq_chernoff (s r : ℝ) (hs : s < 1) :
    (radialGaussian V).real {x | r ≤ s * ‖x‖^2} ≤
      (1-s) ^ (-(Module.finrank ℝ V / 2 : ℝ)) / Real.exp r := by
  apply (le_div_iff₀ (Real.exp_pos r)).mpr
  have hsub : {x : V | r ≤ s * ‖x‖^2} ⊆
      {x : V | Real.exp r ≤ Real.exp (s * ‖x‖^2)} := by
    intro x hx
    exact Real.exp_le_exp.mpr hx
  calc
    _ = Real.exp r * (radialGaussian V).real {x | r ≤ s * ‖x‖^2} := mul_comm _ _
    _ ≤ Real.exp r * (radialGaussian V).real {x | Real.exp r ≤ Real.exp (s * ‖x‖^2)} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos _).le
    _ ≤ _ := by
      simpa only [radialGaussian_mgf_norm_sq s hs] using
        mul_meas_ge_le_integral_of_nonneg
          (ae_of_all (radialGaussian V) (fun x => (Real.exp_pos (s * ‖x‖^2)).le))
          (integrable_radialGaussian_exp_norm_sq s hs) (Real.exp r)


theorem radialGaussian_complex_norm_sq_chernoff (E : Type*) [Fintype E]
    (s r : ℝ) (hs : s < 1) :
    (radialGaussian (EuclideanSpace ℂ E)).real {x | r ≤ s * ‖x‖^2} ≤
      ((1-s)⁻¹)^Fintype.card E / Real.exp r := by
  have h := radialGaussian_norm_sq_chernoff (V := EuclideanSpace ℂ E) s r hs
  rw [complex_euclidean_finrank] at h
  push_cast at h
  rwa [mul_div_cancel_left₀ _ (two_ne_zero : (2:ℝ) ≠ 0),
    Real.rpow_neg (by linarith), Real.rpow_natCast, ← inv_pow] at h

/-- The exact Gamma upper-tail Chernoff estimate for a standard complex Gaussian. -/
theorem radialGaussian_complex_norm_sq_upper_real (E : Type*) [Fintype E]
    (a : ℝ) (ha : 1 < a) :
    (radialGaussian (EuclideanSpace ℂ E)).real
        {x | a * Fintype.card E ≤ ‖x‖^2} ≤
      (a * Real.exp (1-a))^Fintype.card E := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hs : 1-a⁻¹ < 1 := sub_lt_self _ (inv_pos.mpr ha0)
  have hs0 : 0 ≤ 1-a⁻¹ := by
    have : a⁻¹ ≤ (1 : ℝ) := (inv_le_one₀ ha0).mpr ha.le
    linarith
  have hsub : {x : EuclideanSpace ℂ E | a * Fintype.card E ≤ ‖x‖^2} ⊆
      {x | (a-1)*Fintype.card E ≤ (1-a⁻¹) * ‖x‖^2} := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left hx hs0
    have he : (1-a⁻¹) * (a * (Fintype.card E : ℝ)) =
        (a-1) * Fintype.card E := by field_simp; ring
    rwa [he] at h
  refine (measureReal_mono hsub).trans ?_
  have h := radialGaussian_complex_norm_sq_chernoff E (1-a⁻¹)
    ((a-1)*Fintype.card E) hs
  have he : ((1-(1-a⁻¹))⁻¹)^Fintype.card E /
        Real.exp ((a-1)*Fintype.card E) =
      (a * Real.exp (1-a))^Fintype.card E := by
    rw [sub_sub_cancel, inv_inv, mul_comm (a-1), Real.exp_nat_mul, ← div_pow, div_eq_mul_inv,
      ← Real.exp_neg]
    congr 2
    ring
  rwa [he] at h

/-- A simple Gamma lower-tail estimate. The constant is deliberately uniform
in the lower threshold and adequate for the rectangular-matrix net argument. -/
theorem radialGaussian_complex_norm_sq_lower_real (E : Type*) [Fintype E]
    (d : ℝ) (hd : 0 < d) :
    (radialGaussian (EuclideanSpace ℂ E)).real
        {x | ‖x‖^2 ≤ d * Fintype.card E} ≤
      (Real.exp 1 * d)^Fintype.card E := by
  have hs : -d⁻¹ < 1 := by have := inv_pos.mpr hd; linarith
  have hsub : {x : EuclideanSpace ℂ E | ‖x‖^2 ≤ d * Fintype.card E} ⊆
      {x | -(Fintype.card E : ℝ) ≤ -d⁻¹ * ‖x‖^2} := by
    intro x hx
    have h := mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr (inv_nonneg.mpr hd.le))
    have he : -d⁻¹ * (d * (Fintype.card E : ℝ)) = -(Fintype.card E : ℝ) := by
      field_simp
      ring
    rwa [he] at h
  refine (measureReal_mono hsub).trans ?_
  have h := radialGaussian_complex_norm_sq_chernoff E (-d⁻¹)
    (-(Fintype.card E : ℝ)) hs
  have hden : 0 < 1+d⁻¹ := by positivity
  have hinv : (1+d⁻¹)⁻¹ ≤ d := by
    apply (inv_le_iff_one_le_mul₀' hden).mpr
    have he : (1+d⁻¹)*d = d+1 := by field_simp
    rw [he]
    linarith
  calc
    _ ≤ ((1-(-d⁻¹))⁻¹)^Fintype.card E / Real.exp (-(Fintype.card E : ℝ)) := h
    _ ≤ d^Fintype.card E / Real.exp (-(Fintype.card E : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
      simpa only [sub_neg_eq_add] using
        pow_le_pow_left₀ (inv_nonneg.mpr hden.le) hinv (Fintype.card E)
    _ = (Real.exp 1 * d)^Fintype.card E := by
      rw [Real.exp_neg, div_inv_eq_mul, ← Real.exp_one_pow, ← mul_pow, mul_comm]

theorem radialGaussian_complex_norm_sq_upper (E : Type*) [Fintype E]
    (a : ℝ) (ha : 1 < a) :
    radialGaussian (EuclideanSpace ℂ E) {x | a * Fintype.card E ≤ ‖x‖^2} ≤
      ENNReal.ofReal ((a * Real.exp (1-a))^Fintype.card E) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact radialGaussian_complex_norm_sq_upper_real E a ha

theorem radialGaussian_complex_norm_sq_lower (E : Type*) [Fintype E]
    (d : ℝ) (hd : 0 < d) :
    radialGaussian (EuclideanSpace ℂ E) {x | ‖x‖^2 ≤ d * Fintype.card E} ≤
      ENNReal.ofReal ((Real.exp 1 * d)^Fintype.card E) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact radialGaussian_complex_norm_sq_lower_real E d hd

end ProjectionChannels.GaussConcentration

#print axioms ProjectionChannels.GaussConcentration.radialGaussian_mgf_norm_sq
#print axioms ProjectionChannels.GaussConcentration.radialGaussian_complex_norm_sq_upper
#print axioms ProjectionChannels.GaussConcentration.radialGaussian_complex_norm_sq_lower

