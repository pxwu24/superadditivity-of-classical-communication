import HaarProjections.GaussianMatrixLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

open MeasureTheory GaussianRank Matrix
open scoped NNReal ENNReal RealInnerProductSpace
noncomputable section

namespace ProjectionChannels.GaussConcentration

variable {V U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]

lemma integral_radialGaussian_complex_eq (f : V → ℂ) :
    (∫ x, f x ∂radialGaussian V) =
      ((gaussianMass V : ℝ) : ℂ)⁻¹ *
        ∫ x : V, Complex.exp (- (‖x‖ : ℂ)^2) * f x := by
  rw [radialGaussian, integral_withDensity_eq_integral_toReal_smul
    (measurable_radialDensity V) (Filter.Eventually.of_forall (fun x => by
      simp [radialDensity]))]
  simp only [radialDensity, ENNReal.toReal_ofReal (mul_nonneg
    (inv_nonneg.mpr (gaussianMass_pos V).le) (Real.exp_pos _).le), Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_assoc, integral_const_mul,
    ← Complex.ofReal_pow, ← Complex.ofReal_neg, Complex.ofReal_exp]

/-- The exact complex linear exponential transform of the actual radial
Gaussian, including its characteristic function as a special case. -/
theorem radialGaussian_cexp_inner (c : ℂ) (w : V) :
    (∫ x, Complex.exp (c * ⟪w, x⟫) ∂radialGaussian V) =
      Complex.exp (c^2 * (‖w‖ : ℂ)^2 / 4) := by
  rw [integral_radialGaussian_complex_eq]
  simp_rw [← Complex.exp_add]
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := V) (b := 1) (by norm_num) c w
  simp only [neg_mul, one_mul, div_one, mul_one] at h
  rw [h]
  have hm : (Real.pi : ℂ) ^ ((Module.finrank ℝ V : ℂ) / 2) =
      (gaussianMass V : ℂ) := by
    simp [gaussianMass, Complex.ofReal_cpow Real.pi_pos.le]
  rw [hm, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (gaussianMass_pos V).ne'), one_mul]

theorem radialGaussian_charFun (w : V) :
    charFun (radialGaussian V) w = Complex.exp (- (‖w‖ : ℂ)^2 / 4) := by
  rw [charFun_apply]
  have he : (fun x : V => Complex.exp ((⟪x,w⟫ : ℝ) * Complex.I)) =
      fun x : V => Complex.exp (Complex.I * ⟪w,x⟫) := by
    funext x
    rw [real_inner_comm]
    congr 1
    ring
  rw [he, radialGaussian_cexp_inner]
  simp only [Complex.I_sq, neg_one_mul]

/-- A linear map whose real adjoint preserves norms sends the standard
radial Gaussian to the standard radial Gaussian on its codomain. -/
theorem radialGaussian_map_of_adjoint_isometry (T : V → U) (hT : Measurable T)
    (S : U → V) (hadj : ∀ x y, ⟪T x,y⟫ = ⟪x,S y⟫)
    (hS : ∀ y, ‖S y‖ = ‖y‖) :
    (radialGaussian V).map T = radialGaussian U := by
  letI : IsProbabilityMeasure ((radialGaussian V).map T) :=
    isProbabilityMeasure_map hT.aemeasurable
  apply Measure.ext_of_charFun
  funext y
  rw [charFun_apply, integral_map hT.aemeasurable]
  · simp_rw [hadj]
    change charFun (radialGaussian V) (S y) = charFun (radialGaussian U) y
    rw [radialGaussian_charFun, radialGaussian_charFun, hS]
  · exact (by fun_prop : Continuous (fun z : U => Complex.exp ((⟪z,y⟫ : ℝ) * Complex.I))).aestronglyMeasurable

section MatrixVector

variable {E D : Type*} [Fintype E] [Fintype D] [DecidableEq D]

def matrixVectorAdjoint (v : EuclideanSpace ℂ D) (y : EuclideanSpace ℂ E) :
    EuclideanSpace ℂ (E × D) :=
  (WithLp.equiv 2 ((E × D) → ℂ)).symm (fun ed => y ed.1 * star (v ed.2))

lemma matrixVectorAdjoint_inner (v : EuclideanSpace ℂ D)
    (x : EuclideanSpace ℂ (E × D)) (y : EuclideanSpace ℂ E) :
    ⟪Matrix.toEuclideanLin (matrixCoordinates E D x) v, y⟫ =
      ⟪x, matrixVectorAdjoint v y⟫ := by
  simp only [PiLp.inner_apply, Complex.inner, ← Complex.re_sum]
  congr 1
  change (∑ e : E, y e * star (∑ d : D, x (e,d) * v d)) =
    ∑ ed : E × D, (y ed.1 * star (v ed.2)) * star (x ed)
  simp only [star_sum, StarMul.star_mul, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro d _
  ring

omit [DecidableEq D] in
lemma matrixVectorAdjoint_norm (v : EuclideanSpace ℂ D) (hv : ‖v‖ = 1)
    (y : EuclideanSpace ℂ E) : ‖matrixVectorAdjoint v y‖ = ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hv' : ∑ d : D, ‖v d‖^2 = 1 := by
    rw [← PiLp.norm_sq_eq_of_L2, hv]
    norm_num
  simp only [PiLp.norm_sq_eq_of_L2, matrixVectorAdjoint, WithLp.equiv_symm_pi_apply,
    Fintype.sum_prod_type, norm_mul, norm_star, mul_pow, ← Finset.mul_sum, hv', mul_one]

omit [Fintype E] in
lemma continuous_matrix_vector_apply (v : EuclideanSpace ℂ D) :
    Continuous (fun G : Matrix E D ℂ => Matrix.toEuclideanLin G v) := by
  change Continuous (fun G : Matrix E D ℂ =>
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : E => ℂ)).symm (G *ᵥ v))
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : E => ℂ)).symm.continuous.comp
    (continuous_id.matrix_mulVec continuous_const)

/-- A Gaussian rectangular matrix sends each fixed unit vector to a
standard radial Gaussian vector. This proves the exact finite-dimensional
law used by the net argument. -/
theorem matrixGaussian_unit_vector_law (v : EuclideanSpace ℂ D) (hv : ‖v‖ = 1) :
    (matrixGaussian E D).map (fun G => Matrix.toEuclideanLin G v) =
      radialGaussian (EuclideanSpace ℂ E) := by
  rw [matrixGaussian, Measure.map_map (continuous_matrix_vector_apply v).measurable
    (matrixCoordinates E D).continuous.measurable]
  apply radialGaussian_map_of_adjoint_isometry _
    ((continuous_matrix_vector_apply v).comp (matrixCoordinates E D).continuous).measurable
    (matrixVectorAdjoint v)
  · exact matrixVectorAdjoint_inner v
  · exact matrixVectorAdjoint_norm v hv

end MatrixVector

end ProjectionChannels.GaussConcentration

#print axioms ProjectionChannels.GaussConcentration.radialGaussian_cexp_inner
#print axioms ProjectionChannels.GaussConcentration.radialGaussian_map_of_adjoint_isometry
#print axioms ProjectionChannels.GaussConcentration.matrixGaussian_unit_vector_law
