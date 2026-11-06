import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-! Smooth approximation preserves the Lipschitz constant. This supplies the
mollification step of the Gaussian concentration argument without Rademacher's theorem. -/
open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff Topology NNReal
noncomputable section
namespace ProjectionChannels.GaussConcentration

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The scalar integrand defining convolution with a normalized smooth bump is integrable. -/
lemma normed_bump_mul_sub_integrable (φ : ContDiffBump (0 : V))
    {f : V → ℝ} (hf : Continuous f) (x : V) :
    Integrable (fun z => φ.normed volume z * f (x - z)) volume := by
  exact (φ.continuous_normed.mul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    φ.hasCompactSupport_normed.mul_right

/-- Normalized nonnegative mollification does not enlarge a global Lipschitz constant. -/
theorem lipschitzWith_normed_bump_convolution (φ : ContDiffBump (0 : V))
    {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f : V → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, convolution_lsmul, convolution_lsmul]
  simp only [smul_eq_mul]
  rw [← integral_sub (normed_bump_mul_sub_integrable φ hf.continuous x)
    (normed_bump_mul_sub_integrable φ hf.continuous y)]
  have h := norm_integral_le_of_norm_le
    (φ.integrable_normed.mul_const ((L : ℝ) * dist x y))
    (Filter.Eventually.of_forall (fun z => show
      ‖φ.normed volume z * f (x - z) - φ.normed volume z * f (y - z)‖ ≤
        φ.normed volume z * ((L : ℝ) * dist x y) from by
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      simpa only [← Real.dist_eq, dist_sub_right] using hf.dist_le_mul (x - z) (y - z)))
  simpa only [Real.norm_eq_abs, integral_mul_const, φ.integral_normed, one_mul] using h

/-- Smoothness of the actual normalized convolution, for every finite order and `C^∞`. -/
theorem contDiff_normed_bump_convolution (φ : ContDiffBump (0 : V))
    {f : V → ℝ} (hf : Continuous f) {n : ℕ∞} :
    ContDiff ℝ n (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f : V → ℝ) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

/-- The derivative of the mollification obeys the same Lipschitz bound. -/
theorem norm_fderiv_normed_bump_convolution_le (φ : ContDiffBump (0 : V))
    {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : V) :
    ‖fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f : V → ℝ) x‖ ≤ L :=
  norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_normed_bump_convolution φ hf)

/-- Pointwise approximation at the exact radius of the bump. -/
theorem dist_normed_bump_convolution_le (φ : ContDiffBump (0 : V))
    {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : V) :
    dist ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] f : V → ℝ) x) (f x) ≤
      (L : ℝ) * φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le L.coe_nonneg)

/-- A bounded Lipschitz function admits bounded smooth approximants with the
same derivative bound and a prescribed uniform error. The constant-zero
Lipschitz case is included. -/
theorem exists_smooth_lipschitz_approximation {f : V → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {B ρ : ℝ} (hB : ∀ x, |f x| ≤ B) (hρ : 0 < ρ) :
    ∃ g : V → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith L g ∧
      (∀ x, ‖fderiv ℝ g x‖ ≤ L) ∧ (∀ x, |g x - f x| ≤ (L : ℝ) * ρ) ∧
      (∀ x, |g x| ≤ B + (L : ℝ) * ρ) := by
  let φ : ContDiffBump (0 : V) := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  let g : V → ℝ := φ.normed volume ⋆[lsmul ℝ ℝ, volume] f
  have hgerr (x : V) : |g x - f x| ≤ (L : ℝ) * ρ := by
    simpa only [Real.dist_eq] using dist_normed_bump_convolution_le φ hf x
  refine ⟨g, contDiff_normed_bump_convolution φ hf.continuous,
    lipschitzWith_normed_bump_convolution φ hf,
    norm_fderiv_normed_bump_convolution_le φ hf, hgerr, ?_⟩
  intro x
  calc
    |g x| = |(g x - f x) + f x| := by congr 1; ring
    _ ≤ |g x - f x| + |f x| := abs_add _ _
    _ ≤ (L : ℝ) * ρ + B := add_le_add (hgerr x) (hB x)
    _ = B + (L : ℝ) * ρ := by ring

end ProjectionChannels.GaussConcentration
#print axioms ProjectionChannels.GaussConcentration.exists_smooth_lipschitz_approximation
