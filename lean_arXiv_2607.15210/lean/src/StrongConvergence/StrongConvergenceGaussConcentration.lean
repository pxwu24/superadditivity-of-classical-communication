import StrongConvergence.StrongConvergenceGaussMGF
import StrongConvergence.StrongConvergenceGaussRotation
import StrongConvergence.StrongConvergenceGaussMollify
import HaarProjections.GaussianRadial
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

open MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
namespace ProjectionChannels.GaussConcentration

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The rotation path used in Pisier's Gaussian interpolation identity. -/
def rotationPath (x y : V) (θ : ℝ) : V := Real.sin θ • x + Real.cos θ • y

def rotationVelocity (x y : V) (θ : ℝ) : V := Real.cos θ • x - Real.sin θ • y

lemma rotationPath_hasDerivAt (x y : V) (θ : ℝ) :
    HasDerivAt (rotationPath x y) (rotationVelocity x y θ) θ := by
  simpa only [rotationPath, rotationVelocity, sub_eq_add_neg, neg_smul] using
    ((Real.hasDerivAt_sin θ).smul_const x).add ((Real.hasDerivAt_cos θ).smul_const y)

/-- The deterministic path identity. No Gaussian or concentration hypothesis is used. -/
theorem pisier_rotation_integral {f : V → ℝ} (hf : ContDiff ℝ 1 f) (x y : V) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2),
      fderiv ℝ f (rotationPath x y θ) (rotationVelocity x y θ)) = f x - f y := by
  have hd (θ : ℝ) : HasDerivAt (fun θ => f (rotationPath x y θ))
      (fderiv ℝ f (rotationPath x y θ) (rotationVelocity x y θ)) θ :=
    ((hf.differentiable le_rfl) _).hasFDerivAt.comp_hasDerivAt θ
      (rotationPath_hasDerivAt x y θ)
  have hc : Continuous (fun θ =>
      fderiv ℝ f (rotationPath x y θ) (rotationVelocity x y θ)) := by
    have hp : Continuous (rotationPath x y) := by unfold rotationPath; fun_prop
    have hv : Continuous (rotationVelocity x y) := by unfold rotationVelocity; fun_prop
    exact (hf.continuous_fderiv_apply le_rfl).comp (hp.prodMk hv)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hd θ) (hc.intervalIntegrable 0 (Real.pi / 2))
  simpa [rotationPath] using h

/-- Jensen's inequality for the uniform probability law on a nondegenerate interval. -/
theorem exp_interval_average_le {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ} (hab : a < b) :
    Real.exp ((b - a)⁻¹ * ∫ θ in a..b, g θ) ≤
      (b - a)⁻¹ * ∫ θ in a..b, Real.exp (g θ) := by
  have h0 : volume (Set.Ioc a b) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  have hfin : volume (Set.Ioc a b) ≠ ⊤ := by simp [Real.volume_Ioc]
  have h := convexOn_exp.map_set_average_le Real.continuous_exp.continuousOn
    isClosed_univ h0 hfin (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hg.intervalIntegrable a b).1 ((Real.continuous_exp.comp hg).intervalIntegrable a b).1
  simpa only [setAverage_eq, Real.volume_real_Ioc_of_le hab.le,
    smul_eq_mul, ← intervalIntegral.integral_of_le hab.le, Function.comp_def] using h

/-- Pointwise exponential Pisier interpolation, before Gaussian averaging. -/
theorem pisier_exp_difference_le {f : V → ℝ} (hf : ContDiff ℝ 1 f)
    (x y : V) (ell : ℝ) :
    Real.exp (ell * (f x - f y)) ≤ (Real.pi / 2)⁻¹ *
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp ((ell * (Real.pi / 2)) *
          fderiv ℝ f (rotationPath x y θ) (rotationVelocity x y θ)) := by
  have hp : Continuous (rotationPath x y) := by unfold rotationPath; fun_prop
  have hv : Continuous (rotationVelocity x y) := by unfold rotationVelocity; fun_prop
  have hd : Continuous (fun θ =>
      fderiv ℝ f (rotationPath x y θ) (rotationVelocity x y θ)) :=
    (hf.continuous_fderiv_apply le_rfl).comp (hp.prodMk hv)
  have h := exp_interval_average_le ((show Continuous (fun _ : ℝ => ell * (Real.pi / 2)) from continuous_const).mul hd)
    (show 0 < Real.pi / 2 by positivity)
  rw [sub_zero, intervalIntegral.integral_const_mul, pisier_rotation_integral hf x y] at h
  have heq : (Real.pi / 2)⁻¹ * (ell * (Real.pi / 2) * (f x - f y)) =
      ell * (f x - f y) := by field_simp; ring
  simpa only [heq] using h

section Gaussian
variable [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
open GaussianRank

lemma radialGaussian_lintegral_functional (c : ℝ) (L : V →L[ℝ] ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (c * L x)) ∂radialGaussian V) =
      ENNReal.ofReal (Real.exp (c ^ 2 * ‖L‖ ^ 2 / 4)) := by
  have h := radialGaussian_lintegral_exp_inner c ((InnerProductSpace.toDual ℝ V).symm L)
  simpa only [InnerProductSpace.toDual_symm_apply, LinearIsometryEquiv.norm_map] using h

lemma derivative_gaussian_lintegral_le {f : V → ℝ} (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (c : ℝ) :
    (∫⁻ p : V × V, ENNReal.ofReal (Real.exp (c * fderiv ℝ f p.1 p.2))
      ∂(radialGaussian V).prod (radialGaussian V)) ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * (L : ℝ) ^ 2 / 4)) := by
  have hm : Measurable (fun p : V × V =>
      ENNReal.ofReal (Real.exp (c * fderiv ℝ f p.1 p.2))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul
        (hf.continuous_fderiv_apply le_rfl))).measurable
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [radialGaussian_lintegral_functional]
  calc
    _ ≤ ∫⁻ _x : V, ENNReal.ofReal (Real.exp (c ^ 2 * (L : ℝ) ^ 2 / 4))
        ∂radialGaussian V := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      gcongr
      exact hL x
    _ = _ := by simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma pisier_exp_difference_lintegral_le {f : V → ℝ} (hf : ContDiff ℝ 1 f)
    (x y : V) (ell : ℝ) :
    ENNReal.ofReal (Real.exp (ell * (f x - f y))) ≤ ENNReal.ofReal ((Real.pi / 2)⁻¹) *
      ∫⁻ θ in Set.Ioc (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal (Real.exp ((ell * (Real.pi / 2)) *
          fderiv ℝ f (rotationPath x y θ) (rotationVelocity x y θ))) := by
  have hp : Continuous (rotationPath x y) := by unfold rotationPath; fun_prop
  have hv : Continuous (rotationVelocity x y) := by unfold rotationVelocity; fun_prop
  have hd : Continuous (fun θ =>
      fderiv ℝ f (rotationPath x y θ) (rotationVelocity x y θ)) :=
    (hf.continuous_fderiv_apply le_rfl).comp (hp.prodMk hv)
  have he : Continuous (fun θ => Real.exp ((ell * (Real.pi / 2)) *
      fderiv ℝ f (rotationPath x y θ) (rotationVelocity x y θ))) :=
    Real.continuous_exp.comp ((show Continuous (fun _ : ℝ => ell * (Real.pi / 2))
      from continuous_const).mul hd)
  have h := ENNReal.ofReal_le_ofReal (pisier_exp_difference_le hf x y ell)
  rw [ENNReal.ofReal_mul (by positivity), intervalIntegral.integral_of_le (by positivity)] at h
  rw [ofReal_integral_eq_lintegral_ofReal (he.intervalIntegrable 0 (Real.pi / 2)).1
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))] at h
  exact h

/-- Dimension-free symmetrized Gaussian exponential bound, obtained by
rotation interpolation and exact Gaussian integration. -/
theorem radialGaussian_double_exp_difference_le {f : V → ℝ} (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (ell : ℝ) :
    (∫⁻ p : V × V, ENNReal.ofReal (Real.exp (ell * (f p.1 - f p.2)))
      ∂(radialGaussian V).prod (radialGaussian V)) ≤
      ENNReal.ofReal (Real.exp ((ell * (Real.pi / 2)) ^ 2 * (L : ℝ) ^ 2 / 4)) := by
  let T : ℝ := Real.pi / 2
  let c : ℝ := ell * T
  let F : ℝ → (V × V) → ℝ≥0∞ := fun θ p =>
    ENNReal.ofReal (Real.exp (c *
      fderiv ℝ f (rotationPath p.1 p.2 θ) (rotationVelocity p.1 p.2 θ)))
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (c ^ 2 * (L : ℝ) ^ 2 / 4))
  have hm : Measurable (fun q : (V × V) × ℝ => F q.2 q.1) := by
    have hp : Continuous (fun q : (V × V) × ℝ => rotationPath q.1.1 q.1.2 q.2) := by
      unfold rotationPath; fun_prop
    have hv : Continuous (fun q : (V × V) × ℝ => rotationVelocity q.1.1 q.1.2 q.2) := by
      unfold rotationVelocity; fun_prop
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      ((show Continuous (fun _ : (V × V) × ℝ => c) from continuous_const).mul
        ((hf.continuous_fderiv_apply le_rfl).comp (hp.prodMk hv)))).measurable
  have hrot (θ : ℝ) :
      (∫⁻ p : V × V, F θ p ∂(radialGaussian V).prod (radialGaussian V)) ≤ C := by
    have hg : Measurable (fun p : V × V => ENNReal.ofReal (Real.exp (c * fderiv ℝ f p.1 p.2))) :=
      ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
        ((show Continuous (fun _ : V × V => c) from continuous_const).mul
          (hf.continuous_fderiv_apply le_rfl))).measurable
    have hr := (gaussianRotation_measurePreserving (V := V) θ).lintegral_comp hg
    have hid : (∫⁻ p : V × V, F θ p ∂(radialGaussian V).prod (radialGaussian V)) =
        ∫⁻ p : V × V, ENNReal.ofReal (Real.exp (c * fderiv ℝ f p.1 p.2))
          ∂(radialGaussian V).prod (radialGaussian V) := by
      simpa only [gaussianRotation_apply, F, rotationPath, rotationVelocity] using hr
    rw [hid]
    exact derivative_gaussian_lintegral_le hf hL c
  have hT : 0 < T := by dsimp [T]; positivity
  calc
    _ ≤ ∫⁻ p : V × V, ENNReal.ofReal (T⁻¹) *
        (∫⁻ θ in Set.Ioc (0 : ℝ) T, F θ p)
          ∂(radialGaussian V).prod (radialGaussian V) := by
      apply lintegral_mono
      intro p
      exact pisier_exp_difference_lintegral_le hf p.1 p.2 ell
    _ = ENNReal.ofReal (T⁻¹) *
        (∫⁻ θ in Set.Ioc (0 : ℝ) T, ∫⁻ p : V × V, F θ p
          ∂(radialGaussian V).prod (radialGaussian V)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_lintegral_swap hm.aemeasurable]
    _ ≤ ENNReal.ofReal (T⁻¹) * (∫⁻ _θ in Set.Ioc (0 : ℝ) T, C) := by
      exact mul_le_mul_left' (lintegral_mono hrot) _
    _ = C := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      calc
        ENNReal.ofReal (T⁻¹) * (C * ENNReal.ofReal T) =
            (ENNReal.ofReal (T⁻¹) * ENNReal.ofReal T) * C := by ac_rfl
        _ = C := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hT.le),
          inv_mul_cancel₀ hT.ne']; simp

lemma integrable_exp_mul_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) (ell : ℝ) :
    Integrable (fun x => Real.exp (ell * f x)) μ := by
  have hmeas : Measurable (fun x => Real.exp (ell * f x)) := by fun_prop
  apply (integrable_const (Real.exp (|ell| * B))).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    ell * f x ≤ |ell * f x| := le_abs_self _
    _ = |ell| * |f x| := abs_mul _ _
    _ ≤ |ell| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg ell)

/-- Smooth bounded Gaussian functions satisfy the dimension-free centered MGF estimate. -/
theorem radialGaussian_centered_mgf_le {f : V → ℝ} (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (ell : ℝ) :
    (∫ x, Real.exp (ell * (f x - ∫ y, f y ∂radialGaussian V)) ∂radialGaussian V) ≤
      Real.exp (ell ^ 2 * Real.pi ^ 2 * (L : ℝ) ^ 2 / 16) := by
  let μ := radialGaussian V
  have hfi : Integrable f μ := by
    apply (integrable_const B).mono' hf.continuous.measurable.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hB x
  have hnegint := integrable_exp_mul_of_abs_le (μ := μ) hf.continuous.measurable hB (-ell)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hfi.const_mul (-ell)) hnegint
  have hcenter : Real.exp (-ell * ∫ y, f y ∂μ) ≤
      ∫ y, Real.exp (-ell * f y) ∂μ := by
    simpa only [integral_const_mul, Function.comp_def] using hj
  have hd := radialGaussian_double_exp_difference_le hf hL ell
  have hdouble : (∫ p : V × V, Real.exp (ell * (f p.1 - f p.2)) ∂μ.prod μ) ≤
      Real.exp ((ell * (Real.pi / 2)) ^ 2 * (L : ℝ) ^ 2 / 4) := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
      (by exact (Real.continuous_exp.comp (continuous_const.mul
        ((hf.continuous.comp continuous_fst).sub
          (hf.continuous.comp continuous_snd)))).aestronglyMeasurable)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hd).trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)
  calc
    _ = Real.exp (-ell * ∫ y, f y ∂μ) * (∫ x, Real.exp (ell * f x) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (∫ y, Real.exp (-ell * f y) ∂μ) * (∫ x, Real.exp (ell * f x) ∂μ) :=
      mul_le_mul_of_nonneg_right hcenter (integral_nonneg (fun _ => (Real.exp_pos _).le))
    _ = ∫ p : V × V, Real.exp (ell * (f p.1 - f p.2)) ∂μ.prod μ := by
      rw [mul_comm, ← integral_prod_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := hdouble
    _ = _ := by congr 1; ring

/-- One-sided Gaussian Chernoff bound with the Pisier constant. -/
theorem radialGaussian_smooth_upper_tail {f : V → ℝ} (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hLpos : 0 < (L : ℝ)) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) {r : ℝ} (hr : 0 ≤ r) :
    (radialGaussian V).real {x | r ≤ f x - ∫ y, f y ∂radialGaussian V} ≤
      Real.exp (-4 * r ^ 2 / (Real.pi ^ 2 * (L : ℝ) ^ 2)) := by
  let μ := radialGaussian V
  let ell : ℝ := 8 * r / (Real.pi ^ 2 * (L : ℝ) ^ 2)
  have hell : 0 ≤ ell := by dsimp [ell]; positivity
  have hX : Measurable (fun x => f x - ∫ y, f y ∂μ) := hf.continuous.measurable.sub measurable_const
  have hXbound (x : V) : |f x - ∫ y, f y ∂μ| ≤ B + |∫ y, f y ∂μ| :=
    (abs_sub (f x) _).trans (add_le_add_right (hB x) _)
  have hint := integrable_exp_mul_of_abs_le (μ := μ) hX hXbound ell
  have htail := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := μ)
    (X := fun x => f x - ∫ y, f y ∂μ) r hell hint
  calc
    _ ≤ Real.exp (-ell * r) *
        (∫ x, Real.exp (ell * (f x - ∫ y, f y ∂μ)) ∂μ) := htail
    _ ≤ Real.exp (-ell * r) *
        Real.exp (ell ^ 2 * Real.pi ^ 2 * (L : ℝ) ^ 2 / 16) :=
      mul_le_mul_of_nonneg_left (radialGaussian_centered_mgf_le hf hL hB ell)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [ell]
      field_simp [hLpos.ne', Real.pi_ne_zero]
      ring

/-- Two-sided smooth Gaussian concentration; `L = 0` is handled separately below. -/
theorem radialGaussian_smooth_tail {f : V → ℝ} (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hLpos : 0 < (L : ℝ)) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) {r : ℝ} (hr : 0 ≤ r) :
    (radialGaussian V).real {x | r ≤ |f x - ∫ y, f y ∂radialGaussian V|} ≤
      2 * Real.exp (-4 * r ^ 2 / (Real.pi ^ 2 * (L : ℝ) ^ 2)) := by
  have hu := radialGaussian_smooth_upper_tail hf hLpos hL hB hr
  have hl := radialGaussian_smooth_upper_tail hf.neg hLpos
    (fun x => by simpa only [fderiv_neg, norm_neg] using hL x)
    (fun x => by simpa only [abs_neg] using hB x) hr
  have he : {x | r ≤ |f x - ∫ y, f y ∂radialGaussian V|} =
      {x | r ≤ f x - ∫ y, f y ∂radialGaussian V} ∪
      {x | r ≤ -f x - ∫ y, -f y ∂radialGaussian V} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, integral_neg, le_abs]
    constructor <;> intro h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [he]
  exact (measureReal_union_le _ _).trans (by linarith)

/-- Bounded Lipschitz Gaussian concentration, obtained from actual smooth
mollification. The dimension does not enter the exponent. -/
theorem radialGaussian_lipschitz_tail {f : V → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hLpos : 0 < (L : ℝ))
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) {r : ℝ} (hr : 0 < r) :
    (radialGaussian V).real {x | r ≤ |f x - ∫ y, f y ∂radialGaussian V|} ≤
      2 * Real.exp (-r ^ 2 / (Real.pi ^ 2 * (L : ℝ) ^ 2)) := by
  let μ := radialGaussian V
  let ρ : ℝ := r / (4 * (L : ℝ))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨g, hgs, hglip, hgd, happrox, hgb⟩ :=
    exists_smooth_lipschitz_approximation hf hB hρ
  have herr : (L : ℝ) * ρ = r / 4 := by dsimp [ρ]; field_simp; ring
  have ha (x : V) : |g x - f x| ≤ r / 4 := by simpa only [herr] using happrox x
  have hfi : Integrable f μ := by
    apply (integrable_const B).mono' hf.continuous.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hB x
  have hgi : Integrable g μ := by
    apply (integrable_const (B + (L : ℝ) * ρ)).mono' hglip.continuous.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hgb x
  have hmean : |(∫ y, g y ∂μ) - ∫ y, f y ∂μ| ≤ r / 4 := by
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (fun x => show ‖g x - f x‖ ≤ r / 4 from by
        simpa only [Real.norm_eq_abs] using ha x))
    rw [integral_sub hgi hfi] at h
    simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using h
  have hsub : {x | r ≤ |f x - ∫ y, f y ∂μ|} ⊆
      {x | r / 2 ≤ |g x - ∫ y, g y ∂μ|} := by
    intro x hx
    have htriangle : |f x - ∫ y, f y ∂μ| ≤
        |g x - f x| + |g x - ∫ y, g y ∂μ| +
          |(∫ y, g y ∂μ) - ∫ y, f y ∂μ| := by
      calc
        _ = |(f x - g x) + (g x - ∫ y, g y ∂μ) +
            ((∫ y, g y ∂μ) - ∫ y, f y ∂μ)| := by congr 1; ring
        _ ≤ |(f x - g x) + (g x - ∫ y, g y ∂μ)| +
            |(∫ y, g y ∂μ) - ∫ y, f y ∂μ| := abs_add _ _
        _ ≤ (|f x - g x| + |g x - ∫ y, g y ∂μ|) +
            |(∫ y, g y ∂μ) - ∫ y, f y ∂μ| :=
          add_le_add_right (abs_add _ _) _
        _ = _ := by rw [abs_sub_comm (f x) (g x)]
    have hax := ha x
    dsimp only [Set.mem_setOf_eq] at hx ⊢
    linarith
  have hsmooth := radialGaussian_smooth_tail (hgs.of_le (by norm_num)) hLpos hgd hgb
    (show 0 ≤ r / 2 by positivity)
  calc
    _ ≤ μ.real {x | r / 2 ≤ |g x - ∫ y, g y ∂μ|} := measureReal_mono hsub
    _ ≤ 2 * Real.exp (-4 * (r / 2) ^ 2 / (Real.pi ^ 2 * (L : ℝ) ^ 2)) := hsmooth
    _ = _ := by congr 2; ring

/-- Zero Lipschitz constant gives an exactly constant observable and no positive-radius tail. -/
theorem radialGaussian_zero_lipschitz_tail {f : V → ℝ} (hf : LipschitzWith 0 f)
    {r : ℝ} (hr : 0 < r) :
    (radialGaussian V).real {x | r ≤ |f x - ∫ y, f y ∂radialGaussian V|} = 0 := by
  have hconst (x : V) : f x = f 0 := by
    have h := hf.dist_le_mul x 0
    simp only [NNReal.coe_zero, zero_mul, dist_le_zero] at h
    exact h
  have hmean : (∫ y, f y ∂radialGaussian V) = f 0 :=
    integral_eq_const (Filter.Eventually.of_forall hconst)
  have he : {x | r ≤ |f x - ∫ y, f y ∂radialGaussian V|} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, hconst x, hmean,
      sub_self, abs_zero, not_le.mpr hr]
  rw [he]
  simp

end Gaussian

end ProjectionChannels.GaussConcentration
#print axioms ProjectionChannels.GaussConcentration.pisier_rotation_integral

#print axioms ProjectionChannels.GaussConcentration.pisier_exp_difference_le

#print axioms ProjectionChannels.GaussConcentration.radialGaussian_double_exp_difference_le

#print axioms ProjectionChannels.GaussConcentration.radialGaussian_centered_mgf_le

#print axioms ProjectionChannels.GaussConcentration.radialGaussian_smooth_tail

#print axioms ProjectionChannels.GaussConcentration.radialGaussian_lipschitz_tail
#print axioms ProjectionChannels.GaussConcentration.radialGaussian_zero_lipschitz_tail
