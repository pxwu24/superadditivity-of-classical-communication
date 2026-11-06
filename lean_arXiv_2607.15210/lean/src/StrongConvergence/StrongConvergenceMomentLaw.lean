import StrongConvergence.StrongConvergenceMoments
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Order.ProjIcc

/-! Construction of a compactly supported limit law from convergent moments. -/
open MeasureTheory Filter Set Polynomial CompactlySupported
open scoped Topology BigOperators
noncomputable section
namespace StrongConvergenceMoments

variable (μ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μ n)]
variable {a b : ℝ} (hμ : ∀ n, ∀ᵐ x ∂μ n, x ∈ Icc a b)
variable (mom : ℕ → ℝ)
variable (hmom : ∀ j, Tendsto (fun n => ∫ x, x^j ∂μ n) atTop (𝓝 (mom j)))

include hμ hmom

lemma polynomial_integral_tendsto_moment_functional (P : ℝ[X]) :
    Tendsto (fun n => ∫ x, P.eval x ∂μ n) atTop
      (𝓝 (∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * mom j)) := by
  simp_rw [integral_polynomial_eq_moments (hμ _)]
  exact tendsto_finset_sum _ (fun j _ => tendsto_const_nhds.mul (hmom j))

lemma continuous_integral_cauchy_of_moments (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    CauchySeq (fun n => ∫ x, f x ∂μ n) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn a b f hf (ε/3) (by positivity)
  have hc := (polynomial_integral_tendsto_moment_functional μ hμ mom hmom P).cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε/3) (by positivity)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hpn := integral_difference_le_of_uniform_Icc (hμ n) hf P.continuous.continuousOn
    (fun x hx => by simpa only [abs_sub_comm] using (hP x hx).le)
  have hpm := integral_difference_le_of_uniform_Icc (hμ m) P.continuous.continuousOn hf
    (fun x hx => (hP x hx).le)
  have hnm := hN n hn m hm
  rw [Real.dist_eq] at hnm ⊢
  have ht := abs_add ((∫ x, f x ∂μ n) - ∫ x, P.eval x ∂μ n)
    ((∫ x, P.eval x ∂μ n) - ∫ x, P.eval x ∂μ m)
  have ht' := abs_add
    (((∫ x, f x ∂μ n) - ∫ x, P.eval x ∂μ n) +
     ((∫ x, P.eval x ∂μ n) - ∫ x, P.eval x ∂μ m))
    ((∫ x, P.eval x ∂μ m) - ∫ x, f x ∂μ m)
  simp only [sub_add_sub_cancel] at ht ht'
  linarith

variable (hab : a ≤ b)
include hab

def intervalMomentFunctional : C_c(Icc a b, ℝ) →ₗ[ℝ] ℝ where
  toFun f := limUnder atTop (fun n => ∫ x, f (projIcc a b hab x) ∂μ n)
  map_add' f g := by
    have hf := (continuous_integral_cauchy_of_moments μ hμ mom hmom
      (fun x => f (projIcc a b hab x)) (f.continuous.comp continuous_projIcc).continuousOn).tendsto_limUnder
    have hg := (continuous_integral_cauchy_of_moments μ hμ mom hmom
      (fun x => g (projIcc a b hab x)) (g.continuous.comp continuous_projIcc).continuousOn).tendsto_limUnder
    have hfg := (continuous_integral_cauchy_of_moments μ hμ mom hmom
      (fun x => (f + g) (projIcc a b hab x))
      ((f + g).continuous.comp continuous_projIcc).continuousOn).tendsto_limUnder
    apply tendsto_nhds_unique hfg
    convert hf.add hg using 1
    ext n
    exact integral_add
      (integrable_of_continuousOn_of_ae_mem_Icc (hμ n) (f.continuous.comp continuous_projIcc).continuousOn)
      (integrable_of_continuousOn_of_ae_mem_Icc (hμ n) (g.continuous.comp continuous_projIcc).continuousOn)
  map_smul' c f := by
    have hf := (continuous_integral_cauchy_of_moments μ hμ mom hmom
      (fun x => f (projIcc a b hab x)) (f.continuous.comp continuous_projIcc).continuousOn).tendsto_limUnder
    have hcf := (continuous_integral_cauchy_of_moments μ hμ mom hmom
      (fun x => (c • f) (projIcc a b hab x))
      ((c • f).continuous.comp continuous_projIcc).continuousOn).tendsto_limUnder
    apply tendsto_nhds_unique hcf
    convert tendsto_const_nhds.mul hf using 1
    ext n
    exact integral_const_mul c _

lemma intervalMomentFunctional_tendsto (f : C_c(Icc a b, ℝ)) :
    Tendsto (fun n => ∫ x, f (projIcc a b hab x) ∂μ n) atTop
      (𝓝 (intervalMomentFunctional μ hμ mom hmom hab f)) :=
  (continuous_integral_cauchy_of_moments μ hμ mom hmom _
    (f.continuous.comp continuous_projIcc).continuousOn).tendsto_limUnder

lemma intervalMomentFunctional_nonneg (f : C_c(Icc a b, ℝ)) (hf : 0 ≤ f) :
    0 ≤ intervalMomentFunctional μ hμ mom hmom hab f := by
  apply ge_of_tendsto (intervalMomentFunctional_tendsto μ hμ mom hmom hab f)
  exact Eventually.of_forall fun n => integral_nonneg fun x => hf _


def intervalPower (j : ℕ) : C_c(Icc a b, ℝ) :=
  CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported ⟨fun x => (x : ℝ)^j, by fun_prop⟩

lemma intervalMomentFunctional_power (j : ℕ) :
    intervalMomentFunctional μ hμ mom hmom hab (intervalPower (a := a) (b := b) j) = mom j := by
  apply tendsto_nhds_unique (intervalMomentFunctional_tendsto μ hμ mom hmom hab _)
  convert hmom j using 1
  ext n
  apply integral_congr_ae
  filter_upwards [hμ n] with x hx
  simp [intervalPower, projIcc_of_mem hab hx]

omit hμ hab in
lemma moment_zero : mom 0 = 1 := by
  apply tendsto_nhds_unique (hmom 0)
  simp only [pow_zero, integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

lemma intervalMomentFunctional_one :
    intervalMomentFunctional μ hμ mom hmom hab (intervalPower (a := a) (b := b) 0) = 1 := by
  rw [intervalMomentFunctional_power, moment_zero μ mom hmom]

/-- A common compact support and convergence of every moment construct a probability
measure with precisely those moments. The measure is obtained by the Riesz theorem,
not supplied as an additional hypothesis. -/
theorem exists_compact_probability_of_moments :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ᵐ x ∂ν, x ∈ Icc a b) ∧ ∀ j : ℕ, ∫ x, x^j ∂ν = mom j := by
  let Λ := intervalMomentFunctional μ hμ mom hmom hab
  have hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f := intervalMomentFunctional_nonneg μ hμ mom hmom hab
  let ν₀ := RealRMK.rieszMeasure hΛ
  have h1 : Λ (intervalPower (a := a) (b := b) 0) = 1 :=
    intervalMomentFunctional_one μ hμ mom hmom hab
  have hup : ν₀ Set.univ ≤ 1 := by
    have h := RealRMK.rieszMeasure_le_of_eq_one hΛ
      (f := intervalPower (a := a) (b := b) 0) (by intro x; simp [intervalPower])
      isCompact_univ (by intro x hx; simp [intervalPower])
    simpa only [h1, ENNReal.ofReal_one] using h
  have hlo : 1 ≤ ν₀ Set.univ := by
    have h := RealRMK.le_rieszMeasure_tsupport_subset hΛ
      (f := intervalPower (a := a) (b := b) 0)
      (by intro x; simp [intervalPower]) (Set.subset_univ _)
    simpa only [h1, ENNReal.ofReal_one] using h
  haveI : IsProbabilityMeasure ν₀ := ⟨le_antisymm hup hlo⟩
  let ν := ν₀.map (Subtype.val : Icc a b → ℝ)
  have hval : Measurable (Subtype.val : Icc a b → ℝ) := continuous_subtype_val.measurable
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_map hval.aemeasurable
  refine ⟨ν, inferInstance, ?_, fun j => ?_⟩
  · exact (ae_map_iff hval.aemeasurable measurableSet_Icc).mpr
      (Eventually.of_forall fun x => x.property)
  · rw [show ν = ν₀.map (Subtype.val : Icc a b → ℝ) from rfl,
      integral_map_of_stronglyMeasurable hval (Continuous.stronglyMeasurable (by fun_prop))]
    change (∫ x, intervalPower (a := a) (b := b) j x ∂RealRMK.rieszMeasure hΛ) = mom j
    rw [RealRMK.integral_rieszMeasure hΛ]
    exact intervalMomentFunctional_power μ hμ mom hmom hab j

/-- The constructed law is also the weak limit, tested against every function
continuous on the common compact support. -/
theorem exists_compact_probability_limit_of_moments :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ᵐ x ∂ν, x ∈ Icc a b) ∧
      (∀ j : ℕ, ∫ x, x^j ∂ν = mom j) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Icc a b) →
        Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  obtain ⟨ν, hνprob, hν, hνmom⟩ := exists_compact_probability_of_moments μ hμ mom hmom hab
  letI := hνprob
  refine ⟨ν, hνprob, hν, hνmom, fun f hf => ?_⟩
  exact continuous_integral_tendsto_of_moments μ ν hμ hν
    (fun j => by rw [hνmom j]; exact hmom j) f hf

#print axioms exists_compact_probability_limit_of_moments
end StrongConvergenceMoments
