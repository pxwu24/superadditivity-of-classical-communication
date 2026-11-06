import StrongConvergence.StrongConvergenceMoments
import Mathlib.MeasureTheory.Measure.Dirac

/-! Concrete probability measures associated with finite empirical spectra.
The integral formula and support are derived from finite sums of Dirac
measures, not provided as assumptions. -/

open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
noncomputable section
namespace StrongConvergenceMoments

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def empiricalMeasure (v : ι → ℝ) : Measure ℝ :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (v i)

instance empiricalMeasure_isProbability (v : ι → ℝ) :
    IsProbabilityMeasure (empiricalMeasure v) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finset_sum_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)

lemma integral_empiricalMeasure (v : ι → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂empiricalMeasure v) = (1/(Fintype.card ι:ℝ))*∑ i, f (v i) := by
  rw [empiricalMeasure, integral_smul_measure]
  rw [integral_finset_sum_measure (fun i _ => integrable_dirac)]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, one_div]

lemma empiricalMeasure_ae_mem_Icc (v : ι → ℝ) {a b : ℝ}
    (hv : ∀ i, v i ∈ Icc a b) : ∀ᵐ x ∂empiricalMeasure v, x ∈ Icc a b := by
  apply ae_iff.mpr
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
  have hz : ∀ i, Measure.dirac (v i) {x | ¬x ∈ Icc a b} = 0 := by
    intro i
    have hi : v i ∉ {x | ¬x ∈ Icc a b} := fun h => h (hv i)
    rw [Measure.dirac_apply, Set.indicator_of_not_mem hi]
  simp only [hz, Finset.sum_const_zero, mul_zero]

/-- The usual empirical-spectral test convergence follows from convergence
of normalized finite power sums and a fixed support interval. -/
theorem empirical_integral_tendsto_of_moments
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (v : (n : ℕ) → Fin (d n) → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a b : ℝ} (hv : ∀ n i, v n i ∈ Icc a b)
    (hν : ∀ᵐ x ∂ν, x ∈ Icc a b)
    (hmom : ∀ j : ℕ, Tendsto
      (fun n => (1/(d n:ℝ))*∑ i, (v n i)^j) atTop (𝓝 (∫ x, x^j ∂ν)))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => (1/(d n:ℝ))*∑ i, f (v n i)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  letI (n : ℕ) : NeZero (d n) := ⟨(hd n).ne'⟩
  have h := continuous_integral_tendsto_of_moments (fun n => empiricalMeasure (v n)) ν
    (fun n => empiricalMeasure_ae_mem_Icc (v n) (hv n)) hν
    (fun j => by simpa only [integral_empiricalMeasure, Fintype.card_fin] using hmom j) f hf
  simpa only [integral_empiricalMeasure, Fintype.card_fin] using h

end StrongConvergenceMoments
