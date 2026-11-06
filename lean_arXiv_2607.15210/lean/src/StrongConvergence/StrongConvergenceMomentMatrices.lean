import StrongConvergence.StrongConvergenceMomentMeasures
import Entropy.RevisionMatrixEntropy
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The moment criterion applied to actual finite Hermitian matrices.
Empirical moments are proved to equal normalized traces of powers.
Uniform operator-norm bounds supply the common spectral interval. -/

open MeasureTheory Filter Set Matrix RevisionMatrixEntropy
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergenceMoments

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def empiricalSpectralMeasure (M : Matrix ι ι ℂ) (hM : M.IsHermitian) : Measure ℝ :=
  empiricalMeasure hM.eigenvalues

instance empiricalSpectralMeasure_isProbability (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    IsProbabilityMeasure (empiricalSpectralMeasure M hM) := empiricalMeasure_isProbability _

lemma trace_power_eq_sum_eigenvalues (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (j : ℕ) :
    (Matrix.trace (M^j)).re = ∑ i, (hM.eigenvalues i)^j := by
  have he : M = unitaryConjugateDiagonalHom hM.eigenvectorUnitary
      (fun i => (hM.eigenvalues i:ℂ)) := hM.spectral_theorem
  conv_lhs => rw [he, ← map_pow]
  change (Matrix.trace ((hM.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal ((fun i => (hM.eigenvalues i:ℂ))^j) *
      star (hM.eigenvectorUnitary : Matrix ι ι ℂ))).re = _
  rw [Matrix.trace_mul_cycle, hM.eigenvectorUnitary.prop.1, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp only [Pi.pow_apply, Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re]

lemma empiricalSpectralMeasure_moment (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (j : ℕ) :
    (∫ x, x^j ∂empiricalSpectralMeasure M hM) =
      (1/(Fintype.card ι:ℝ)) * (Matrix.trace (M^j)).re := by
  rw [empiricalSpectralMeasure, integral_empiricalMeasure, trace_power_eq_sum_eigenvalues]

lemma empiricalSpectralMeasure_ae_mem_of_norm_le
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) {R : ℝ} (hR : ‖M‖ ≤ R) :
    ∀ᵐ x ∂empiricalSpectralMeasure M hM, x ∈ Icc (-R) R := by
  apply empiricalMeasure_ae_mem_Icc
  intro i
  have hi : |hM.eigenvalues i| ≤ ‖M‖ := by
    simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem (hM.eigenvalues_mem_spectrum_real i)
  exact abs_le.mp (hi.trans hR)

/-- Convergent normalized traces of all powers and a uniform operator-norm
bound imply actual bounded-continuous empirical spectral convergence. -/
theorem matrix_spectral_tests_tendsto_of_trace_moments
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (M : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hM : ∀ n, (M n).IsHermitian)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {R : ℝ}
    (hbound : ∀ n, ‖M n‖ ≤ R) (hν : ∀ᵐ x ∂ν, x ∈ Icc (-R) R)
    (hmom : ∀ j : ℕ, Tendsto
      (fun n => (1/(d n:ℝ))*(Matrix.trace ((M n)^j)).re)
      atTop (𝓝 (∫ x, x^j ∂ν)))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-R) R)) :
    Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM n).eigenvalues i))
      atTop (𝓝 (∫ x, f x ∂ν)) := by
  letI (n : ℕ) : NeZero (d n) := ⟨(hd n).ne'⟩
  apply empirical_integral_tendsto_of_moments d hd (fun n => (hM n).eigenvalues) ν
    (a := -R) (b := R) _ hν _ f hf
  · intro n i
    have hi : |(hM n).eigenvalues i| ≤ ‖M n‖ := by
      simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem
        ((hM n).eigenvalues_mem_spectrum_real i)
    exact abs_le.mp (hi.trans (hbound n))
  · intro j
    have he : (fun n => (1/(d n:ℝ))*(Matrix.trace ((M n)^j)).re) =
        (fun n => (1/(d n:ℝ))*∑ i, ((hM n).eigenvalues i)^j) := by
      funext n
      rw [trace_power_eq_sum_eigenvalues (M n) (hM n) j]
    rw [← he]
    exact hmom j

/-- Only a countable intersection over moments is needed to obtain one
probability-one event valid simultaneously for every continuous test. -/
theorem ae_matrix_spectral_tests_of_ae_trace_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (M : Ω → (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hM : ∀ ω n, (M ω n).IsHermitian)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {R : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ∀ n, ‖M ω n‖ ≤ R)
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (-R) R)
    (hmom : ∀ j : ℕ, ∀ᵐ ω ∂μ, Tendsto
      (fun n => (1/(d n:ℝ))*(Matrix.trace ((M ω n)^j)).re)
      atTop (𝓝 (∫ x, x^j ∂ν))) :
    ∀ᵐ ω ∂μ, ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-R) R) →
      Tendsto (fun n => (1/(d n:ℝ))*∑ i, f ((hM ω n).eigenvalues i))
        atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hcommon : ∀ᵐ ω ∂μ, ∀ j : ℕ, Tendsto
      (fun n => (1/(d n:ℝ))*(Matrix.trace ((M ω n)^j)).re)
      atTop (𝓝 (∫ x, x^j ∂ν)) := ae_all_iff.mpr hmom
  filter_upwards [hbound, hcommon] with ω hωbound hωmom
  exact fun f hf => matrix_spectral_tests_tendsto_of_trace_moments d hd (M ω) (hM ω)
    ν hωbound hν hωmom f hf

end StrongConvergenceMoments
