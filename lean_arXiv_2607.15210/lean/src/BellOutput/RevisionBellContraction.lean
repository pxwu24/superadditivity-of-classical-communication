import OutputStates.RevisionOutputStates
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! # Uniform contraction for the locally normalized block map

The proof uses genuine output density matrices and the exact Choi pairing.
All norms below are the Euclidean operator matrix norm.
-/
open Matrix PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped BigOperators ComplexOrder Matrix.L2OpNorm
namespace BellLimitVerification
noncomputable section
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]

lemma largestEigenvalue_le_opNorm {H : Matrix B B ℂ} (hH : H.IsHermitian) :
    largestEigenvalue hH ≤ ‖H‖ := by
  apply (largest_le_iff hH _).mpr
  intro i
  have h := spectrum.norm_le_norm_of_mem (hH.eigenvalues_mem_spectrum_real i)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)

lemma density_expectation_abs_le_opNorm {H σ : Matrix B B ℂ}
    (hH : H.IsHermitian) (hσ : σ ∈ densityMatrices B) :
    |(Matrix.trace (H*σ)).re| ≤ ‖H‖ := by
  have hu := (density_expectation_le hH hσ).trans (largestEigenvalue_le_opNorm hH)
  have hl := (density_expectation_le hH.neg hσ).trans (largestEigenvalue_le_opNorm hH.neg)
  simp only [Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re, norm_neg] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- Every eigenvalue of the normalized adjoint is bounded uniformly by the
operator norm of the original Hermitian test matrix. Neither positivity nor
normalization of the output state is an extra premise: both are derived. -/
theorem normalized_contraction_eigenvalue_bound
    {P : Matrix (A × B) (A × B) ℂ} (hP : P.PosSemidef)
    (D : Matrix A A ℂ) (hD : D.IsHermitian)
    (hn : D * traceB P * D = 1)
    (H : Matrix B B ℂ) (hH : H.IsHermitian) (i : A) :
    |(hermitian_sandwich (contraction_isHermitian hP.isHermitian hH) hD).eigenvalues i| ≤ ‖H‖ := by
  let C := D * contraction P H * D
  let hC : C.IsHermitian := hermitian_sandwich (contraction_isHermitian hP.isHermitian hH) hD
  let ρ := eigenstate C hC i
  have hρ : ρ ∈ densityMatrices A := ⟨eigenstate_posSemidef C hC i, eigenstate_trace C hC i⟩
  let σ := normalizedOutput P D ρ.transpose
  have hσ : σ ∈ densityMatrices B := by
    refine ⟨normalizedOutput_posSemidef hP D hD hρ.1.transpose, ?_⟩
    rw [normalizedOutput_trace P D hn, Matrix.trace_transpose, hρ.2]
  have hpair : (Matrix.trace (H*σ)).re = hC.eigenvalues i := by
    dsimp [σ]
    rw [normalizedOutput_pairing, Matrix.transpose_transpose]
    exact eigenstate_expectation C hC i
  have h := density_expectation_abs_le_opNorm hH hσ
  rwa [hpair] at h

local instance contractionMatrixCStarAlgebra : CStarAlgebra (Matrix A A ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance
  norm_mul_self_le := CStarRing.norm_mul_self_le

/-- The full Hermitian operator-norm contraction used in Appendix A. -/
theorem normalized_contraction_opNorm_le
    {P : Matrix (A × B) (A × B) ℂ} (hP : P.PosSemidef)
    (D : Matrix A A ℂ) (hD : D.IsHermitian)
    (hn : D * traceB P * D = 1)
    (H : Matrix B B ℂ) (hH : H.IsHermitian) :
    ‖D * contraction P H * D‖ ≤ ‖H‖ := by
  let C := D * contraction P H * D
  let hC : C.IsHermitian := hermitian_sandwich (contraction_isHermitian hP.isHermitian hH) hD
  have heq : cfc (id : ℝ → ℝ) C = C := cfc_id ℝ C hC.isSelfAdjoint
  change ‖C‖ ≤ ‖H‖
  rw [← heq]
  apply norm_cfc_le (norm_nonneg H)
  intro x hx
  obtain ⟨i, rfl⟩ := hC.eigenvalues_eq_spectrum_real ▸ hx
  simpa only [id_eq, Real.norm_eq_abs] using
    normalized_contraction_eigenvalue_bound hP D hD hn H hH i

end
end BellLimitVerification
