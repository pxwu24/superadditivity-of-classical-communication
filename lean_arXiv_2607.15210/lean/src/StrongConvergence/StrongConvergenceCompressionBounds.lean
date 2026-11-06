import StrongConvergence.StrongConvergenceNorm
import RandomCompression.RevisionFullBlockInput

/-! Uniform deterministic compact spectral bounds for actual projection
compressions, including arbitrary fixed unitary changes of block basis. -/
open Matrix ProjectionChannels
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace StrongConvergence

variable {N K : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
  [Fintype K] [DecidableEq K]

lemma positive_contraction_norm_le_one (P : Matrix N N ℂ)
    (hP : P.PosSemidef) (hI : (1-P).PosSemidef) : ‖P‖ ≤ 1 := by
  have he := norm_shift_eq_largest hP.isHermitian 0 (by simpa using hP)
  simp only [Complex.ofReal_zero,zero_smul,zero_add] at he
  rw [he]
  apply (largest_le_iff hP.isHermitian 1).mpr
  intro i
  exact eigenvalue_le_of_shift_posSemidef hP.isHermitian 1 (by simpa using hI) i

theorem blockCompression_norm_le (P : K → Matrix N N ℂ)
    (hP : ∀ i,(P i).PosSemidef) (hI : ∀ i,(1-P i).PosSemidef) (a : K → ℝ) :
    ‖blockCompression P a‖ ≤ ∑ i, |a i| := by
  rw [blockCompression]
  calc
    _ ≤ ∑ i, ‖(a i:ℂ) • P i‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (positive_contraction_norm_le_one (P i) (hP i) (hI i))

/-- The empirical spectra of every projected block compression lie in one
fixed compact interval, independently of input dimension and sample. -/
theorem projection_compression_norm_le (P : Matrix (N×K) (N×K) ℂ)
    (hH : P.IsHermitian) (hId : P*P=P) (a : K → ℝ) :
    ‖blockCompression (diagonalBlock P) a‖ ≤ ∑ i, |a i| := by
  apply blockCompression_norm_le
  · intro i
    exact (projection_diagonalBlock_contraction P hH hId i).1
  · intro i
    exact (projection_diagonalBlock_contraction P hH hId i).2

#print axioms projection_compression_norm_le
end StrongConvergence
