import StrongConvergence.StrongConvergenceCompressionBounds

/-!
# Deterministic affine spectral enclosure for signed block compressions

For arbitrary positive contractions `P i`, the spectrum of `∑ i, a i • P i`
lies between the sums of the negative and positive coefficient parts. This
gives a sharper affine norm envelope than the triangle bound `|c| + ∑ i, |a i|`.
It is a finite-dimensional enclosure, not the sharp free-law support bound:
in general the limiting Haar support is strictly smaller than this interval.
-/

open Matrix ProjectionChannels
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace StrongConvergence

variable {N K : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
  [Fintype K] [DecidableEq K]

lemma contraction_positive_part_shift {P : Matrix N N ℂ}
    (hP : P.PosSemidef) (hI : (1 - P).PosSemidef) (a : ℝ) :
    (((max a 0 : ℝ) : ℂ) • (1 : Matrix N N ℂ) - (a : ℂ) • P).PosSemidef := by
  by_cases ha : 0 ≤ a
  · simpa only [max_eq_left ha, smul_sub] using posSemidef_real_smul hI a ha
  · have hna : 0 ≤ -a := by linarith
    simpa only [max_eq_right (le_of_not_ge ha), Complex.ofReal_zero, zero_smul,
      zero_sub, Complex.ofReal_neg, neg_smul] using posSemidef_real_smul hP (-a) hna

lemma contraction_negative_part_shift {P : Matrix N N ℂ}
    (hP : P.PosSemidef) (hI : (1 - P).PosSemidef) (a : ℝ) :
    ((a : ℂ) • P - ((min a 0 : ℝ) : ℂ) • (1 : Matrix N N ℂ)).PosSemidef := by
  by_cases ha : 0 ≤ a
  · simpa only [min_eq_right ha, Complex.ofReal_zero, zero_smul, sub_zero] using
      posSemidef_real_smul hP a ha
  · have hna : 0 ≤ -a := by linarith
    simpa only [min_eq_left (le_of_not_ge ha), Complex.ofReal_neg, neg_smul,
      smul_sub, neg_sub, neg_sub_neg] using posSemidef_real_smul hI (-a) hna

/-- The positive coefficient sum is an operator upper bound. -/
theorem blockCompression_positive_part_bound (P : K → Matrix N N ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hI : ∀ i, (1 - P i).PosSemidef) (a : K → ℝ) :
    (((∑ i, max (a i) 0 : ℝ) : ℂ) • (1 : Matrix N N ℂ) -
      blockCompression P a).PosSemidef := by
  have h := posSemidef_finite_sum Finset.univ
    (fun i => ((max (a i) 0 : ℝ) : ℂ) • (1 : Matrix N N ℂ) - (a i : ℂ) • P i)
    (fun i _ => contraction_positive_part_shift (hP i) (hI i) (a i))
  simpa only [Finset.sum_sub_distrib, Complex.ofReal_sum, ← Finset.sum_smul,
    blockCompression] using h

/-- The negative coefficient sum is an operator lower bound. -/
theorem blockCompression_negative_part_bound (P : K → Matrix N N ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hI : ∀ i, (1 - P i).PosSemidef) (a : K → ℝ) :
    (blockCompression P a -
      ((∑ i, min (a i) 0 : ℝ) : ℂ) • (1 : Matrix N N ℂ)).PosSemidef := by
  have h := posSemidef_finite_sum Finset.univ
    (fun i => (a i : ℂ) • P i - ((min (a i) 0 : ℝ) : ℂ) • (1 : Matrix N N ℂ))
    (fun i _ => contraction_negative_part_shift (hP i) (hI i) (a i))
  simpa only [Finset.sum_sub_distrib, Complex.ofReal_sum, ← Finset.sum_smul,
    blockCompression] using h

lemma eigenvalue_ge_of_sub_scalar_posSemidef {M : Matrix N N ℂ}
    (hM : M.IsHermitian) (r : ℝ)
    (h : (M - (r : ℂ) • (1 : Matrix N N ℂ)).PosSemidef) (i : N) :
    r ≤ hM.eigenvalues i := by
  have hq := h.re_dotProduct_nonneg (⇑(hM.eigenvectorBasis i))
  have hn : dotProduct (star ⇑(hM.eigenvectorBasis i)) ⇑(hM.eigenvectorBasis i) =
      (1 : ℂ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hM.eigenvectorBasis.orthonormal.1 i]
    simp
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, hn, smul_eq_mul, mul_one] at hq
  rw [map_sub, show RCLike.re (r : ℂ) = r from rfl, ← hM.eigenvalues_eq i] at hq
  linarith

/-- Every eigenvalue lies in the interval of negative/positive coefficient sums. -/
theorem blockCompression_eigenvalue_interval (P : K → Matrix N N ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hI : ∀ i, (1 - P i).PosSemidef)
    (a : K → ℝ) (j : N) :
    (∑ i, min (a i) 0) ≤
      (blockCompression_isHermitian P (fun i => (hP i).isHermitian) a).eigenvalues j ∧
    (blockCompression_isHermitian P (fun i => (hP i).isHermitian) a).eigenvalues j ≤
      ∑ i, max (a i) 0 := by
  exact ⟨eigenvalue_ge_of_sub_scalar_posSemidef _ _
    (blockCompression_negative_part_bound P hP hI a) j,
    eigenvalue_le_of_shift_posSemidef _ _
    (blockCompression_positive_part_bound P hP hI a) j⟩

/-- An operator-order interval bounds the norm by its largest endpoint magnitude. -/
theorem hermitian_norm_le_interval {M : Matrix N N ℂ} (hM : M.IsHermitian)
    (l u : ℝ) (hl : (M - (l : ℂ) • (1 : Matrix N N ℂ)).PosSemidef)
    (hu : ((u : ℂ) • (1 : Matrix N N ℂ) - M).PosSemidef) :
    ‖M‖ ≤ max |l| |u| := by
  obtain ⟨j, hj⟩ := norm_eq_abs_eigenvalue M hM
  rw [hj]
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left |l| |u|)).trans
      ((neg_abs_le l).trans (eigenvalue_ge_of_sub_scalar_posSemidef hM l hl j))
  · exact (eigenvalue_le_of_shift_posSemidef hM u hu j).trans
      ((le_abs_self u).trans (le_max_right |l| |u|))

/-- The finite-dimensional affine spectral envelope, valid for signed coefficients. -/
theorem blockCompression_affine_norm_envelope (P : K → Matrix N N ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hI : ∀ i, (1 - P i).PosSemidef)
    (a : K → ℝ) (c : ℝ) :
    ‖(c : ℂ) • (1 : Matrix N N ℂ) + blockCompression P a‖ ≤
      max |c + ∑ i, min (a i) 0| |c + ∑ i, max (a i) 0| := by
  have hH : ((c : ℂ) • (1 : Matrix N N ℂ) + blockCompression P a).IsHermitian := by
    apply Matrix.IsHermitian.add _ (blockCompression_isHermitian P
      (fun i => (hP i).isHermitian) a)
    simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  apply hermitian_norm_le_interval hH
  · convert blockCompression_negative_part_bound P hP hI a using 1
    simp only [Complex.ofReal_add, add_smul]
    abel
  · convert blockCompression_positive_part_bound P hP hI a using 1
    simp only [Complex.ofReal_add, add_smul]
    abel

/-- The envelope applies to every orthogonal projection, independently of its law. -/
theorem projection_compression_affine_norm_envelope (P : Matrix (N × K) (N × K) ℂ)
    (hH : P.IsHermitian) (hId : P * P = P) (a : K → ℝ) (c : ℝ) :
    ‖(c : ℂ) • (1 : Matrix N N ℂ) + blockCompression (diagonalBlock P) a‖ ≤
      max |c + ∑ i, min (a i) 0| |c + ∑ i, max (a i) 0| := by
  exact blockCompression_affine_norm_envelope (diagonalBlock P)
    (fun i => (projection_diagonalBlock_contraction P hH hId i).1)
    (fun i => (projection_diagonalBlock_contraction P hH hId i).2) a c

end StrongConvergence

#print axioms StrongConvergence.projection_compression_affine_norm_envelope
