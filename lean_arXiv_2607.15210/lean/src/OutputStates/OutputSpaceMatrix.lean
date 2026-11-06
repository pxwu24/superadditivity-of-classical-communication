import RandomCompression.CompressionSpectral

/-!
# Generalized eigenvalue thresholds for locally normalized channels

This file proves the actual matrix cone equivalence used in the support
threshold formula. In particular, the inverse square root normalizer and its
invertibility are derived from positivity of the input marginal.
-/

open scoped BigOperators ComplexOrder
open Matrix
namespace ProjectionChannels
noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [DecidableEq n] [Nonempty n] in
lemma hermitian_sandwich {H D : Matrix n n ℂ}
    (hH : H.IsHermitian) (hD : D.IsHermitian) : (D * H * D).IsHermitian := by
  simpa only [hD.eq] using Matrix.isHermitian_mul_mul_conjTranspose D hH

omit [Nonempty n] in
/-- Congruence by an invertible Hermitian matrix reflects as well as
preserves the positive semidefinite cone. -/
theorem invertible_hermitian_congruence_iff
    (M D : Matrix n n ℂ) (hD : D.IsHermitian) (hunit : IsUnit D) :
    (D * M * D).PosSemidef ↔ M.PosSemidef := by
  have hdet := (Matrix.isUnit_iff_isUnit_det D).mp hunit
  constructor
  · intro h
    have hc := h.mul_mul_conjTranspose_same D⁻¹
    rw [hD.inv.eq] at hc
    have heq : D⁻¹ * (D * M * D) * D⁻¹ = M := by
      rw [Matrix.mul_assoc D M D, ← Matrix.mul_assoc D⁻¹ D (M * D),
        Matrix.nonsing_inv_mul D hdet, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv D hdet, Matrix.mul_one]
    rwa [heq] at hc
  · intro h
    simpa only [hD.eq] using h.mul_mul_conjTranspose_same D

/-- The generalized eigenvalue inequality is equivalent to an inequality
before normalization. This is a theorem about the genuine largest eigenvalue
and the genuine matrix positive cone. -/
theorem normalizer_largest_le_iff
    (A H D : Matrix n n ℂ) (hH : H.IsHermitian) (hD : D.IsHermitian)
    (hunit : IsUnit D) (hnormalize : D * A * D = 1) (z : ℝ) :
    largestEigenvalue (hermitian_sandwich hH hD) ≤ z ↔
      ((z : ℂ) • A - H).PosSemidef := by
  rw [largest_le_iff_shift_posSemidef]
  have heq : (z : ℂ) • (1 : Matrix n n ℂ) - D * H * D =
      D * ((z : ℂ) • A - H) * D := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hnormalize]
  rw [heq]
  exact invertible_hermitian_congruence_iff _ D hD hunit

omit [Nonempty n] in
lemma positive_sqrt_isUnit {A : Matrix n n ℂ} (hA : A.PosDef) :
    IsUnit hA.posSemidef.sqrt := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have h : IsUnit (hA.posSemidef.sqrt.det * hA.posSemidef.sqrt.det) := by
    rw [← Matrix.det_mul, hA.posSemidef.sqrt_mul_self]
    exact (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  exact (IsUnit.mul_iff.mp h).1

omit [Nonempty n] in
lemma inverse_sqrt_normalizes {A : Matrix n n ℂ} (hA : A.PosDef) :
    hA.posSemidef.sqrt⁻¹ * A * hA.posSemidef.sqrt⁻¹ = 1 := by
  let S := hA.posSemidef.sqrt
  change S⁻¹ * A * S⁻¹ = 1
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).mp (positive_sqrt_isUnit hA)
  have heq : S * S = A := hA.posSemidef.sqrt_mul_self
  rw [← heq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
    Matrix.one_mul, Matrix.mul_nonsing_inv _ hdet]

/-- Specialization to exactly the inverse positive square root appearing
in the projection-induced channel. No normalizer identity is assumed. -/
theorem inverse_sqrt_largest_le_iff
    (A H : Matrix n n ℂ) (hA : A.PosDef) (hH : H.IsHermitian) (z : ℝ) :
    largestEigenvalue
      (hermitian_sandwich hH hA.posSemidef.posSemidef_sqrt.isHermitian.inv) ≤ z ↔
      ((z : ℂ) • A - H).PosSemidef := by
  exact normalizer_largest_le_iff A H hA.posSemidef.sqrt⁻¹ hH
    hA.posSemidef.posSemidef_sqrt.isHermitian.inv
    (Matrix.isUnit_nonsing_inv_iff.mpr (positive_sqrt_isUnit hA))
    (inverse_sqrt_normalizes hA) z

omit [Fintype n] [DecidableEq n] [Nonempty n] in
lemma real_scalar_shift_hermitian {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℝ) :
    (H - (z : ℂ) • A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    hH.eq, hA.eq]
  simp

/-- The exact threshold equivalence needed by `concrete_normalized_support_tendsto`:
`λmax(A^{-1/2} H A^{-1/2}) ≤ z` iff `λmax(H-zA) ≤ 0`. -/
theorem inverse_sqrt_threshold
    (A H : Matrix n n ℂ) (hA : A.PosDef) (hH : H.IsHermitian) (z : ℝ) :
    largestEigenvalue
      (hermitian_sandwich hH hA.posSemidef.posSemidef_sqrt.isHermitian.inv) ≤ z ↔
    largestEigenvalue (real_scalar_shift_hermitian hH hA.isHermitian z) ≤ 0 := by
  rw [inverse_sqrt_largest_le_iff A H hA hH z, largest_le_iff_shift_posSemidef]
  simp only [Complex.ofReal_zero, zero_smul, zero_sub, neg_sub]

omit [Fintype n] [DecidableEq n] [Nonempty n] in
/-- The scalar shift of a block compression is the unnormalized pencil
`S(a)-z S(1)`, proved directly from finite sums. -/
lemma blockCompression_sub_constant
    {ι : Type*} [Fintype ι] (P : ι → Matrix n n ℂ) (a : ι → ℝ) (z : ℝ) :
    blockCompression P (fun i => a i - z) =
      blockCompression P a - (z : ℂ) • blockCompression P (fun _ => 1) := by
  simp only [blockCompression, Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib,
    Complex.ofReal_one, one_smul, Finset.smul_sum]

/-- The threshold identity for the exact diagonal-block compression in
the paper. The marginal is the sum of the blocks, and the inverse square
root is built from its positive definiteness. -/
theorem normalized_blockCompression_threshold
    {ι : Type*} [Fintype ι] (P : ι → Matrix n n ℂ)
    (hP : ∀ i, (P i).IsHermitian)
    (hA : (blockCompression P (fun _ => 1)).PosDef)
    (a : ι → ℝ) (z : ℝ) :
    largestEigenvalue (hermitian_sandwich (blockCompression_isHermitian P hP a)
      hA.posSemidef.posSemidef_sqrt.isHermitian.inv) ≤ z ↔
    largestEigenvalue (blockCompression_isHermitian P hP (fun i => a i - z)) ≤ 0 := by
  have heq := blockCompression_sub_constant P a z
  simpa only [heq] using inverse_sqrt_threshold
    (blockCompression P (fun _ => 1)) (blockCompression P a) hA
    (blockCompression_isHermitian P hP a) z

end
end ProjectionChannels
