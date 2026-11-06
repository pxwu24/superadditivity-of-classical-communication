import Preliminaries.PreliminariesMatrix
import Preliminaries.PreliminariesAnalysis
import Mathlib.LinearAlgebra.Matrix.Spectrum

open scoped BigOperators ComplexOrder
open Matrix

namespace ProjectionChannels

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The actual largest eigenvalue of a finite-dimensional Hermitian matrix. -/
def largestEigenvalue {M : Matrix n n ℂ} (hM : M.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hM.eigenvalues

lemma eigenvalue_le_largest {M : Matrix n n ℂ} (hM : M.IsHermitian) (i : n) :
    hM.eigenvalues i ≤ largestEigenvalue hM := by
  exact Finset.le_sup' _ (Finset.mem_univ i)

lemma largest_le_iff {M : Matrix n n ℂ} (hM : M.IsHermitian) (r : ℝ) :
    largestEigenvalue hM ≤ r ↔ ∀ i, hM.eigenvalues i ≤ r := by
  simp [largestEigenvalue, Finset.sup'_le_iff]

lemma scalar_shift_spectral {M : Matrix n n ℂ} (hM : M.IsHermitian) (r : ℝ) :
    (r : ℂ) • (1 : Matrix n n ℂ) - M =
      (hM.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((r - hM.eigenvalues i : ℝ) : ℂ)) *
      (hM.eigenvectorUnitary : Matrix n n ℂ).conjTranspose := by
  have hd : Matrix.diagonal (fun i => ((r - hM.eigenvalues i : ℝ) : ℂ)) =
      (r : ℂ) • (1 : Matrix n n ℂ) -
      Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]
  have hU : (hM.eigenvectorUnitary : Matrix n n ℂ) *
      (hM.eigenvectorUnitary : Matrix n n ℂ).conjTranspose = 1 := by
    exact (Matrix.mem_unitaryGroup_iff).mp hM.eigenvectorUnitary.2
  rw [hU]
  congr 1
  exact hM.spectral_theorem

lemma eigenvalue_le_of_shift_posSemidef {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (r : ℝ)
    (h : ((r : ℂ) • (1 : Matrix n n ℂ) - M).PosSemidef) (i : n) :
    hM.eigenvalues i ≤ r := by
  have hq := h.re_dotProduct_nonneg (⇑(hM.eigenvectorBasis i))
  have hn : dotProduct (star ⇑(hM.eigenvectorBasis i)) ⇑(hM.eigenvectorBasis i) = (1 : ℂ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hM.eigenvectorBasis.orthonormal.1 i]
    simp
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, hn, smul_eq_mul, mul_one] at hq
  have hr : RCLike.re (r : ℂ) = r := rfl
  rw [map_sub, hr, ← hM.eigenvalues_eq i] at hq
  linarith

/-- Characterization of the largest eigenvalue by the positive cone. -/
theorem largest_le_iff_shift_posSemidef {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (r : ℝ) :
    largestEigenvalue hM ≤ r ↔ ((r : ℂ) • (1 : Matrix n n ℂ) - M).PosSemidef := by
  constructor
  · intro h
    rw [scalar_shift_spectral hM r]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ ((r - hM.eigenvalues i : ℝ) : ℂ)
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr ((largest_le_iff hM r).mp h i))
  · intro h
    exact (largest_le_iff hM r).mpr (eigenvalue_le_of_shift_posSemidef hM r h)


lemma posSemidef_real_smul {M : Matrix n n ℂ} (hM : M.PosSemidef)
    (r : ℝ) (hr : 0 ≤ r) : ((r : ℂ) • M).PosSemidef := by
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hM.1.eq]
    simp
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (Complex.zero_le_real.mpr hr) (hM.2 x)

lemma posSemidef_finite_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix n n ℂ)
    (hM : ∀ i ∈ s, (M i).PosSemidef) : (∑ i ∈ s, M i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hM i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hM j (Finset.mem_insert_of_mem hj)))

lemma contraction_scalar_shift {P : Matrix n n ℂ}
    (hP : P.PosSemidef) (hIP : (1 - P).PosSemidef) (r : ℝ) :
    ((|r| : ℝ) : ℂ) • (1 : Matrix n n ℂ) - (r : ℂ) • P |>.PosSemidef := by
  by_cases hr : 0 ≤ r
  · simpa [abs_of_nonneg hr, smul_sub] using posSemidef_real_smul hIP r hr
  · have hr' : 0 ≤ -r := by linarith
    have h := (posSemidef_real_smul (Matrix.PosSemidef.one :
      (1 : Matrix n n ℂ).PosSemidef) (-r) hr').add (posSemidef_real_smul hP (-r) hr')
    simpa [abs_of_neg (lt_of_not_ge hr), neg_smul, sub_eq_add_neg] using h

lemma largest_compare {M N : Matrix n n ℂ}
    (hM : M.IsHermitian) (hN : N.IsHermitian) (r : ℝ)
    (hD : ((r : ℂ) • (1 : Matrix n n ℂ) - (M - N)).PosSemidef) :
    largestEigenvalue hM ≤ largestEigenvalue hN + r := by
  apply (largest_le_iff_shift_posSemidef hM _).mpr
  have h := hD.add ((largest_le_iff_shift_posSemidef hN _).mp le_rfl)
  convert h using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_add]
  ring

variable {ι : Type*} [Fintype ι]

/-- The diagonal-block compression with real coefficients. -/
def blockCompression (P : ι → Matrix n n ℂ) (a : ι → ℝ) : Matrix n n ℂ :=
  ∑ i, (a i : ℂ) • P i

lemma blockCompression_isHermitian (P : ι → Matrix n n ℂ)
    (hP : ∀ i, (P i).IsHermitian) (a : ι → ℝ) :
    (blockCompression P a).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp only [blockCompression, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp [hP i |>.eq]

lemma blockCompression_shift (P : ι → Matrix n n ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hIP : ∀ i, (1 - P i).PosSemidef)
    (a b : ι → ℝ) :
    (((∑ i, |a i - b i| : ℝ) : ℂ) • (1 : Matrix n n ℂ) -
      (blockCompression P a - blockCompression P b)).PosSemidef := by
  have h := posSemidef_finite_sum Finset.univ
    (fun i => ((|a i - b i| : ℝ) : ℂ) • (1 : Matrix n n ℂ) -
      ((a i - b i : ℝ) : ℂ) • P i)
    (fun i _ => contraction_scalar_shift (hP i) (hIP i) (a i - b i))
  simpa only [Finset.sum_sub_distrib, Complex.ofReal_sum, Complex.ofReal_sub,
    sub_smul, ← Finset.sum_smul, blockCompression] using h

/-- The largest eigenvalue in the manuscript is 1-Lipschitz for the ℓ¹
coefficient distance, proved from the actual positive diagonal blocks. -/
theorem blockCompression_largest_lipschitz (P : ι → Matrix n n ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hIP : ∀ i, (1 - P i).PosSemidef)
    (a b : ι → ℝ) :
    |largestEigenvalue (blockCompression_isHermitian P (fun i => (hP i).1) a) -
      largestEigenvalue (blockCompression_isHermitian P (fun i => (hP i).1) b)|
      ≤ ∑ i, |a i - b i| := by
  have hab := largest_compare
    (blockCompression_isHermitian P (fun i => (hP i).1) a)
    (blockCompression_isHermitian P (fun i => (hP i).1) b) _
    (blockCompression_shift P hP hIP a b)
  have hba := largest_compare
    (blockCompression_isHermitian P (fun i => (hP i).1) b)
    (blockCompression_isHermitian P (fun i => (hP i).1) a) _
    (blockCompression_shift P hP hIP b a)
  have heq : (∑ i, |b i - a i|) = ∑ i, |a i - b i| := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_sub_comm _ _
  rw [heq] at hba
  exact abs_le.mpr ⟨by linarith, by linarith⟩


lemma projection_posSemidef {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (hId : M * M = M) : M.PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose M
  simpa only [hM.eq, hId] using h

lemma projection_complement_posSemidef {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (hId : M * M = M) : (1 - M).PosSemidef := by
  apply projection_posSemidef (Matrix.isHermitian_one.sub hM)
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hId]
  abel

variable {k : Type*} [Fintype k] [DecidableEq k]

def diagonalBlock (P : Matrix (n × k) (n × k) ℂ) (i : k) : Matrix n n ℂ :=
  P.submatrix (fun a => (a, i)) (fun a => (a, i))

/-- Every diagonal block of an orthogonal projection is a positive contraction. -/
theorem projection_diagonalBlock_contraction (P : Matrix (n × k) (n × k) ℂ)
    (hP : P.IsHermitian) (hId : P * P = P) (i : k) :
    (diagonalBlock P i).PosSemidef ∧ (1 - diagonalBlock P i).PosSemidef := by
  have hPs : P.PosSemidef := by
    simpa only [hP.eq, hId] using Matrix.posSemidef_self_mul_conjTranspose P
  constructor
  · exact hPs.submatrix (fun a => (a, i))
  · have hIc : (1 - P).PosSemidef := by
      have hId' : (1 - P) * (1 - P) = 1 - P := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hId]
        abel
      have hH : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hP
      convert Matrix.posSemidef_self_mul_conjTranspose (1 - P) using 1
      rw [hH.eq, hId']
    have hs := hIc.submatrix (fun a : n => (a, i))
    have hi : Function.Injective (fun a : n => (a, i)) := fun _ _ h => Prod.mk.inj h |>.1
    simpa only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one _ hi, diagonalBlock] using hs

end
end ProjectionChannels

