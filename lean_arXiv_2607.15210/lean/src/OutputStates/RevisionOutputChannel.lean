import OutputStates.OutputSpaceMatrix
import Preliminaries.PreliminariesChoi

/-!
# Density-matrix support and the locally normalized channel

This file uses actual complex matrices, positive semidefiniteness, trace-one
states, and their Choi channel. It proves that maximization over density
matrices yields the largest eigenvalue, including attainment by an eigenstate.
-/

open scoped BigOperators ComplexOrder
open Matrix PreliminariesMatrix ProjectionChannels
namespace RevisionOutput
noncomputable section
variable {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Actual density matrices, rather than an abstract support-function model. -/
def densityMatrices (A : Type*) [Fintype A] : Set (Matrix A A ℂ) :=
  {ρ | ρ.PosSemidef ∧ Matrix.trace ρ = 1}

lemma re_trace_nonneg {M : Matrix A A ℂ} (hM : M.PosSemidef) :
    0 ≤ (Matrix.trace M).re := by
  have hd : ∀ i, 0 ≤ (M i i).re := by
    intro i
    simpa only [← Pi.single_star, star_one, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.transpose_apply] using hM.re_dotProduct_nonneg (Pi.single i 1)
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hd i

lemma re_trace_mul_nonneg {M N : Matrix A A ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    0 ≤ (Matrix.trace (M * N)).re := by
  have hp := hN.mul_mul_conjTranspose_same hM.sqrt
  rw [hM.posSemidef_sqrt.isHermitian.eq] at hp
  have h := re_trace_nonneg hp
  rw [Matrix.trace_mul_cycle, hM.sqrt_mul_self] at h
  exact h

lemma density_expectation_le {M ρ : Matrix A A ℂ} (hM : M.IsHermitian)
    (hρ : ρ ∈ densityMatrices A) :
    (Matrix.trace (M * ρ)).re ≤ largestEigenvalue hM := by
  have hp := (largest_le_iff_shift_posSemidef hM (largestEigenvalue hM)).mp le_rfl
  have h := re_trace_mul_nonneg hp hρ.1
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, hρ.2] at h
  simp only [smul_eq_mul, mul_one, Complex.sub_re, Complex.ofReal_re] at h
  linarith

lemma eigenvector_norm_one (M : Matrix A A ℂ) (hM : M.IsHermitian) (i : A) :
    dotProduct (star ⇑(hM.eigenvectorBasis i)) ⇑(hM.eigenvectorBasis i) = (1 : ℂ) := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, hM.eigenvectorBasis.orthonormal.1 i]
  simp

/-- Rank-one density matrix associated with a unit eigenvector. -/
def eigenstate (M : Matrix A A ℂ) (hM : M.IsHermitian) (i : A) : Matrix A A ℂ :=
  Matrix.vecMulVec ⇑(hM.eigenvectorBasis i) (star ⇑(hM.eigenvectorBasis i))

lemma eigenstate_posSemidef (M : Matrix A A ℂ) (hM : M.IsHermitian) (i : A) :
    (eigenstate M hM i).PosSemidef := by
  let V : Matrix A Unit ℂ := fun a _ => ⇑(hM.eigenvectorBasis i) a
  have h := Matrix.posSemidef_self_mul_conjTranspose V
  convert h using 1
  ext a b
  simp [eigenstate, Matrix.vecMulVec, V, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma eigenstate_trace (M : Matrix A A ℂ) (hM : M.IsHermitian) (i : A) :
    Matrix.trace (eigenstate M hM i) = 1 := by
  simpa [eigenstate, Matrix.trace, Matrix.diag, Matrix.vecMulVec, dotProduct,
    mul_comm] using eigenvector_norm_one M hM i

lemma trace_mul_vecMulVec (M : Matrix A A ℂ) (v w : A → ℂ) :
    Matrix.trace (M * Matrix.vecMulVec v w) = dotProduct w (M *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma eigenstate_expectation (M : Matrix A A ℂ) (hM : M.IsHermitian) (i : A) :
    (Matrix.trace (M * eigenstate M hM i)).re = hM.eigenvalues i := by
  rw [eigenstate, trace_mul_vecMulVec]
  exact (hM.eigenvalues_eq i).symm

/-- The largest eigenvalue is the attained maximum over genuine density
matrices. This is the variational principle used in Lemma III.4. -/
theorem density_expectation_isGreatest (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    IsGreatest ((fun ρ => (Matrix.trace (M * ρ)).re) '' densityMatrices A)
      (largestEigenvalue hM) := by
  constructor
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hM.eigenvalues
    refine ⟨eigenstate M hM i, ⟨eigenstate_posSemidef M hM i, eigenstate_trace M hM i⟩, ?_⟩
    change (Matrix.trace (M * eigenstate M hM i)).re = largestEigenvalue hM
    rw [eigenstate_expectation]
    exact heq.symm
  · rintro x ⟨ρ, hρ, rfl⟩
    exact density_expectation_le hM hρ

/-- Transposition permutes the density matrices in the chosen basis. -/
lemma transpose_image_densityMatrices :
    Matrix.transpose '' densityMatrices A = densityMatrices A := by
  ext ρ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨hσ.1.transpose, by simpa using hσ.2⟩
  · intro hρ
    exact ⟨ρ.transpose, ⟨hρ.1.transpose, by simpa using hρ.2⟩, Matrix.transpose_transpose ρ⟩

/-- The same maximum with the transpose from the input-first Choi formula. -/
theorem density_transpose_expectation_isGreatest (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    IsGreatest ((fun ρ => (Matrix.trace (M * ρ.transpose)).re) '' densityMatrices A)
      (largestEigenvalue hM) := by
  have h := density_expectation_isGreatest M hM
  rw [← transpose_image_densityMatrices (A := A)] at h
  simpa only [Set.image_image, Function.comp_def] using h

variable [Fintype B] [DecidableEq B]

/-- The unnormalized adjoint block contraction in Eq. (29). -/
def contraction (P : Matrix (A × B) (A × B) ℂ) (H : Matrix B B ℂ) : Matrix A A ℂ :=
  traceB (P * Matrix.kronecker (1 : Matrix A A ℂ) H)

lemma contraction_entry (P : Matrix (A × B) (A × B) ℂ) (H : Matrix B B ℂ) (a b : A) :
    contraction P H a b = ∑ i : B, ∑ j : B, P (a,i) (b,j) * H j i := by
  simp [contraction, traceB, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]

/-- The output written in the exact locally normalized form of Eq. (20). -/
def normalizedOutput (P : Matrix (A × B) (A × B) ℂ) (D : Matrix A A ℂ)
    (ρ : Matrix A A ℂ) : Matrix B B ℂ :=
  traceA (P * Matrix.kronecker (D * ρ.transpose * D) (1 : Matrix B B ℂ))

lemma trace_partialTrace_pairing (P : Matrix (A × B) (A × B) ℂ)
    (M : Matrix A A ℂ) (H : Matrix B B ℂ) :
    Matrix.trace (H * traceA (P * Matrix.kronecker M (1 : Matrix B B ℂ))) =
      Matrix.trace (contraction P H * M) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceA,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    contraction_entry, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma normalizedOutput_pairing (P : Matrix (A × B) (A × B) ℂ)
    (D ρ : Matrix A A ℂ) (H : Matrix B B ℂ) :
    Matrix.trace (H * normalizedOutput P D ρ) =
      Matrix.trace (D * contraction P H * D * ρ.transpose) := by
  rw [normalizedOutput, trace_partialTrace_pairing]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

lemma contraction_isHermitian {P : Matrix (A × B) (A × B) ℂ}
    {H : Matrix B B ℂ} (hP : P.IsHermitian) (hH : H.IsHermitian) :
    (contraction P H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [contraction_entry, star_sum, star_mul', hP.apply, hH.apply]
  rw [Finset.sum_comm]

lemma contraction_one (P : Matrix (A × B) (A × B) ℂ) :
    contraction P (1 : Matrix B B ℂ) = traceB P := by
  ext a b
  simp [contraction_entry, Matrix.one_apply, traceB]

lemma contraction_sub_scalar (P : Matrix (A × B) (A × B) ℂ)
    (H : Matrix B B ℂ) (z : ℝ) :
    contraction P (H - (z : ℂ) • (1 : Matrix B B ℂ)) =
      contraction P H - (z : ℂ) • traceB P := by
  ext a b
  simp only [contraction_entry, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, mul_sub, Finset.sum_sub_distrib, traceB, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

/-- The support of the actual output image of the density matrices. -/
def outputSupport (P : Matrix (A × B) (A × B) ℂ) (D : Matrix A A ℂ)
    (H : Matrix B B ℂ) : ℝ :=
  sSup ((fun σ => (Matrix.trace (H * σ)).re) ''
    (normalizedOutput P D '' densityMatrices A))

/-- First equality of Lemma III.4, including actual channel pairing and
maximization over all trace-one positive semidefinite input matrices. -/
theorem normalized_output_support (P : Matrix (A × B) (A × B) ℂ)
    (hP : P.IsHermitian) (D : Matrix A A ℂ) (hD : D.IsHermitian)
    (H : Matrix B B ℂ) (hH : H.IsHermitian) :
    outputSupport P D H =
      largestEigenvalue (hermitian_sandwich (contraction_isHermitian hP hH) hD) := by
  unfold outputSupport
  rw [Set.image_image]
  have hf : (fun x => (Matrix.trace (H * normalizedOutput P D x)).re) =
      (fun x => (Matrix.trace (D * contraction P H * D * x.transpose)).re) := by
    funext x
    rw [normalizedOutput_pairing]
  change sSup ((fun x => (Matrix.trace (H * normalizedOutput P D x)).re) '' _) = _
  rw [hf]
  exact (density_transpose_expectation_isGreatest (D * contraction P H * D)
    (hermitian_sandwich (contraction_isHermitian hP hH) hD)).csSup_eq

/-- Lemma III.4 for the inverse positive square root in Eq. (20).
All finite-dimensional support and threshold identities are derived here;
no channel-support formula is assumed. -/
theorem local_channel_support_threshold (P : Matrix (A × B) (A × B) ℂ)
    (hP : P.IsHermitian) (hA : (traceB P).PosDef)
    (H : Matrix B B ℂ) (hH : H.IsHermitian) :
    outputSupport P hA.posSemidef.sqrt⁻¹ H =
      sInf {z : ℝ | largestEigenvalue
        (contraction_isHermitian hP
          (real_scalar_shift_hermitian hH (Matrix.isHermitian_one) z)) ≤ 0} := by
  rw [normalized_output_support P hP _ hA.posSemidef.posSemidef_sqrt.isHermitian.inv H hH]
  have hs : {z : ℝ | largestEigenvalue
        (contraction_isHermitian hP
          (real_scalar_shift_hermitian hH (Matrix.isHermitian_one) z)) ≤ 0} =
      Set.Ici (largestEigenvalue
        (hermitian_sandwich (contraction_isHermitian hP hH)
          hA.posSemidef.posSemidef_sqrt.isHermitian.inv)) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    have ht := inverse_sqrt_threshold (traceB P) (contraction P H) hA
      (contraction_isHermitian hP hH) z
    simpa only [contraction_sub_scalar] using ht.symm
  rw [hs, csInf_Ici]

end
end RevisionOutput
