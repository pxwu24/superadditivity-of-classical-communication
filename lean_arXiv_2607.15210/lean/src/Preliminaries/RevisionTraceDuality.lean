import BellOutput.RevisionBellContraction
import OutputStates.RevisionOutputBody

/-! # Exact trace/operator norm duality on Hermitian matrices

The upper bound is proved on an eigenbasis of the tested matrix. Equality
is attained by its spectral sign matrix, constructed by functional calculus.
-/
open Matrix PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped BigOperators ComplexOrder Matrix.L2OpNorm
namespace RevisionOutput
noncomputable section
variable {k : ℕ} [NeZero k]

local instance traceDualMatrixCStarAlgebra : CStarAlgebra (Matrix (Fin k) (Fin k) ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance
  norm_mul_self_le := CStarRing.norm_mul_self_le

lemma conjugate_diagonal_eq_eigenstate_expectation
    (M H : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) (i : Fin k) :
    (unitaryConjugate (star hM.eigenvectorUnitary) H i i).re =
      (Matrix.trace (H * eigenstate M hM i)).re := by
  rw [eigenstate, trace_mul_vecMulVec]
  simp only [unitaryConjugate, unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma trace_pairing_abs_le_traceNorm (M H : Matrix (Fin k) (Fin k) ℂ)
    (hM : M.IsHermitian) (hH : H.IsHermitian) :
    |(Matrix.trace (H*M)).re| ≤ ‖H‖ * ∑ i, |hM.eigenvalues i| := by
  rw [Matrix.trace_mul_comm H M, trace_pairing_in_eigenbasis M H hM]
  calc
    _ ≤ ∑ i, |hM.eigenvalues i *
        (unitaryConjugate (star hM.eigenvectorUnitary) H i i).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |hM.eigenvalues i| * ‖H‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, conjugate_diagonal_eq_eigenstate_expectation]
      exact mul_le_mul_of_nonneg_left
        (BellLimitVerification.density_expectation_abs_le_opNorm hH
          ⟨eigenstate_posSemidef M hM i, eigenstate_trace M hM i⟩) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma spectral_sign_witness (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) :
    ∃ H : Matrix (Fin k) (Fin k) ℂ, H.IsHermitian ∧ ‖H‖ ≤ 1 ∧
      (Matrix.trace (H*M)).re = ∑ i, |hM.eigenvalues i| := by
  let f : ℝ → ℝ := fun x => if x < 0 then -1 else 1
  let H := cfc f M
  have hH : H.IsHermitian := by exact cfc_predicate f M
  have hn : ‖H‖ ≤ 1 := by
    apply norm_cfc_le (by norm_num : (0:ℝ) ≤ 1)
    intro x _
    dsimp [f]
    split_ifs <;> norm_num
  refine ⟨H, hH, hn, ?_⟩
  rw [Matrix.trace_mul_comm H M, trace_pairing_in_eigenbasis M H hM]
  have heq : H = unitaryConjugate hM.eigenvectorUnitary
      (diagonal (fun i => (f (hM.eigenvalues i) : ℂ))) := by
    simp only [H, hM.cfc_eq, Matrix.IsHermitian.cfc, unitaryConjugate,
      Function.comp_def, Matrix.star_eq_conjTranspose]
    rfl
  rw [heq, unitaryConjugate_star_self]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diagonal_apply_eq, Complex.ofReal_re]
  dsimp [f]
  split_ifs with hi
  · rw [abs_of_neg hi]; ring
  · rw [abs_of_nonneg (le_of_not_gt hi)]; ring

/-- Trace norm is the attained dual of the operator norm on Hermitian matrices. -/
theorem trace_operator_duality_isGreatest
    (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) :
    IsGreatest ((fun H : Matrix (Fin k) (Fin k) ℂ => (Matrix.trace (H*M)).re) ''
      {H | H.IsHermitian ∧ ‖H‖ ≤ 1}) (∑ i, |hM.eigenvalues i|) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨H, hH, hn, he⟩ := spectral_sign_witness M hM
    exact ⟨H, ⟨hH, hn⟩, he⟩
  · rintro _ ⟨H, ⟨hH, hn⟩, rfl⟩
    exact (le_abs_self _).trans ((trace_pairing_abs_le_traceNorm M H hM hH).trans
      (by
        simpa only [one_mul] using (mul_le_mul_of_nonneg_right hn
          (Finset.sum_nonneg fun i _ => abs_nonneg (hM.eigenvalues i)))))

theorem trace_operator_duality (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) :
    (∑ i, |hM.eigenvalues i|) = sSup
      ((fun H : Matrix (Fin k) (Fin k) ℂ => (Matrix.trace (H*M)).re) ''
        {H | H.IsHermitian ∧ ‖H‖ ≤ 1}) :=
  (trace_operator_duality_isGreatest M hM).csSup_eq.symm

/-- The Euclidean operator norm, explicitly named to avoid choosing an
entrywise matrix norm in downstream finite-dimensional geometry. -/
def hermitianOperatorNorm (H : Matrix (Fin k) (Fin k) ℂ) : ℝ := ‖H‖

@[simp] lemma hermitianOperatorNorm_zero :
    hermitianOperatorNorm (0 : Matrix (Fin k) (Fin k) ℂ) = 0 := norm_zero

@[simp] lemma hermitianOperatorNorm_neg (H : Matrix (Fin k) (Fin k) ℂ) :
    hermitianOperatorNorm (-H) = hermitianOperatorNorm H := norm_neg H

lemma hermitianOperatorNorm_nonneg (H : Matrix (Fin k) (Fin k) ℂ) :
    0 ≤ hermitianOperatorNorm H := norm_nonneg H

@[simp] lemma hermitianOperatorNorm_eq_zero (H : Matrix (Fin k) (Fin k) ℂ) :
    hermitianOperatorNorm H = 0 ↔ H = 0 := norm_eq_zero

lemma hermitianOperatorNorm_smul (a : ℝ) (H : Matrix (Fin k) (Fin k) ℂ) :
    hermitianOperatorNorm (a • H) = |a| * hermitianOperatorNorm H := by
  exact norm_smul a H

lemma hermitianOperatorNorm_add_le (H K : Matrix (Fin k) (Fin k) ℂ) :
    hermitianOperatorNorm (H+K) ≤ hermitianOperatorNorm H + hermitianOperatorNorm K :=
  norm_add_le H K

lemma exists_abs_eigenvalue_eq_opNorm (H : Matrix (Fin k) (Fin k) ℂ)
    (hH : H.IsHermitian) : ∃ i, |hH.eigenvalues i| = hermitianOperatorNorm H := by
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => |hH.eigenvalues i|)
  have hall : ∀ j, |hH.eigenvalues j| ≤ |hH.eigenvalues i| := by
    intro j
    rw [← heq]
    exact Finset.le_sup' (fun j => |hH.eigenvalues j|) (Finset.mem_univ j)
  refine ⟨i, le_antisymm ?_ ?_⟩
  · exact spectrum.norm_le_norm_of_mem (hH.eigenvalues_mem_spectrum_real i)
  · change ‖H‖ ≤ |hH.eigenvalues i|
    conv_lhs => rw [← cfc_id ℝ H hH.isSelfAdjoint]
    apply norm_cfc_le (abs_nonneg _)
    intro x hx
    obtain ⟨j, rfl⟩ := hH.eigenvalues_eq_spectrum_real ▸ hx
    simpa only [id_eq, Real.norm_eq_abs] using hall j

/-- A rank-one density matrix attains the absolute operator-norm pairing. -/
theorem density_opNorm_witness (H : Matrix (Fin k) (Fin k) ℂ)
    (hH : H.IsHermitian) :
    ∃ ρ ∈ densityMatrices (Fin k),
      |(Matrix.trace (H*ρ)).re| = hermitianOperatorNorm H := by
  obtain ⟨i, hi⟩ := exists_abs_eigenvalue_eq_opNorm H hH
  refine ⟨eigenstate H hH i, ⟨eigenstate_posSemidef H hH i,
    eigenstate_trace H hH i⟩, ?_⟩
  rw [eigenstate_expectation, hi]

theorem trace_operator_duality_named (M : Matrix (Fin k) (Fin k) ℂ)
    (hM : M.IsHermitian) :
    IsGreatest ((fun H : Matrix (Fin k) (Fin k) ℂ => (Matrix.trace (H*M)).re) ''
      {H | H.IsHermitian ∧ hermitianOperatorNorm H ≤ 1})
      (∑ i, |hM.eigenvalues i|) :=
  trace_operator_duality_isGreatest M hM

end
end RevisionOutput
