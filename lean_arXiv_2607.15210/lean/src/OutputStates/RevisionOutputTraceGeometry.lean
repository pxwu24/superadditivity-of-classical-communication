import OutputStates.RevisionOutputTraceDistance

/-! Basic trace-norm geometry needed for Lemma III.3. -/
open Matrix PreliminariesMatrix ProjectionChannels
open scoped BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

lemma hermitianTraceNorm_density {ρ : Matrix A A ℂ} (hρ : ρ ∈ densityMatrices A) :
    hermitianTraceNorm ρ = 1 := by
  rw [hermitianTraceNorm_eq ρ hρ.1.isHermitian]
  calc
    ∑ i, |hρ.1.isHermitian.eigenvalues i| = ∑ i, hρ.1.isHermitian.eigenvalues i := by
      apply Finset.sum_congr rfl
      intro i _
      exact abs_of_nonneg (hρ.1.eigenvalues_nonneg i)
    _ = 1 := density_eigenvalues_sum hρ

lemma matrix_entry_norm_le_traceNorm (M : Matrix A A ℂ) (hM : M.IsHermitian) (i j : A) :
    ‖M i j‖ ≤ hermitianTraceNorm M := by
  have heq := congrArg (fun X : Matrix A A ℂ => X i j) hM.spectral_theorem
  simp only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Function.comp_apply, Matrix.diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at heq
  rw [heq, hermitianTraceNorm_eq M hM]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [norm_mul, norm_mul, norm_star]
  change ‖hM.eigenvectorUnitary i l‖ * ‖(hM.eigenvalues l : ℂ)‖ *
    ‖hM.eigenvectorUnitary j l‖ ≤ |hM.eigenvalues l|
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hi := HaarProjection.unitary_entry_norm_le_one hM.eigenvectorUnitary i l
  have hj := HaarProjection.unitary_entry_norm_le_one hM.eigenvectorUnitary j l
  calc
    _ ≤ 1 * |hM.eigenvalues l| * 1 := by gcongr
    _ = _ := by ring

/-- The entrywise supremum norm is bounded by the genuine trace norm on
the Hermitian subspace. Together with the opposite bound, this gives an
explicit finite-dimensional norm comparison. -/
lemma norm_le_hermitianTraceNorm (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    ‖M‖ ≤ hermitianTraceNorm M := by
  apply (pi_norm_le_iff_of_nonneg (hermitianTraceNorm_nonneg M)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (hermitianTraceNorm_nonneg M)).mpr
  intro j
  exact matrix_entry_norm_le_traceNorm M hM i j

lemma continuous_trace_pairing (H : Matrix A A ℂ) :
    Continuous (fun M : Matrix A A ℂ => (Matrix.trace (H*M)).re) := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  fun_prop

/-- The support function written exactly as in the manuscript. -/
def matrixSupport (K : Set (Matrix A A ℂ)) (H : Matrix A A ℂ) : ℝ :=
  sSup ((fun M => (Matrix.trace (H*M)).re) '' K)

lemma matrixSupport_isGreatest (K : Set (Matrix A A ℂ)) (hK : IsCompact K)
    (hne : K.Nonempty) (H : Matrix A A ℂ) :
    IsGreatest ((fun M => (Matrix.trace (H*M)).re) '' K) (matrixSupport K H) :=
  (hK.image (continuous_trace_pairing H)).isGreatest_sSup (hne.image _)

lemma matrixSupport_eq_real_support {K : Set (Matrix A A ℂ)}
    (hK : ∀ M ∈ K, M.IsHermitian) (f : Matrix A A ℂ →L[ℝ] ℝ) :
    matrixSupport K (hermitianFunctionalMatrix f) = support K f := by
  unfold matrixSupport support
  congr 1
  apply Set.image_congr
  intro M hM
  exact hermitian_trace_representation f (hK M hM)

end
end RevisionOutput
