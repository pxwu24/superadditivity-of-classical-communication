import OutputStates.RevisionOutputUnitary

/-!
# Compactness and convexity of actual input/output state spaces

These lemmas concern genuine complex density matrices. In particular,
compactness is proved from closed positivity constraints and a spectral
entry bound, rather than assumed as an abstract feasible-set property.
-/

open Matrix PreliminariesMatrix ProjectionChannels Set
open scoped BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
variable {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

lemma trace_eq_sum_eigenvalues (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    Matrix.trace M = ∑ i, (hM.eigenvalues i : ℂ) := by
  conv_lhs => rw [hM.spectral_theorem]
  rw [Matrix.trace_mul_cycle, hM.eigenvectorUnitary.prop.1, Matrix.one_mul,
    Matrix.trace_diagonal]
  rfl

lemma density_eigenvalues_sum {ρ : Matrix A A ℂ} (hρ : ρ ∈ densityMatrices A) :
    ∑ i, hρ.1.isHermitian.eigenvalues i = 1 := by
  have heq := trace_eq_sum_eigenvalues ρ hρ.1.isHermitian
  have h := congrArg Complex.re (heq.symm.trans hρ.2)
  simpa only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] using h

lemma density_entry_norm_le_one {ρ : Matrix A A ℂ} (hρ : ρ ∈ densityMatrices A) (i j : A) :
    ‖ρ i j‖ ≤ 1 := by
  have heq := congrArg (fun M : Matrix A A ℂ => M i j) hρ.1.isHermitian.spectral_theorem
  simp only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Function.comp_apply, Matrix.diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at heq
  rw [heq]
  apply (norm_sum_le _ _).trans
  calc
    ∑ l : A, ‖hρ.1.isHermitian.eigenvectorUnitary i l *
      (hρ.1.isHermitian.eigenvalues l : ℂ) * star (hρ.1.isHermitian.eigenvectorUnitary j l)‖
      ≤ ∑ l : A, hρ.1.isHermitian.eigenvalues l := by
      apply Finset.sum_le_sum
      intro l _
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hρ.1.eigenvalues_nonneg l)]
      have hp := hρ.1.eigenvalues_nonneg l
      have hi := HaarProjection.unitary_entry_norm_le_one hρ.1.isHermitian.eigenvectorUnitary i l
      have hj := HaarProjection.unitary_entry_norm_le_one hρ.1.isHermitian.eigenvectorUnitary j l
      calc
        _ ≤ 1 * hρ.1.isHermitian.eigenvalues l * 1 := by gcongr
        _ = _ := by ring
    _ = 1 := density_eigenvalues_sum hρ

lemma isClosed_posSemidef : IsClosed {M : Matrix A A ℂ | M.PosSemidef} := by
  have hh : IsClosed {M : Matrix A A ℂ | M.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hq : IsClosed {M : Matrix A A ℂ | ∀ v : A → ℂ, 0 ≤ dotProduct (star v) (M *ᵥ v)} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold dotProduct Matrix.mulVec
    fun_prop
  exact hh.inter hq

lemma isClosed_densityMatrices : IsClosed (densityMatrices A) := by
  have ht : IsClosed {M : Matrix A A ℂ | Matrix.trace M = 1} := by
    apply isClosed_eq _ continuous_const
    unfold Matrix.trace Matrix.diag
    fun_prop
  exact isClosed_posSemidef.inter ht

/-- The state space is compact in the ordinary finite-dimensional matrix topology. -/
theorem isCompact_densityMatrices : IsCompact (densityMatrices A) := by
  let K : Set (Matrix A A ℂ) := Set.pi Set.univ
    (fun _ : A => Set.pi Set.univ (fun _ : A => Metric.closedBall (0 : ℂ) 1))
  have hK : IsCompact K :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  apply hK.of_isClosed_subset isClosed_densityMatrices
  intro ρ hρ i _ j _
  simpa only [Metric.mem_closedBall, dist_zero_right] using density_entry_norm_le_one hρ i j

lemma densityMatrices_nonempty : (densityMatrices A).Nonempty := by
  let i : A := Classical.arbitrary A
  exact ⟨eigenstate (1 : Matrix A A ℂ) Matrix.isHermitian_one i,
    eigenstate_posSemidef _ _ _, eigenstate_trace _ _ _⟩

/-- The convexity of the state space is proved from cone convexity and the
trace-one constraint. -/
theorem convex_densityMatrices : Convex ℝ (densityMatrices A) := by
  intro ρ hρ σ hσ a b ha hb hab
  constructor
  · have h := (posSemidef_real_smul hρ.1 a ha).add (posSemidef_real_smul hσ.1 b hb)
    exact h
  · simp only [Matrix.trace_add, Matrix.trace_smul, hρ.2, hσ.2,
      smul_eq_mul, mul_one]
    rw [← add_smul, hab, one_smul]

variable [Fintype B] [DecidableEq B]

lemma normalizedOutput_continuous (P : Matrix (A × B) (A × B) ℂ) (D : Matrix A A ℂ) :
    Continuous (normalizedOutput P D) := by
  unfold normalizedOutput traceA
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  fun_prop

/-- The actual output image is nonempty and compact. -/
theorem output_image_nonempty_compact (P : Matrix (A × B) (A × B) ℂ) (D : Matrix A A ℂ) :
    (normalizedOutput P D '' densityMatrices A).Nonempty ∧
      IsCompact (normalizedOutput P D '' densityMatrices A) :=
  ⟨densityMatrices_nonempty.image _, isCompact_densityMatrices.image (normalizedOutput_continuous P D)⟩

lemma normalizedOutput_linear_combination (P : Matrix (A × B) (A × B) ℂ)
    (D ρ σ : Matrix A A ℂ) (a b : ℝ) :
    normalizedOutput P D (a • ρ + b • σ) =
      a • normalizedOutput P D ρ + b • normalizedOutput P D σ := by
  ext i j
  simp [normalizedOutput, traceA, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.transpose_apply,
    Matrix.add_apply, Matrix.smul_apply, mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul, Complex.real_smul, mul_assoc, mul_left_comm]

/-- The actual output image is convex. -/
theorem output_image_convex (P : Matrix (A × B) (A × B) ℂ) (D : Matrix A A ℂ) :
    Convex ℝ (normalizedOutput P D '' densityMatrices A) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨ρ, hρ, rfl⟩ := hx
  obtain ⟨σ, hσ, rfl⟩ := hy
  exact ⟨a • ρ + b • σ, convex_densityMatrices hρ hσ ha hb hab,
    normalizedOutput_linear_combination P D ρ σ a b⟩

end
end RevisionOutput
