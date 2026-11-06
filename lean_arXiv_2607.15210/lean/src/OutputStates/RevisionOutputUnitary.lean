import OutputStates.RevisionOutputConvergence
import HaarProjections.HaarMeasure

/-!
# Unitary transport of the actual output support

This is the deterministic tensor-product calculation used to pass from
diagonal observables to arbitrary fixed Hermitian observables in Step 3
of Theorem III.1. All partial-trace identities are verified on actual matrices.
-/

open Matrix PreliminariesMatrix ProjectionChannels
open scoped BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [Nonempty A]

lemma traceB_local_cyclic (P : Matrix (A × B) (A × B) ℂ) (V : Matrix B B ℂ) :
    traceB (Matrix.kronecker (1 : Matrix A A ℂ) V * P) =
      traceB (P * Matrix.kronecker (1 : Matrix A A ℂ) V) := by
  ext a b
  simp only [traceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma local_kronecker_mul (U V : Matrix B B ℂ) :
    Matrix.kronecker (1 : Matrix A A ℂ) U * Matrix.kronecker (1 : Matrix A A ℂ) V =
      Matrix.kronecker (1 : Matrix A A ℂ) (U * V) := by
  simpa only [Matrix.kronecker, Matrix.one_mul] using
    (Matrix.mul_kronecker_mul (1 : Matrix A A ℂ) (1 : Matrix A A ℂ) U V).symm

/-- Local conjugation by the fixed output unitary. -/
def localConjugate (P : Matrix (A × B) (A × B) ℂ) (V : Matrix B B ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  Matrix.kronecker (1 : Matrix A A ℂ) V.conjTranspose * P *
    Matrix.kronecker (1 : Matrix A A ℂ) V

lemma contraction_localConjugate (P : Matrix (A × B) (A × B) ℂ)
    (V H : Matrix B B ℂ) :
    contraction (localConjugate P V) H = contraction P (V * H * V.conjTranspose) := by
  unfold contraction localConjugate
  rw [Matrix.mul_assoc, Matrix.mul_assoc, traceB_local_cyclic]
  simp only [Matrix.mul_assoc, local_kronecker_mul]

lemma traceB_localConjugate (P : Matrix (A × B) (A × B) ℂ)
    (V : Matrix.unitaryGroup B ℂ) :
    traceB (localConjugate P (V : Matrix B B ℂ)) = traceB P := by
  rw [← contraction_one, contraction_localConjugate]
  have hV : (V : Matrix B B ℂ) * (V : Matrix B B ℂ).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp V.2
  simp only [Matrix.mul_one, hV, contraction_one]

lemma localConjugate_isHermitian {P : Matrix (A × B) (A × B) ℂ}
    (hP : P.IsHermitian) (V : Matrix B B ℂ) : (localConjugate P V).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul
    (Matrix.kronecker (1 : Matrix A A ℂ) V) hP
  have heq : (Matrix.kronecker (1 : Matrix A A ℂ) V).conjTranspose =
      Matrix.kronecker (1 : Matrix A A ℂ) V.conjTranspose := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases hab : a = b
    · subst b
      simp [Matrix.conjTranspose_apply, Matrix.kronecker_apply]
    · simp [Matrix.conjTranspose_apply, Matrix.kronecker_apply, Matrix.one_apply, hab, Ne.symm hab]
  simpa only [localConjugate, heq] using h

/-- The exact support-function transport, for any Hermitian observable.
The normalization is retained unchanged, since the marginal is unchanged. -/
theorem outputSupport_localConjugate (P : Matrix (A × B) (A × B) ℂ)
    (hP : P.IsHermitian) (D : Matrix A A ℂ) (hD : D.IsHermitian)
    (V : Matrix B B ℂ) (H : Matrix B B ℂ) (hH : H.IsHermitian) :
    outputSupport (localConjugate P V) D H =
      outputSupport P D (V * H * V.conjTranspose) := by
  rw [normalized_output_support _ (localConjugate_isHermitian hP V) D hD H hH,
    normalized_output_support P hP D hD _ (Matrix.isHermitian_mul_mul_conjTranspose V hH)]
  simp only [contraction_localConjugate]

lemma local_kronecker_conjTranspose (V : Matrix B B ℂ) :
    (Matrix.kronecker (1 : Matrix A A ℂ) V).conjTranspose =
      Matrix.kronecker (1 : Matrix A A ℂ) V.conjTranspose := by
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases hab : a = b
  · subst b
    simp [Matrix.conjTranspose_apply, Matrix.kronecker_apply]
  · simp [Matrix.conjTranspose_apply, Matrix.kronecker_apply, Matrix.one_apply, hab, Ne.symm hab]

/-- A fixed output unitary, lifted to the full input-output space. -/
def liftedOutputUnitary (V : Matrix.unitaryGroup B ℂ) : Matrix.unitaryGroup (A × B) ℂ :=
  ⟨Matrix.kronecker (1 : Matrix A A ℂ) (V : Matrix B B ℂ).conjTranspose, by
    apply Matrix.mem_unitaryGroup_iff.mpr
    have hV : (V : Matrix B B ℂ).conjTranspose * (V : Matrix B B ℂ) = 1 := V.prop.1
    rw [Matrix.star_eq_conjTranspose, local_kronecker_conjTranspose, Matrix.conjTranspose_conjTranspose,
      local_kronecker_mul, hV]
    exact Matrix.one_kronecker_one⟩

/-- The actual Haar projection law is invariant under the conjugation in
Step 3. This uses the already proved Haar invariance theorem and introduces
no distributional assumption. -/
theorem haarProjectionLaw_localConjugate_invariant
    (P₀ : Matrix (A × B) (A × B) ℂ) (V : Matrix.unitaryGroup B ℂ) :
    (HaarProjection.haarProjectionLaw P₀).map
      (fun P => localConjugate P (V : Matrix B B ℂ)) =
      HaarProjection.haarProjectionLaw P₀ := by
  have h := HaarProjection.haarProjectionLaw_conjugation_invariant P₀
    (liftedOutputUnitary (A := A) V)
  simpa only [liftedOutputUnitary, local_kronecker_conjTranspose,
    Matrix.conjTranspose_conjTranspose, localConjugate] using h

end
end RevisionOutput
