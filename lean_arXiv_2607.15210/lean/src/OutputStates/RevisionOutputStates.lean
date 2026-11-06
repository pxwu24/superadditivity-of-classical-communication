import OutputStates.RevisionOutputFunctionals
import Preliminaries.CompletePositivity
import Mathlib.Analysis.Matrix

/-!
# The normalized outputs are density matrices

Positivity is obtained from the proved Kraus/Choi construction, and trace
normalization is proved using the exact partial-trace pairing. The final
bound uses the elementwise supremum matrix norm, explicitly selected locally.
-/

open Matrix PreliminariesMatrix ProjectionChannels ProjectionChannelsCP
open scoped BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]

lemma channel_posSemidef {P : Matrix (A × B) (A × B) ℂ} (hP : P.PosSemidef)
    {X : Matrix A A ℂ} (hX : X.PosSemidef) : (channel P X).PosSemidef := by
  have heq : hP.sqrt * hP.sqrt.conjTranspose = P := by
    rw [hP.posSemidef_sqrt.isHermitian.eq, hP.sqrt_mul_self]
  rw [← heq, channel_gram_kraus]
  exact posSemidef_sum _ (fun _ => hX.mul_mul_conjTranspose_same _)

lemma normalizedOutput_posSemidef {P : Matrix (A × B) (A × B) ℂ}
    (hP : P.PosSemidef) (D : Matrix A A ℂ) (hD : D.IsHermitian)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (normalizedOutput P D ρ).PosSemidef := by
  have hm : (D * ρ.transpose * D).PosSemidef := by
    simpa only [hD.eq] using hρ.transpose.mul_mul_conjTranspose_same D
  have heq := choi_inversion P (D * ρ.transpose * D).transpose
  simp only [Matrix.transpose_transpose] at heq
  rw [normalizedOutput, heq]
  exact channel_posSemidef hP hm.transpose

lemma normalizedOutput_trace (P : Matrix (A × B) (A × B) ℂ)
    (D : Matrix A A ℂ) (hn : D * traceB P * D = 1) (ρ : Matrix A A ℂ) :
    Matrix.trace (normalizedOutput P D ρ) = Matrix.trace ρ := by
  have h := normalizedOutput_pairing P D ρ (1 : Matrix B B ℂ)
  simpa only [Matrix.one_mul, contraction_one, hn, Matrix.trace_transpose] using h

/-- The exact Eq. (20) output has positive semidefinite trace-one values. -/
theorem normalizedOutput_mem_densityMatrices (P : Matrix (A × B) (A × B) ℂ)
    (hP : P.PosSemidef) (hA : (traceB P).PosDef)
    {ρ : Matrix A A ℂ} (hρ : ρ ∈ densityMatrices A) :
    normalizedOutput P hA.posSemidef.sqrt⁻¹ ρ ∈ densityMatrices B := by
  constructor
  · exact normalizedOutput_posSemidef hP _ hA.posSemidef.posSemidef_sqrt.isHermitian.inv hρ.1
  · rw [normalizedOutput_trace P _ (ProjectionChannels.inverse_sqrt_normalizes hA), hρ.2]

section SupNorm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma density_norm_le_one {ρ : Matrix A A ℂ} (hρ : ρ ∈ densityMatrices A) : ‖ρ‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  exact density_entry_norm_le_one hρ i j

end SupNorm
end
end RevisionOutput
