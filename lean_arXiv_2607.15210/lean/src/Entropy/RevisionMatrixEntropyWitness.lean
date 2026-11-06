import Entropy.RevisionMatrixEntropyConjugate
import Preliminaries.RevisionTensorChannels

/-! The Bell state is an admissible input for the actual tensor channel.
The upper bound on its minimum output entropy follows from boundedness on
the compact density-matrix space, without any assumed witness inequality. -/

open Filter Set Matrix PreliminariesMatrix ProjectionChannels ProjectionChannelsCP RevisionOutput
open scoped Topology BigOperators ComplexOrder
namespace RevisionMatrixEntropy
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]

lemma entropy_image_bddBelow (p : ℝ) (hp : 0<p)
    (C : Set (Matrix B B ℂ)) (hC : C ⊆ densityMatrices B) :
    BddBelow (matrixRenyiEntropy p '' C) :=
  ((isCompact_densityMatrices.image_of_continuousOn
    (matrixRenyiEntropy_continuousOn p hp)).bddBelow).mono (Set.image_mono hC)

/-- An actual density input gives an upper bound on minimum output entropy. -/
theorem minimumOutputEntropy_le_of_density (p : ℝ) (hp : 0<p)
    (Φ : Matrix A A ℂ → Matrix B B ℂ)
    (hΦ : ∀ρ∈densityMatrices A, Φ ρ ∈ densityMatrices B)
    {ρ : Matrix A A ℂ} (hρ : ρ ∈ densityMatrices A) :
    minimumOutputEntropy p Φ ≤ matrixRenyiEntropy p (Φ ρ) := by
  have hC : Φ '' densityMatrices A ⊆ densityMatrices B := by
    rintro _ ⟨σ,hσ,rfl⟩
    exact hΦ σ hσ
  exact csInf_le (entropy_image_bddBelow p hp _ hC) ⟨Φ ρ,⟨ρ,hρ,rfl⟩,rfl⟩

/-- Tensor products of genuine CP/TP maps preserve all input density matrices. -/
lemma tensor_channel_mem_density
    (Φ Ψ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hΦ : CompletelyPositive Φ ∧ TracePreserving Φ)
    (hΨ : CompletelyPositive Ψ ∧ TracePreserving Ψ)
    {ρ : Matrix (A×A) (A×A) ℂ} (hρ : ρ ∈ densityMatrices (A×A)) :
    RevisionBell.tensorMap Φ Ψ ρ ∈ densityMatrices (B×B) :=
  ⟨RevisionBell.tensorMap_posSemidef Φ Ψ hΦ.1 hΨ.1 hρ.1,
    (RevisionBell.tensorMap_trace Φ Ψ hΦ.2 hΨ.2 ρ).trans hρ.2⟩

/-- The Bell witness bound for arbitrary actual CP/TP channels. -/
theorem minimumOutputEntropy_tensor_bell_le (p : ℝ) (hp : 0<p)
    (Φ Ψ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hΦ : CompletelyPositive Φ ∧ TracePreserving Φ)
    (hΨ : CompletelyPositive Ψ ∧ TracePreserving Ψ) :
    minimumOutputEntropy p (RevisionBell.tensorMap Φ Ψ) ≤
      matrixRenyiEntropy p (RevisionBell.tensorMap Φ Ψ (RevisionBell.bellState A)) :=
  minimumOutputEntropy_le_of_density p hp _
    (fun _ hρ => tensor_channel_mem_density Φ Ψ hΦ hΨ hρ)
    RevisionBell.bellState_mem_densityMatrices

/-- The Bell witness for precisely the projection-induced normalized map. -/
theorem normalizedOutput_minimum_bell_le (p : ℝ) (hp : 0<p)
    {P : Matrix (A×B) (A×B) ℂ} (hP : P.PosSemidef)
    (D : Matrix A A ℂ) (hD : D.IsHermitian) (hn : D*traceB P*D=1) :
    minimumOutputEntropy p
      (RevisionBell.tensorMap (normalizedOutput P D) (conjugateMap (normalizedOutput P D))) ≤
      matrixRenyiEntropy p
        (RevisionBell.tensorMap (normalizedOutput P D) (conjugateMap (normalizedOutput P D))
          (RevisionBell.bellState A)) := by
  apply minimumOutputEntropy_le_of_density p hp _ _ RevisionBell.bellState_mem_densityMatrices
  intro ρ hρ
  have heq : normalizedOutput P D=channel (RevisionBell.normalizedChoi P D) :=
    funext fun σ => (RevisionBell.channel_normalizedChoi P D σ).symm
  rw [heq]
  exact RevisionBell.tensor_choi_conjugate_mem_densityMatrices
    (RevisionBell.normalizedChoi_posSemidef hP D hD hn) (normalized_choi D P hD hP hn).2 hρ

#print axioms normalizedOutput_minimum_bell_le
end
end RevisionMatrixEntropy
