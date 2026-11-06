import HaarProjections.GaussianRank
import HaarProjections.HaarMeasure

open scoped BigOperators ComplexOrder
open Matrix MeasureTheory PreliminariesMatrix GaussianRank

namespace HaarProjection
noncomputable section

variable {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq D]

/-- Whitening an actual independent Gaussian matrix gives a projection with
maximal local rank almost surely. -/
theorem ae_complexGaussian_whitenedProjection_rank
    (hd : Fintype.card D ≤ Fintype.card A * Fintype.card B) :
    ∀ᵐ z ∂Measure.pi (fun _ : (A × B) × D => complexGaussian),
      let G : Matrix (A × B) D ℂ := fun ab d => z (ab, d)
      (whitenedProjection G).PosSemidef ∧
      whitenedProjection G * whitenedProjection G = whitenedProjection G ∧
      (whitenedProjection G).rank = Fintype.card D ∧
      (traceB (whitenedProjection G)).rank =
        min (Fintype.card A) (Fintype.card B * Fintype.card D) := by
  filter_upwards [ae_gaussian_whitening_rank_inputs A B D hd] with z hz
  dsimp only at hz ⊢
  let G : Matrix (A × B) D ℂ := fun ab d => z (ab, d)
  have hi := injective_of_full_column_rank G hz.1
  exact ⟨whitenedProjection_posSemidef G hi,
    whitenedProjection_idempotent G hi,
    (whitenedProjection_rank G hi).trans hz.1,
    (whitenedProjection_partialTrace_rank G hi).trans hz.2⟩

/-- The exact full-local-support criterion for a whitened independent Gaussian matrix. -/
theorem ae_complexGaussian_whitenedProjection_posDef_iff
    (hd : Fintype.card D ≤ Fintype.card A * Fintype.card B) :
    ∀ᵐ z ∂Measure.pi (fun _ : (A × B) × D => complexGaussian),
      let G : Matrix (A × B) D ℂ := fun ab d => z (ab, d)
      (traceB (whitenedProjection G)).PosDef ↔
        Fintype.card A ≤ Fintype.card B * Fintype.card D := by
  filter_upwards [ae_gaussian_whitening_rank_inputs A B D hd] with z hz
  dsimp only at hz ⊢
  exact whitenedProjection_partialTrace_posDef_iff _
    (injective_of_full_column_rank _ hz.1) hz.2

end
end HaarProjection

