import HaarProjections.GaussianWhitening
import HaarProjections.HaarOrbitUnique
import HaarProjections.ProjectionOrbit
import HaarProjections.MatrixRankMeasurable

open scoped BigOperators ComplexOrder
open Matrix MeasureTheory PreliminariesMatrix

namespace HaarProjection
noncomputable section

variable {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq D]

/-- The linear algebra, uniqueness-of-invariant-law argument, and measurable
rank transfer assembled. The three distributional inputs are proved separately
for the radial Gaussian matrix law. -/
theorem haar_local_rank_from_invariant_matrix_law
    (ν : Measure (Matrix (A × B) D ℂ)) [IsProbabilityMeasure ν]
    (hinv : ∀ U : Matrix.unitaryGroup (A × B) ℂ,
      ν.map (fun G => (U : Matrix (A × B) (A × B) ℂ) * G) = ν)
    (hcol : ∀ᵐ G ∂ν, G.rank = Fintype.card D)
    (hflat : ∀ᵐ G ∂ν, (flatten G).rank =
      min (Fintype.card A) (Fintype.card B * Fintype.card D))
    (P₀ : Matrix (A × B) (A × B) ℂ) (hP₀ : P₀.IsHermitian)
    (hp₀ : P₀ * P₀ = P₀) (hr₀ : P₀.rank = Fintype.card D) :
    ∀ᵐ U : Matrix.unitaryGroup (A × B) ℂ ∂(unitaryHaar (E := A × B)),
      (traceB ((U : Matrix (A × B) (A × B) ℂ) * P₀ *
        (U : Matrix (A × B) (A × B) ℂ).conjTranspose)).rank =
          min (Fintype.card A) (Fintype.card B * Fintype.card D) := by
  have horbit : ∀ᵐ G ∂ν, ∃ U : Matrix.unitaryGroup (A × B) ℂ,
      whitenedProjection G = (U : Matrix (A × B) (A × B) ℂ) * P₀ *
        (U : Matrix (A × B) (A × B) ℂ).conjTranspose := by
    filter_upwards [hcol] with G hG
    have hi := injective_of_full_column_rank G hG
    exact ProjectionOrbit.exists_unitary_conjugate _ _
      (whitenedProjection_posSemidef G hi).isHermitian
      (whitenedProjection_idempotent G hi) hP₀ hp₀
      (by rw [whitenedProjection_rank G hi, hG, hr₀])
  have hlaw := whitenedLaw_eq_haarProjectionLaw ν P₀ hinv horbit
  exact (ae_haar_iff_ae_whitened_of_law_eq ν P₀ hlaw _
    (ProjectionChannels.measurableSet_traceB_rank_eq _)).mpr
      (ae_whitenedProjection_partialTrace_rank ν id hcol hflat)

/-- The strict-positivity criterion follows on the same probability-one event. -/
theorem haar_local_support_from_invariant_matrix_law
    (ν : Measure (Matrix (A × B) D ℂ)) [IsProbabilityMeasure ν]
    (hinv : ∀ U : Matrix.unitaryGroup (A × B) ℂ,
      ν.map (fun G => (U : Matrix (A × B) (A × B) ℂ) * G) = ν)
    (hcol : ∀ᵐ G ∂ν, G.rank = Fintype.card D)
    (hflat : ∀ᵐ G ∂ν, (flatten G).rank =
      min (Fintype.card A) (Fintype.card B * Fintype.card D))
    (P₀ : Matrix (A × B) (A × B) ℂ) (hP₀ : P₀.IsHermitian)
    (hp₀ : P₀ * P₀ = P₀) (hr₀ : P₀.rank = Fintype.card D) :
    ∀ᵐ U : Matrix.unitaryGroup (A × B) ℂ ∂(unitaryHaar (E := A × B)),
      (traceB ((U : Matrix (A × B) (A × B) ℂ) * P₀ *
        (U : Matrix (A × B) (A × B) ℂ).conjTranspose)).PosDef ↔
          Fintype.card A ≤ Fintype.card B * Fintype.card D := by
  filter_upwards [haar_local_rank_from_invariant_matrix_law ν hinv hcol hflat P₀ hP₀ hp₀ hr₀]
    with U hU
  have hps := traceB_posSemidef _
    ((projection_posSemidef P₀ hP₀ hp₀).mul_mul_conjTranspose_same
      (U : Matrix (A × B) (A × B) ℂ))
  rw [posDef_iff_full_rank _ hps, hU]
  omega

end
end HaarProjection

