import HaarProjections.GaussianRadial
import HaarProjections.GaussianUnitary
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ENNReal NNReal BigOperators
open MeasureTheory MeasureTheory.Measure Matrix

noncomputable section
namespace GaussianRank

instance euclideanMeasurableSpace (K : Type*) : MeasurableSpace (EuclideanSpace ℂ K) :=
  borel (EuclideanSpace ℂ K)
instance euclideanBorelSpace (K : Type*) : BorelSpace (EuclideanSpace ℂ K) := ⟨rfl⟩

variable (E D : Type*) [Fintype E] [Fintype D]

/-- Coordinate identification between a Hilbert space and rectangular complex matrices. -/
def matrixCoordinates : EuclideanSpace ℂ (E × D) ≃L[ℂ] Matrix E D ℂ :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x e d => x (e, d)
    invFun := fun G => (WithLp.equiv 2 ((E × D) → ℂ)).symm (fun ed => G ed.1 ed.2)
    left_inv := by intro x; ext ed; rfl
    right_inv := by intro G; rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem matrixCoordinates_apply (x : EuclideanSpace ℂ (E × D)) (e : E) (d : D) :
    matrixCoordinates E D x e d = x (e, d) := rfl

/-- A normalized Gaussian law on the Hilbert space of rectangular complex matrices. -/
def matrixGaussian : Measure (Matrix E D ℂ) :=
  (radialGaussian (EuclideanSpace ℂ (E × D))).map (matrixCoordinates E D)

instance matrixGaussian_isProbabilityMeasure : IsProbabilityMeasure (matrixGaussian E D) :=
  isProbabilityMeasure_map (matrixCoordinates E D).continuous.measurable.aemeasurable

/-- Euclidean volume has the same null sets as product coordinate Lebesgue measure. -/
theorem euclideanCoordinates_quasiMeasurePreserving (K : Type*) [Fintype K] :
    QuasiMeasurePreserving (PiLp.continuousLinearEquiv 2 ℂ (fun _ : K => ℂ))
      (volume : Measure (EuclideanSpace ℂ K)) (Measure.pi (fun _ : K => (volume : Measure ℂ))) := by
  let L := PiLp.continuousLinearEquiv 2 ℂ (fun _ : K => ℂ)
  refine ⟨L.continuous.measurable, ?_⟩
  letI : SigmaFinite ((volume : Measure (EuclideanSpace ℂ K)).map L) :=
    L.toHomeomorph.measurableEmbedding.sigmaFinite_map
  exact absolutelyContinuous_isAddHaarMeasure _ _

/-- A nonzero minor remains nonzero almost everywhere for the radial Gaussian. -/
theorem ae_radial_matrix_rank :
    ∀ᵐ x ∂radialGaussian (EuclideanSpace ℂ (E × D)),
      (matrixCoordinates E D x).rank = min (Fintype.card E) (Fintype.card D) := by
  have hp := ae_matrix_rank (fun _ : E × D => (volume : Measure ℂ))
  have hv := (euclideanCoordinates_quasiMeasurePreserving (E × D)).ae hp
  exact (radialGaussian_absolutelyContinuous _).ae_le hv

/-- Rectangular matrices sampled from the actual Gaussian law have maximal rank. -/
theorem ae_matrixGaussian_rank :
    ∀ᵐ G ∂matrixGaussian E D,
      G.rank = min (Fintype.card E) (Fintype.card D) := by
  exact (matrixCoordinates E D).toHomeomorph.measurableEmbedding.ae_map_iff.mpr
    (ae_radial_matrix_rank E D)

/-- Reindexing rectangular coordinates preserves the almost-everywhere full-rank statement. -/
theorem ae_volume_matrix_rank_reindex
    (I J K : Type*) [Fintype I] [Fintype J] [Fintype K] (e : I × J ≃ K) :
    ∀ᵐ z ∂Measure.pi (fun _ : K => (volume : Measure ℂ)),
      Matrix.rank ((fun i j => z (e (i, j))) : Matrix I J ℂ) =
        min (Fintype.card I) (Fintype.card J) := by
  have he := (measurePreserving_piCongrLeft (fun _ : K => (volume : Measure ℂ)) e).symm
  have ha := he.quasiMeasurePreserving.ae (ae_matrix_rank
    (fun _ : I × J => (volume : Measure ℂ)))
  simpa [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft'] using ha

/-- Both ranks used by Gaussian whitening are maximal for this same actual Gaussian law. -/
theorem ae_matrixGaussian_whitening_rank_inputs
    (A B D : Type*) [Fintype A] [Fintype B] [Fintype D]
    (hd : Fintype.card D ≤ Fintype.card A * Fintype.card B) :
    ∀ᵐ G ∂matrixGaussian (A × B) D,
      G.rank = Fintype.card D ∧
        (PreliminariesMatrix.flatten G).rank =
          min (Fintype.card A) (Fintype.card B * Fintype.card D) := by
  apply (matrixCoordinates (A × B) D).toHomeomorph.measurableEmbedding.ae_map_iff.mpr
  have hp := ae_volume_matrix_rank_reindex A (B × D) ((A × B) × D)
    (Equiv.prodAssoc A B D).symm
  have hv := (euclideanCoordinates_quasiMeasurePreserving ((A × B) × D)).ae hp
  have hg := (radialGaussian_absolutelyContinuous (EuclideanSpace ℂ ((A × B) × D))).ae_le hv
  filter_upwards [ae_radial_matrix_rank (A × B) D, hg] with z hz1 hz2
  constructor
  · simpa only [Fintype.card_prod, min_eq_right hd] using hz1
  · simpa only [PreliminariesMatrix.flatten, matrixCoordinates_apply, Fintype.card_prod,
      Equiv.prodAssoc_symm_apply] using hz2

/-- Gaussian matrix coordinates intertwine the Euclidean unitary isometry and left multiplication. -/
theorem matrixCoordinates_unitary [DecidableEq E] [DecidableEq D]
    (U : Matrix.unitaryGroup E ℂ) (x : EuclideanSpace ℂ (E × D)) :
    matrixCoordinates E D (HaarProjection.gaussianLeftUnitaryIsometry U x) =
      (U : Matrix E E ℂ) * matrixCoordinates E D x := by
  ext e d
  simp only [matrixCoordinates_apply, HaarProjection.gaussianLeftUnitaryIsometry_apply,
    Matrix.mul_apply]

/-- The actual Gaussian matrix law is invariant under every unitary acting on its rows. -/
theorem matrixGaussian_unitary_invariant [DecidableEq E] [DecidableEq D]
    (U : Matrix.unitaryGroup E ℂ) :
    (matrixGaussian E D).map (fun G => (U : Matrix E E ℂ) * G) = matrixGaussian E D := by
  have hm : Measurable (fun G : Matrix E D ℂ => (U : Matrix E E ℂ) * G) :=
    (continuous_const.matrix_mul continuous_id).measurable
  let L := HaarProjection.gaussianLeftUnitaryIsometry (D := D) U
  have he : (fun G : Matrix E D ℂ => (U : Matrix E E ℂ) * G) ∘ matrixCoordinates E D =
      matrixCoordinates E D ∘ L := by
    funext x
    exact (matrixCoordinates_unitary E D U x).symm
  unfold matrixGaussian
  rw [Measure.map_map hm (matrixCoordinates E D).continuous.measurable, he,
    ← Measure.map_map (matrixCoordinates E D).continuous.measurable L.continuous.measurable,
    radialGaussian_isometry_invariant]

end GaussianRank

