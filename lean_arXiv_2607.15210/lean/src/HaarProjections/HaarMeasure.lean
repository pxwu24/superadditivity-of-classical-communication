import HaarProjections.HaarProjection
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi

open scoped BigOperators ComplexOrder
open Matrix MeasureTheory Set

set_option maxHeartbeats 600000

namespace HaarProjection
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

instance matrixMeasurableSpace {I J : Type*} : MeasurableSpace (Matrix I J ℂ) :=
  inferInstanceAs (MeasurableSpace (I → J → ℂ))

instance matrixBorelSpace {I J : Type*} [Fintype I] [Fintype J] :
    BorelSpace (Matrix I J ℂ) :=
  inferInstanceAs (BorelSpace (I → J → ℂ))

instance matrixSecondCountableTopology {I J : Type*} [Fintype I] [Fintype J] :
    SecondCountableTopology (Matrix I J ℂ) :=
  inferInstanceAs (SecondCountableTopology (I → J → ℂ))


/-- The ordinary subtype topology makes the unitary matrix group a topological group. -/
instance unitaryGroupContinuousInv : ContinuousInv (Matrix.unitaryGroup E ℂ) where
  continuous_inv := by
    exact continuous_subtype_val.matrix_conjTranspose.subtype_mk _

instance unitaryGroupIsTopologicalGroup : IsTopologicalGroup (Matrix.unitaryGroup E ℂ) := ⟨⟩

/-- Every column of a unitary matrix has squared Euclidean norm one. -/
theorem unitary_column_normSq_sum (U : Matrix.unitaryGroup E ℂ) (j : E) :
    ∑ i : E, Complex.normSq (U i j) = 1 := by
  have h := congrFun (congrFun U.prop.1 j) j
  simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply_eq, Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at h
  exact_mod_cast h

/-- A unitary matrix has entries in the closed complex unit disk. -/
theorem unitary_entry_norm_le_one (U : Matrix.unitaryGroup E ℂ) (i j : E) :
    ‖U i j‖ ≤ 1 := by
  have h : Complex.normSq (U i j) ≤ 1 := by
    rw [← unitary_column_normSq_sum U j]
    exact Finset.single_le_sum (fun a _ => Complex.normSq_nonneg (U a j)) (Finset.mem_univ i)
  rw [← Complex.sq_norm] at h
  nlinarith [norm_nonneg (U i j)]

/-- The unitary equations define a closed subset of all complex matrices. -/
theorem isClosed_unitary_matrices :
    IsClosed (Matrix.unitaryGroup E ℂ : Set (Matrix E E ℂ)) := by
  have h : (Matrix.unitaryGroup E ℂ : Set (Matrix E E ℂ)) =
      {U | U.conjTranspose * U = 1} := by
    ext U
    exact Matrix.mem_unitaryGroup_iff'
  rw [h]
  exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const

/-- Compactness follows from the entrywise unit-disk bound and the closed unitary equations. -/
theorem isCompact_unitary_matrices :
    IsCompact (Matrix.unitaryGroup E ℂ : Set (Matrix E E ℂ)) := by
  let K : Set (Matrix E E ℂ) := Set.pi Set.univ
    (fun _ : E => Set.pi Set.univ (fun _ : E => Metric.closedBall (0 : ℂ) 1))
  have hK : IsCompact K :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  apply hK.of_isClosed_subset isClosed_unitary_matrices
  intro U hU i hi j hj
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    unitary_entry_norm_le_one (⟨U, hU⟩ : Matrix.unitaryGroup E ℂ) i j

instance unitaryGroupCompactSpace : CompactSpace (Matrix.unitaryGroup E ℂ) :=
  isCompact_iff_compactSpace.mp isCompact_unitary_matrices

instance unitaryGroupMeasurableSpace : MeasurableSpace (Matrix.unitaryGroup E ℂ) :=
  borel (Matrix.unitaryGroup E ℂ)

instance unitaryGroupBorelSpace : BorelSpace (Matrix.unitaryGroup E ℂ) := ⟨rfl⟩

/-- Normalized Haar probability measure on the finite-dimensional complex unitary group. -/
def unitaryHaar : Measure (Matrix.unitaryGroup E ℂ) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup E ℂ))

instance unitaryHaar_isProbabilityMeasure : IsProbabilityMeasure (unitaryHaar (E := E)) where
  measure_univ := by
    simpa only [unitaryHaar, TopologicalSpace.PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ :=
        (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup E ℂ))))


instance unitaryHaar_isHaarMeasure : Measure.IsHaarMeasure (unitaryHaar (E := E)) := by
  unfold unitaryHaar
  infer_instance

/-- Compact-group Haar probability is invariant also under right multiplication. -/
instance unitaryHaar_isMulRightInvariant :
    Measure.IsMulRightInvariant (unitaryHaar (E := E)) where
  map_mul_right_eq_self U := by
    letI : IsProbabilityMeasure ((unitaryHaar (E := E)).map (· * U)) :=
      MeasureTheory.isProbabilityMeasure_map (measurable_mul_const U).aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- A Haar-random projection is the unitary orbit of a fixed projection. -/
def haarProjectionLaw (P₀ : Matrix E E ℂ) : Measure (Matrix E E ℂ) :=
  (unitaryHaar (E := E)).map
    (fun U : Matrix.unitaryGroup E ℂ => (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose)

/-- The unitary orbit map is continuous. -/
theorem continuous_unitary_orbit (P₀ : Matrix E E ℂ) :
    Continuous (fun U : Matrix.unitaryGroup E ℂ =>
      (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose) :=
  (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
    continuous_subtype_val.matrix_conjTranspose

instance haarProjectionLaw_isProbabilityMeasure (P₀ : Matrix E E ℂ) :
    IsProbabilityMeasure (haarProjectionLaw P₀) :=
  MeasureTheory.isProbabilityMeasure_map (continuous_unitary_orbit P₀).measurable.aemeasurable


/-- The Haar projection law is invariant under conjugating the random output. -/
theorem haarProjectionLaw_conjugation_invariant (P₀ : Matrix E E ℂ)
    (V : Matrix.unitaryGroup E ℂ) :
    (haarProjectionLaw P₀).map
      (fun P => (V : Matrix E E ℂ) * P * (V : Matrix E E ℂ).conjTranspose) =
      haarProjectionLaw P₀ := by
  have hc : Measurable (fun P : Matrix E E ℂ =>
      (V : Matrix E E ℂ) * P * (V : Matrix E E ℂ).conjTranspose) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  unfold haarProjectionLaw
  rw [Measure.map_map hc (continuous_unitary_orbit P₀).measurable]
  have he : (fun P : Matrix E E ℂ =>
      (V : Matrix E E ℂ) * P * (V : Matrix E E ℂ).conjTranspose) ∘
        (fun U : Matrix.unitaryGroup E ℂ =>
          (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose) =
      (fun U : Matrix.unitaryGroup E ℂ =>
        (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose) ∘ (V * ·) := by
    funext U
    simp only [Function.comp_apply, Matrix.UnitaryGroup.mul_val,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he, ← Measure.map_map (continuous_unitary_orbit P₀).measurable (measurable_const_mul V),
    map_mul_left_eq_self]

/-- Conjugate base projections produce the same Haar orbit law. -/
theorem haarProjectionLaw_conjugate_base (P₀ : Matrix E E ℂ)
    (V : Matrix.unitaryGroup E ℂ) :
    haarProjectionLaw ((V : Matrix E E ℂ) * P₀ * (V : Matrix E E ℂ).conjTranspose) =
      haarProjectionLaw P₀ := by
  unfold haarProjectionLaw
  have he : (fun U : Matrix.unitaryGroup E ℂ =>
      (U : Matrix E E ℂ) * ((V : Matrix E E ℂ) * P₀ * (V : Matrix E E ℂ).conjTranspose) *
        (U : Matrix E E ℂ).conjTranspose) =
      (fun U : Matrix.unitaryGroup E ℂ =>
        (U : Matrix E E ℂ) * P₀ * (U : Matrix E E ℂ).conjTranspose) ∘ (· * V) := by
    funext U
    simp only [Function.comp_apply, Matrix.UnitaryGroup.mul_val,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he, ← Measure.map_map (continuous_unitary_orbit P₀).measurable (measurable_mul_const V),
    map_mul_right_eq_self]

/-- Matrix inversion, defined as zero at singular matrices, is Borel measurable. -/
theorem measurable_matrix_inverse : Measurable (Inv.inv : Matrix E E ℂ → Matrix E E ℂ) := by
  have hdet : Measurable (fun M : Matrix E E ℂ => (M.det)⁻¹) :=
    continuous_id.matrix_det.measurable.inv
  have hadj : Measurable (fun M : Matrix E E ℂ => M.adjugate) :=
    continuous_id.matrix_adjugate.measurable
  change Measurable (fun M : Matrix E E ℂ => M⁻¹)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact hdet.smul hadj

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The Gram-normalization map used in Gaussian realization is measurable. -/
theorem measurable_whitenedProjection :
    Measurable (whitenedProjection : Matrix E D ℂ → Matrix E E ℂ) := by
  have hgram : Measurable (fun G : Matrix E D ℂ => G.conjTranspose * G) :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).measurable
  have hinv := (measurable_matrix_inverse (E := D)).comp hgram
  have hprod : Measurable (fun G : Matrix E D ℂ => G * (G.conjTranspose * G)⁻¹) :=
    (continuous_fst.matrix_mul continuous_snd).measurable.comp
      (measurable_id.prodMk hinv)
  exact (continuous_fst.matrix_mul continuous_snd).measurable.comp
    (hprod.prodMk continuous_id.matrix_conjTranspose.measurable)

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The input partial trace is a continuous linear operation in finite dimension. -/
theorem continuous_traceB :
    Continuous (PreliminariesMatrix.traceB : Matrix (A × B) (A × B) ℂ → Matrix A A ℂ) := by
  apply continuous_matrix
  intro a b
  exact continuous_finset_sum _ (fun i _ => continuous_id.matrix_elem (a, i) (b, i))

/-- The reshaping operation is continuous. -/
theorem continuous_flatten :
    Continuous (PreliminariesMatrix.flatten : Matrix (A × B) D ℂ → Matrix A (B × D) ℂ) := by
  apply continuous_matrix
  intro a bd
  exact continuous_id.matrix_elem (a, bd.1) bd.2

end
end HaarProjection

