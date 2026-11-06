import StrongConvergence.StrongConvergenceGaussConcentration
import StrongConvergence.StrongConvergenceWhiteningLipschitz
import HaarProjections.RevisionCanonicalEnsemble
import HaarProjections.HaarOrbitUnique
import HaarProjections.ProjectionOrbit
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Concentration transfer from Gaussian whitening to canonical projections

The Gaussian estimate is proved in `StrongConvergenceGaussConcentration`.
Here bounded Lipschitz extension, exact equality of the two projection laws,
and the exceptional-set error give concentration for canonical observables.
-/

open MeasureTheory Matrix GaussianRank HaarProjection
open scoped Topology BigOperators NNReal ENNReal Matrix.L2OpNorm ComplexOrder
noncomputable section

namespace ProjectionChannels.GaussConcentration

lemma exists_bounded_lipschitz_extension {V : Type*} [PseudoMetricSpace V]
    {F : V → ℝ} {A : Set V} {L : ℝ≥0} (hF : LipschitzOnWith L F A)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |F x| ≤ M) :
    ∃ g : V → ℝ, LipschitzWith L g ∧ Set.EqOn F g A ∧ ∀ x, |g x| ≤ M := by
  obtain ⟨g, hg, heq⟩ := hF.extend_real
  refine ⟨fun x => max (-M) (min (g x) M), (hg.min_const M).const_max (-M), ?_, ?_⟩
  · intro x hx
    dsimp only
    rw [← heq hx]
    have h := abs_le.mp (hbound x)
    rw [min_eq_left h.2, max_eq_right h.1]
  · intro x
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

lemma integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : Ω → ℝ}
    (hF : Measurable F) {M : ℝ} (hbound : ∀ x, |F x| ≤ M) : Integrable F μ := by
  apply (integrable_const M).mono' hF.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x)

lemma abs_integral_sub_le_of_eqOn {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F g : Ω → ℝ}
    (hF : Measurable F) (hg : Measurable g) {A : Set Ω} (hA : MeasurableSet A)
    (heq : Set.EqOn F g A) {M : ℝ}
    (hFbound : ∀ x, |F x| ≤ M) (hgbound : ∀ x, |g x| ≤ M) :
    |(∫ x, g x ∂μ) - ∫ x, F x ∂μ| ≤ 2 * M * μ.real Aᶜ := by
  rw [← integral_sub (integrable_of_abs_le hg hgbound) (integrable_of_abs_le hF hFbound)]
  have he : (fun x => g x - F x) = Aᶜ.indicator (fun x => g x - F x) := by
    funext x
    by_cases hx : x ∈ A
    · simp [hx, heq hx]
    · simp [hx]
  rw [he, integral_indicator hA.compl]
  rw [← Real.norm_eq_abs]
  apply norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top _ _)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs]
    exact (abs_sub (g x) (F x)).trans (by linarith [hgbound x, hFbound x]))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A measurable bounded function which is Lipschitz off an exceptional
set has a deterministic center with both a Gaussian tail and a controlled
distance to its actual expectation. -/
theorem exists_center_of_lipschitzOn
    {F : V → ℝ} (hF : Measurable F) {A : Set V} (hA : MeasurableSet A)
    {L : ℝ≥0} (hL : 0 < (L : ℝ)) (hLip : LipschitzOnWith L F A)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |F x| ≤ M) :
    ∃ m : ℝ,
      |m - ∫ x, F x ∂radialGaussian V| ≤ 2 * M * (radialGaussian V).real Aᶜ ∧
      ∀ r : ℝ, 0 < r →
        (radialGaussian V).real {x | r ≤ |F x-m|} ≤
          (radialGaussian V).real Aᶜ + 2 * Real.exp (-r^2 / (Real.pi^2 * (L : ℝ)^2)) := by
  obtain ⟨g, hg, heq, hgbound⟩ := exists_bounded_lipschitz_extension hLip hM hbound
  refine ⟨∫ x, g x ∂radialGaussian V,
    abs_integral_sub_le_of_eqOn hF hg.continuous.measurable hA heq hbound hgbound, ?_⟩
  intro r hr
  have hsub : {x | r ≤ |F x - ∫ y, g y ∂radialGaussian V|} ⊆
      Aᶜ ∪ {x | r ≤ |g x - ∫ y, g y ∂radialGaussian V|} := by
    intro x hx
    by_cases hxa : x ∈ A
    · exact Or.inr (by simpa only [Set.mem_setOf_eq, heq hxa] using hx)
    · exact Or.inl hxa
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add_left (radialGaussian_lipschitz_tail hg hL hgbound hr) _))

end ProjectionChannels.GaussConcentration

namespace ProjectionChannels.Canonical

/-- Gaussian whitening and the canonical projection have exactly the same
law, including the zero-column case. -/
theorem whitened_gaussian_law {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    (matrixGaussian (Index k n) (Fin (rankSequence k t n))).map whitenedProjection =
      haarProjectionLaw (baseProjection k t n) := by
  refine whitenedLaw_eq_haarProjectionLaw _ _ (matrixGaussian_unitary_invariant _ _) ?_
  filter_upwards [ae_matrixGaussian_rank (Index k n) (Fin (rankSequence k t n))] with G hG
  have hG' : G.rank = Fintype.card (Fin (rankSequence k t n)) := by
    simpa only [Fintype.card_fin, min_eq_right (rankSequence_le ht0 ht1 n)] using hG
  have hi := injective_of_full_column_rank G hG'
  exact ProjectionOrbit.exists_unitary_conjugate _ _
    (whitenedProjection_posSemidef G hi).isHermitian (whitenedProjection_idempotent G hi)
    (baseProjection_isHermitian k t n) (baseProjection_idempotent k t n)
    (by rw [whitenedProjection_rank G hi, hG', Fintype.card_fin, baseProjection_rank ht0 ht1])

def gaussianProjection (k : ℕ) (t : ℝ) (n : ℕ)
    (x : EuclideanSpace ℂ (Index k n × Fin (rankSequence k t n))) :
    Matrix (Index k n) (Index k n) ℂ :=
  whitenedProjection (matrixCoordinates (Index k n) (Fin (rankSequence k t n)) x)

theorem measurable_gaussianProjection (k : ℕ) (t : ℝ) (n : ℕ) :
    Measurable (gaussianProjection k t n) :=
  measurable_whitenedProjection.comp (matrixCoordinates _ _).continuous.measurable

theorem gaussianProjection_measurePreserving {k : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    MeasurePreserving (gaussianProjection k t n)
      (radialGaussian (EuclideanSpace ℂ (Index k n × Fin (rankSequence k t n))))
      (haarProjectionLaw (baseProjection k t n)) := by
  refine ⟨measurable_gaussianProjection k t n, ?_⟩
  change (radialGaussian _).map (whitenedProjection ∘ matrixCoordinates _ _) = _
  rw [← Measure.map_map
    measurable_whitenedProjection (matrixCoordinates _ _).continuous.measurable]
  exact whitened_gaussian_law ht0 ht1 n

theorem projection_measurePreserving (k : ℕ) (t : ℝ) (n : ℕ) :
    MeasurePreserving (fun ω => projection k t ω n)
      (probability k) (haarProjectionLaw (baseProjection k t n)) :=
  ⟨(continuous_unitary_orbit _).measurable.comp (evaluation_measurePreserving k n).measurable,
    projection_haar_law k t n⟩

theorem projection_event_eq_gaussian {k : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ)
    (s : Set (Matrix (Index k n) (Index k n) ℂ)) (hs : MeasurableSet s) :
    probability k {ω | projection k t ω n ∈ s} =
      radialGaussian (EuclideanSpace ℂ (Index k n × Fin (rankSequence k t n)))
        {x | gaussianProjection k t n x ∈ s} := by
  exact (projection_measurePreserving k t n).measure_preimage hs.nullMeasurableSet |>.trans
    ((gaussianProjection_measurePreserving ht0 ht1 n).measure_preimage hs.nullMeasurableSet).symm

theorem projection_integral_eq_gaussian {k : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ)
    (Φ : Matrix (Index k n) (Index k n) ℂ → ℝ) (hΦ : Measurable Φ) :
    (∫ ω, Φ (projection k t ω n) ∂probability k) =
      ∫ x, Φ (gaussianProjection k t n x)
        ∂radialGaussian (EuclideanSpace ℂ (Index k n × Fin (rankSequence k t n))) := by
  calc
    _ = ∫ P, Φ P ∂(probability k).map (fun ω => projection k t ω n) :=
      (integral_map (projection_measurePreserving k t n).measurable.aemeasurable
        hΦ.aestronglyMeasurable).symm
    _ = ∫ P, Φ P ∂haarProjectionLaw (baseProjection k t n) := by
      rw [projection_haar_law]
    _ = _ := by
      rw [← (gaussianProjection_measurePreserving ht0 ht1 n).map_eq]
      exact integral_map (measurable_gaussianProjection k t n).aemeasurable
        hΦ.aestronglyMeasurable

set_option maxHeartbeats 800000 in
/-- Concentration for any measurable bounded Lipschitz observable of
orthogonal projections. Only the lower-frame failure probability remains
on the right; the Gaussian concentration and exact law transfer are proved. -/
theorem exists_projection_center {k : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ)
    (Φ : Matrix (Index k n) (Index k n) ℂ → ℝ) (hΦ : Measurable Φ)
    {H M s : ℝ} (hH : 0 < H) (hM : 0 ≤ M) (hs : 0 < s)
    (hbound : ∀ P : Matrix (Index k n) (Index k n) ℂ,
      P.IsHermitian → P*P = P → |Φ P| ≤ M)
    (hLip : ∀ P Q : Matrix (Index k n) (Index k n) ℂ,
      P.IsHermitian → Q.IsHermitian → P*P = P → Q*Q = Q →
      |Φ P - Φ Q| ≤ H * ‖P-Q‖) :
    ∃ m : ℝ,
      |m - ∫ ω, Φ (projection k t ω n) ∂probability k| ≤
        2 * M * (matrixGaussian (Index k n) (Fin (rankSequence k t n))).real
          {G | ¬ StrongConvergence.LowerFrame s G} ∧
      ∀ r : ℝ, 0 < r →
        (probability k).real {ω | r ≤ |Φ (projection k t ω n)-m|} ≤
          (matrixGaussian (Index k n) (Fin (rankSequence k t n))).real
            {G | ¬ StrongConvergence.LowerFrame s G} +
          2 * Real.exp (-(s^2*r^2)/(4*Real.pi^2*H^2)) := by
  let V := EuclideanSpace ℂ (Index k n × Fin (rankSequence k t n))
  let A : Set V := {x | StrongConvergence.LowerFrame s (matrixCoordinates _ _ x)}
  let F : V → ℝ := fun x => Φ (gaussianProjection k t n x)
  have hA : MeasurableSet A :=
    (StrongConvergence.isClosed_lowerFrame s).measurableSet.preimage
      (matrixCoordinates _ _).continuous.measurable
  have hFb : ∀ x, |F x| ≤ M := fun x => hbound _
    (StrongConvergence.whitenedProjection_isHermitian_all _)
    (StrongConvergence.whitenedProjection_idempotent_all _)
  have hFl : LipschitzOnWith ⟨2*H/s, by positivity⟩ F A := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm]
    dsimp only [F, NNReal.coe_mk]
    calc
      _ ≤ H * ‖gaussianProjection k t n x - gaussianProjection k t n y‖ :=
        hLip _ _ (StrongConvergence.whitenedProjection_isHermitian_all _)
          (StrongConvergence.whitenedProjection_isHermitian_all _)
          (StrongConvergence.whitenedProjection_idempotent_all _)
          (StrongConvergence.whitenedProjection_idempotent_all _)
      _ ≤ H * ((2/s) * ‖x-y‖) := by
        gcongr
        exact (StrongConvergence.norm_whitenedProjection_sub_le_common hs hx hy).trans
          (mul_le_mul_of_nonneg_left (StrongConvergence.matrixCoordinates_opNorm_sub_le x y)
            (by positivity))
      _ = _ := by ring
  have hbad : (radialGaussian V).real Aᶜ =
      (matrixGaussian (Index k n) (Fin (rankSequence k t n))).real
        {G | ¬ StrongConvergence.LowerFrame s G} := by
    apply congrArg ENNReal.toReal
    exact ((matrixCoordinates (Index k n) (Fin (rankSequence k t n))).toHomeomorph.measurableEmbedding.map_apply
      (radialGaussian V) {G | ¬ StrongConvergence.LowerFrame s G}).symm
  obtain ⟨m, hm, htail⟩ := GaussConcentration.exists_center_of_lipschitzOn
    (hΦ.comp (measurable_gaussianProjection k t n)) hA
    (show 0 < (⟨2*H/s, by positivity⟩ : ℝ≥0).val by dsimp; positivity)
    hFl hM hFb
  refine ⟨m, ?_, ?_⟩
  · rw [projection_integral_eq_gaussian ht0 ht1 n Φ hΦ, ← hbad]
    exact hm
  · intro r hr
    have hevent := congrArg ENNReal.toReal (projection_event_eq_gaussian ht0 ht1 n
      {P | r ≤ |Φ P-m|} (measurableSet_le measurable_const ((hΦ.sub_const m).abs)))
    rw [show (probability k).real {ω | r ≤ |Φ (projection k t ω n)-m|} =
      (radialGaussian V).real {x | r ≤ |F x-m|} from hevent]
    have he : -r^2 / (Real.pi^2 * (2*H/s)^2) = -(s^2*r^2)/(4*Real.pi^2*H^2) := by
      field_simp [hs.ne', hH.ne', Real.pi_ne_zero]
      ring
    rw [← hbad]
    simpa only [NNReal.coe_mk, he] using htail r hr

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.GaussConcentration.exists_center_of_lipschitzOn
#print axioms ProjectionChannels.Canonical.whitened_gaussian_law
#print axioms ProjectionChannels.Canonical.projection_event_eq_gaussian
#print axioms ProjectionChannels.Canonical.projection_integral_eq_gaussian
#print axioms ProjectionChannels.Canonical.exists_projection_center
