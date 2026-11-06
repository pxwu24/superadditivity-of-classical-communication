import RandomCompression.RevisionFullBlockInput
import Mathlib.Analysis.SpecificLimits.Basic

/-! A concrete Haar-projection ensemble. Its sample space is the compact
countable product of the finite unitary groups, equipped with normalized
Haar probability. Every coordinate has exactly the required Haar law.
The canonical strong-convergence proposition is then stated for this
specified ensemble, not for an unspecified existential model. -/

open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.Canonical

abbrev Index (k n : ℕ) := Fin (n+1) × Fin k
abbrev Sample (k : ℕ) := ∀ n : ℕ, Matrix.unitaryGroup (Index k n) ℂ

instance unitarySecondCountable (k n : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Index k n) ℂ) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance sampleMeasurableSpace (k : ℕ) : MeasurableSpace (Sample k) := borel (Sample k)
instance sampleBorelSpace (k : ℕ) : BorelSpace (Sample k) := ⟨rfl⟩

def probability (k : ℕ) : Measure (Sample k) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Sample k))

instance probability_isProbabilityMeasure (k : ℕ) : IsProbabilityMeasure (probability k) where
  measure_univ := by
    simpa only [probability,TopologicalSpace.PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Sample k))))

instance probability_isHaarMeasure (k : ℕ) : Measure.IsHaarMeasure (probability k) := by
  unfold probability
  infer_instance

def evaluation (k n : ℕ) : Sample k →* Matrix.unitaryGroup (Index k n) ℂ where
  toFun ω := ω n
  map_one' := rfl
  map_mul' _ _ := rfl

theorem evaluation_measurePreserving (k n : ℕ) :
    MeasurePreserving (evaluation k n) (probability k) HaarProjection.unitaryHaar := by
  apply MonoidHom.measurePreserving
  · exact continuous_apply n
  · intro U
    refine ⟨Function.update (fun _ => 1) n U,?_⟩
    simp [evaluation]
  · simp

/-- Joint coordinate projections have the finite product Haar law. This
records the independence of the canonical unitary sequence. -/
def finiteEvaluation (k : ℕ) (s : Finset ℕ) :
    Sample k →* (∀ n : s, Matrix.unitaryGroup (Index k n) ℂ) where
  toFun ω n := ω n
  map_one' := rfl
  map_mul' _ _ := rfl

theorem finiteEvaluation_measurePreserving (k : ℕ) (s : Finset ℕ) :
    MeasurePreserving (finiteEvaluation k s) (probability k)
      (Measure.pi (fun n : s => HaarProjection.unitaryHaar (E:=Index k n))) := by
  classical
  letI : BorelSpace (∀ n : s, Matrix.unitaryGroup (Index k n) ℂ) := Pi.borelSpace
  apply MonoidHom.measurePreserving
  · exact continuous_pi (fun n => continuous_apply n.val)
  · intro U
    refine ⟨fun n => if hn : n∈s then U ⟨n,hn⟩ else 1,?_⟩
    funext n
    simp [finiteEvaluation,n.property]
  · simp

def rankSequence (k : ℕ) (t : ℝ) (n : ℕ) : ℕ := ⌊t*((k:ℝ)*(n+1))⌋₊

lemma rankSequence_le {k : ℕ} {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) (n : ℕ) :
    rankSequence k t n ≤ Fintype.card (Index k n) := by
  have hN : 0≤(k:ℝ)*(n+1) := by positivity
  have hle := Nat.floor_le (mul_nonneg ht0 hN)
  have hprod := mul_le_of_le_one_left hN ht1
  have hcast : (Fintype.card (Index k n):ℝ) = (k:ℝ)*(n+1) := by
    simp [Index,Fintype.card_prod]
    ring
  unfold rankSequence
  have hh : (⌊t*((k:ℝ)*(n+1))⌋₊:ℝ) ≤ (Fintype.card (Index k n):ℝ) :=
    hle.trans (hprod.trans_eq hcast.symm)
  exact_mod_cast hh

def coordinateNumber (k n : ℕ) : Index k n ≃ Fin (Fintype.card (Index k n)) := Fintype.equivFin _

def baseProjection (k : ℕ) (t : ℝ) (n : ℕ) : Matrix (Index k n) (Index k n) ℂ :=
  Matrix.diagonal (fun i => if (coordinateNumber k n i).val < rankSequence k t n then 1 else 0)

theorem baseProjection_isHermitian (k : ℕ) (t : ℝ) (n : ℕ) :
    (baseProjection k t n).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  split_ifs <;> simp

theorem baseProjection_idempotent (k : ℕ) (t : ℝ) (n : ℕ) :
    baseProjection k t n*baseProjection k t n=baseProjection k t n := by
  unfold baseProjection
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · simp [Matrix.diagonal_apply,hij]

theorem baseProjection_rank {k : ℕ} {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) (n : ℕ) :
    (baseProjection k t n).rank = rankSequence k t n := by
  classical
  rw [baseProjection,Matrix.rank_diagonal]
  let d := rankSequence k t n
  let e := coordinateNumber k n
  have hd : d≤Fintype.card (Index k n) := rankSequence_le ht0 ht1 n
  let f : {i : Index k n // (if (e i).val<d then (1:ℂ) else 0)≠0} ≃ Fin d :=
    { toFun := fun i => ⟨(e i.val).val,by
          by_contra h
          have hh := i.property
          simp [h] at hh⟩
      invFun := fun j => ⟨e.symm ⟨j.val,j.isLt.trans_le hd⟩,by simp [j.isLt]⟩
      left_inv := by intro i; apply Subtype.ext; apply e.injective; simp
      right_inv := by intro j; apply Fin.ext; simp }
  change Fintype.card {i : Index k n // (if (e i).val<d then (1:ℂ) else 0)≠0}=d
  rw [Fintype.card_congr f,Fintype.card_fin]

def projection (k : ℕ) (t : ℝ) (ω : Sample k) (n : ℕ) :
    Matrix (Index k n) (Index k n) ℂ :=
  (ω n : Matrix (Index k n) (Index k n) ℂ)*baseProjection k t n*
    (ω n : Matrix (Index k n) (Index k n) ℂ).conjTranspose

theorem projection_isHermitian (k : ℕ) (t : ℝ) (ω : Sample k) (n : ℕ) :
    (projection k t ω n).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ (baseProjection_isHermitian k t n)

theorem projection_idempotent (k : ℕ) (t : ℝ) (ω : Sample k) (n : ℕ) :
    projection k t ω n*projection k t ω n=projection k t ω n := by
  have hU : (ω n : Matrix (Index k n) (Index k n) ℂ).conjTranspose *
      (ω n : Matrix (Index k n) (Index k n) ℂ)=1 := (ω n).prop.1
  unfold projection
  calc
    _ = (ω n : Matrix (Index k n) (Index k n) ℂ)*
        (baseProjection k t n*((ω n : Matrix (Index k n) (Index k n) ℂ).conjTranspose *
          (ω n : Matrix (Index k n) (Index k n) ℂ))*baseProjection k t n)*
        (ω n : Matrix (Index k n) (Index k n) ℂ).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU,Matrix.mul_one,baseProjection_idempotent]

theorem projection_rank {k : ℕ} {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1)
    (ω : Sample k) (n : ℕ) : (projection k t ω n).rank=rankSequence k t n := by
  rw [projection,HaarProjection.unitary_conjugation_rank,baseProjection_rank ht0 ht1]

theorem projection_haar_law (k : ℕ) (t : ℝ) (n : ℕ) :
    (probability k).map (fun ω => projection k t ω n) =
      HaarProjection.haarProjectionLaw (baseProjection k t n) := by
  have he := (evaluation_measurePreserving k n).map_eq
  rw [HaarProjection.haarProjectionLaw,← he,Measure.map_map
    (HaarProjection.continuous_unitary_orbit _).measurable (evaluation_measurePreserving k n).measurable]
  rfl

theorem rank_density_tendsto {k : ℕ} {t : ℝ} (hk : 0<k) (ht : 0≤t) :
    Tendsto (fun n => (rankSequence k t n:ℝ)/((k:ℝ)*(n+1))) atTop (𝓝 t) := by
  apply (tendsto_nat_floor_mul_div_atTop ht).comp
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact hn.const_mul_atTop (by exact_mod_cast hk)

/-- The canonical strong-convergence proposition, proved by
`ProjectionChannels.Canonical.canonicalStrongInput` in
`StrongConvergence.StrongConvergenceCanonicalStrong`. -/
def CanonicalStrongInput : Prop :=
  ∀ k : ℕ, 0<k → ∀ t : ℝ, 0<t → t<1 →
    FullBlockModifiedStrongInput (probability k) k t (projection k t) (projection_isHermitian k t)

end Canonical
end ProjectionChannels
