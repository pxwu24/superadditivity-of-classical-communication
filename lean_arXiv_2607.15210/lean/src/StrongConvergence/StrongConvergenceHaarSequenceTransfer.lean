import HaarProjections.ProjectionOrbit
import StrongConvergence.StrongConvergenceGenusMomentBound
import StrongConvergence.StrongConvergenceProbability

/-! Coordinate Haar-law transport to arbitrary probability spaces.  Only marginal
laws and summable coordinate tails are used; no independence is required. -/
open Matrix MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
noncomputable section

namespace HaarProjection
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The Haar orbit law of a Hermitian projection depends only on its rank. -/
theorem haarProjectionLaw_eq_of_rank_eq (P Q : Matrix E E ℂ)
    (hP : P.IsHermitian) (hp : P*P=P) (hQ : Q.IsHermitian) (hq : Q*Q=Q)
    (hr : P.rank=Q.rank) : haarProjectionLaw P = haarProjectionLaw Q := by
  obtain ⟨U,hU⟩ := ProjectionOrbit.exists_unitary_conjugate P Q hP hp hQ hq hr
  rw [hU, haarProjectionLaw_conjugate_base]
end HaarProjection

namespace ProjectionChannels

/-- The exact hypotheses on a Haar projection sequence in the original random
compression target, with no requirement on its joint coordinate law. -/
structure HaarSequence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (k : ℕ)
    (d : ℕ → ℕ)
    (P₀ : (n : ℕ) → Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ)
    (P : Ω → (n : ℕ) → Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ) : Prop where
  base_isHermitian : ∀ n, (P₀ n).IsHermitian
  base_idempotent : ∀ n, P₀ n * P₀ n = P₀ n
  base_rank : ∀ n, (P₀ n).rank = d n
  isHermitian : ∀ ω n, (P ω n).IsHermitian
  idempotent : ∀ ω n, P ω n * P ω n = P ω n
  measurable : ∀ n, Measurable (fun ω => P ω n)
  law : ∀ n, μ.map (fun ω => P ω n) = HaarProjection.haarProjectionLaw (P₀ n)

namespace HaarSequence
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ} {d : ℕ → ℕ}
variable {P₀ : (n : ℕ) → Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ}
variable {P : Ω → (n : ℕ) → Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ}

/-- Rank density on the positive input-dimension indexing of the target. -/
def density (k : ℕ) (d : ℕ → ℕ) (n : ℕ) : ℝ :=
  (d n : ℝ) / (((n+1)*k : ℕ) : ℝ)

lemma rank_le (h : HaarSequence μ k d P₀ P) (n : ℕ) : d n ≤ (n+1)*k := by
  rw [← h.base_rank n]
  simpa [Canonical.Index] using Matrix.rank_le_card_width (P₀ n)

lemma density_nonneg (k : ℕ) (d : ℕ → ℕ) (n : ℕ) : 0 ≤ density k d n := by
  unfold density
  positivity

lemma density_le_one (h : HaarSequence μ k d P₀ P) (hk : 0<k) (n : ℕ) :
    density k d n ≤ 1 := by
  unfold density
  rw [div_le_one (by positivity : (0:ℝ)<(((n+1)*k : ℕ):ℝ))]
  exact_mod_cast h.rank_le n

lemma canonical_base_rank (h : HaarSequence μ k d P₀ P) (hk : 0<k) (n : ℕ) :
    (Canonical.baseProjection k (density k d n) n).rank = d n := by
  rw [Canonical.baseProjection_rank (density_nonneg k d n) (h.density_le_one hk n)]
  exact Canonical.rankSequence_exact_density hk n (d n)

/-- Equality of every coordinate marginal with the variable-density canonical
ensemble realizing the original integer ranks exactly. -/
theorem marginal_eq_canonical (h : HaarSequence μ k d P₀ P) (hk : 0<k) (n : ℕ) :
    μ.map (fun ω => P ω n) =
      (Canonical.probability k).map (fun ω => Canonical.projection k (density k d n) ω n) := by
  rw [h.law, Canonical.projection_haar_law]
  apply HaarProjection.haarProjectionLaw_eq_of_rank_eq _ _
    (h.base_isHermitian n) (h.base_idempotent n)
    (Canonical.baseProjection_isHermitian _ _ _) (Canonical.baseProjection_idempotent _ _ _)
  rw [h.base_rank, h.canonical_base_rank hk]

lemma canonical_measurable (k : ℕ) (s : ℕ → ℝ) (n : ℕ) :
    Measurable (fun ω : Canonical.Sample k => Canonical.projection k (s n) ω n) :=
  (HaarProjection.continuous_unitary_orbit (Canonical.baseProjection k (s n) n)).measurable.comp
    (continuous_apply n).measurable
/-- Conjugating by any fixed output unitary preserves the full Haar-sequence
interface, including all marginals, without changing the base projections. -/
theorem localConjugate (h : HaarSequence μ k d P₀ P) (U : Matrix.unitaryGroup (Fin k) ℂ) :
    HaarSequence μ k d P₀ (fun ω n => RevisionOutput.localConjugate (P ω n) U) := by
  have hC (n : ℕ) : Measurable (fun Q : Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ =>
      RevisionOutput.localConjugate Q U) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  refine ⟨h.base_isHermitian, h.base_idempotent, h.base_rank,
    (fun ω n => RevisionOutput.localConjugate_isHermitian (h.isHermitian ω n) U), ?_,
    (fun n => (hC n).comp (h.measurable n)), ?_⟩
  · intro ω n
    let V := RevisionOutput.liftedOutputUnitary (A := Fin (n+1)) U
    have hv : (V : Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ).conjTranspose * V = 1 := V.prop.1
    have he (Q : Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ) :
        RevisionOutput.localConjugate Q U = (V : Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ)*Q*(V : Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ).conjTranspose := by
      simp only [V, RevisionOutput.liftedOutputUnitary, RevisionOutput.localConjugate,
        RevisionOutput.local_kronecker_conjTranspose, Matrix.conjTranspose_conjTranspose]
    rw [he]
    calc
      _ = (V : Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ) *
          (P ω n * ((V : Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ).conjTranspose *
            (V : Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ)) * P ω n) *
          (V : Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ).conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hv, Matrix.mul_one, h.idempotent]
  · intro n
    change μ.map ((fun Q => RevisionOutput.localConjugate Q U) ∘ (fun ω => P ω n)) = _
    rw [← Measure.map_map (hC n) (h.measurable n), h.law]
    exact RevisionOutput.haarProjectionLaw_localConjugate_invariant (P₀ n) U

end HaarSequence

namespace HaarSequenceTransfer
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : Measure Ω} {ν : Measure Ω'}
variable {B : ℕ → Type*} [∀ n, MeasurableSpace (B n)]
variable (X : (n : ℕ) → Ω → B n) (Y : (n : ℕ) → Ω' → B n)
variable (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
variable (hLaw : ∀ n, μ.map (X n) = ν.map (Y n))
include hX hY hLaw

lemma coordinate_event_measure_eq (n : ℕ) (S : Set (B n)) (hS : MeasurableSet S) :
    μ {ω | X n ω ∈ S} = ν {ω | Y n ω ∈ S} := by
  change μ ((X n) ⁻¹' S) = ν ((Y n) ⁻¹' S)
  rw [← Measure.map_apply (hX n) hS, hLaw n, Measure.map_apply (hY n) hS]

/-- Summable tails transfer coordinate by coordinate, regardless of dependence. -/
theorem tsum_coordinate_events_eq (S : (n : ℕ) → Set (B n)) (hS : ∀ n, MeasurableSet (S n)) :
    (∑' n, μ {ω | X n ω ∈ S n}) = ∑' n, ν {ω | Y n ω ∈ S n} := by
  congr 1
  funext n
  exact coordinate_event_measure_eq X Y hX hY hLaw n (S n) (hS n)

/-- The first Borel--Cantelli conclusion under arbitrary coordinate dependence. -/
theorem ae_eventually_avoid (S : (n : ℕ) → Set (B n)) (hS : ∀ n, MeasurableSet (S n))
    (hSum : (∑' n, ν {ω | Y n ω ∈ S n}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, X n ω ∉ S n := by
  apply ae_eventually_not_mem
  change (∑' n, μ {ω | X n ω ∈ S n}) ≠ ∞
  rw [tsum_coordinate_events_eq X Y hX hY hLaw S hS]
  exact hSum

lemma coordinate_integral_eq (n : ℕ) (f : B n → ℝ) (hf : Measurable f) :
    (∫ ω, f (X n ω) ∂μ) = ∫ ω, f (Y n ω) ∂ν := by
  rw [← integral_map (hX n).aemeasurable hf.stronglyMeasurable.aestronglyMeasurable,
    hLaw n, integral_map (hY n).aemeasurable hf.stronglyMeasurable.aestronglyMeasurable]

lemma coordinate_integrable_iff (n : ℕ) (f : B n → ℝ) (hf : Measurable f) :
    Integrable (fun ω => f (X n ω)) μ ↔ Integrable (fun ω => f (Y n ω)) ν := by
  change Integrable (f ∘ X n) μ ↔ Integrable (f ∘ Y n) ν
  rw [← integrable_map_measure hf.stronglyMeasurable.aestronglyMeasurable (hX n).aemeasurable,
    hLaw n, integrable_map_measure hf.stronglyMeasurable.aestronglyMeasurable (hY n).aemeasurable]

/-- Countably many centered real tests converge almost surely on the new
probability space whenever their canonical centered tails are summable. -/
theorem ae_countable_tendsto_of_centered_tails {ι : Type*} [Countable ι]
    (F : (n : ℕ) → ι → B n → ℝ) (hF : ∀ n i, Measurable (F n i))
    (center : ℕ → ι → ℝ) (L : ι → ℝ)
    (hcenter : ∀ i, Tendsto (fun n => center n i) atTop (𝓝 (L i)))
    (hTail : ∀ i (m : ℕ),
      (∑' n, ν {ω | 1/((m:ℝ)+1) ≤ |F n i (Y n ω)-center n i|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => F n i (X n ω)) atTop (𝓝 (L i)) := by
  apply StrongConvergenceProbability.ae_countable_tendsto_of_centered_tails μ
    (fun ω n i => F n i (X n ω)) center L hcenter
  intro i m
  apply ne_top_of_le_ne_top (hTail i m)
  exact le_of_eq (tsum_coordinate_events_eq X Y hX hY hLaw
    (fun n => {b | 1/((m:ℝ)+1) ≤ |F n i b-center n i|})
    (fun n => measurableSet_le measurable_const
      (continuous_abs.measurable.comp ((hF n i).sub measurable_const))))

/-- Complete convergence of centered coordinate tests transfers exactly. -/
lemma tsum_centered_deviations_eq (F : (n : ℕ) → B n → ℝ)
    (hF : ∀ n, Measurable (F n)) (center : ℕ → ℝ) (ε : ℝ) :
    (∑' n, μ {ω | ε ≤ |F n (X n ω)-center n|}) =
      ∑' n, ν {ω | ε ≤ |F n (Y n ω)-center n|} :=
  tsum_coordinate_events_eq X Y hX hY hLaw
    (fun n => {b | ε ≤ |F n b-center n|})
    (fun n => measurableSet_le measurable_const (continuous_abs.measurable.comp ((hF n).sub measurable_const)))

/-- Almost-sure convergence on a reference probability space and summable
centered deviations suffice for transport under equality of coordinate laws.
The deterministic centers are proved to converge by selecting a reference
sample satisfying both almost-sure limits. -/
theorem ae_tendsto_transfer_of_summable_centered [IsProbabilityMeasure ν]
    (F : (n : ℕ) → B n → ℝ) (hF : ∀ n, Measurable (F n))
    (center : ℕ → ℝ) (L : ℝ)
    (hSource : ∀ᵐ ω ∂ν, Tendsto (fun n => F n (Y n ω)) atTop (𝓝 L))
    (hTail : ∀ m : ℕ,
      (∑' n, ν {ω | 1/((m:ℝ)+1) ≤ |F n (Y n ω)-center n|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => F n (X n ω)) atTop (𝓝 L) := by
  have hdev := StrongConvergenceProbability.ae_countable_tendsto_of_summable_deviations ν
    (fun ω n (_ : Unit) => F n (Y n ω)-center n) (fun _ => (0:ℝ)) (by
      intro _ m
      simpa only [Real.dist_eq, sub_zero] using hTail m)
  obtain ⟨ω,hω,hδ⟩ := (hSource.and hdev).exists
  have hc : Tendsto center atTop (𝓝 L) := by
    have hlim := hω.sub (hδ ())
    simpa only [sub_sub_cancel, sub_zero] using hlim
  have h := ae_countable_tendsto_of_centered_tails X Y hX hY hLaw
    (fun n (_ : Unit) => F n) (fun n _ => hF n) (fun n _ => center n) (fun _ => L)
    (fun _ => hc) (fun _ m => hTail m)
  filter_upwards [h] with ω hω
  exact hω ()

end HaarSequenceTransfer
namespace HaarSequence
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ} {d : ℕ → ℕ}
variable {P₀ : (n : ℕ) → Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ}
variable {P : Ω → (n : ℕ) → Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ}

/-- Transfer an actual variable-rank canonical scalar limit to the arbitrary
Haar sequence in the original target. -/
theorem ae_tendsto_of_canonical_centered_tails (h : HaarSequence μ k d P₀ P) (hk : 0<k)
    (F : (n : ℕ) → Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ → ℝ)
    (hF : ∀ n, Measurable (F n)) (center : ℕ → ℝ) (L : ℝ)
    (hSource : ∀ᵐ ω ∂Canonical.probability k,
      Tendsto (fun n => F n (Canonical.projection k (density k d n) ω n)) atTop (𝓝 L))
    (hTail : ∀ m : ℕ,
      (∑' n, (Canonical.probability k) {ω | 1/((m:ℝ)+1) ≤
        |F n (Canonical.projection k (density k d n) ω n)-center n|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => F n (P ω n)) atTop (𝓝 L) :=
  HaarSequenceTransfer.ae_tendsto_transfer_of_summable_centered
    (fun n ω => P ω n) (fun n ω => Canonical.projection k (density k d n) ω n)
    h.measurable (canonical_measurable k (density k d)) (h.marginal_eq_canonical hk)
    F hF center L hSource hTail
end HaarSequence

end ProjectionChannels

#print axioms HaarProjection.haarProjectionLaw_eq_of_rank_eq
#print axioms ProjectionChannels.HaarSequence.marginal_eq_canonical
#print axioms ProjectionChannels.HaarSequenceTransfer.ae_countable_tendsto_of_centered_tails
#print axioms ProjectionChannels.HaarSequenceTransfer.ae_tendsto_transfer_of_summable_centered

#print axioms ProjectionChannels.HaarSequence.localConjugate
#print axioms ProjectionChannels.HaarSequence.ae_tendsto_of_canonical_centered_tails
