import StrongConvergence.StrongConvergenceScalar
import StrongConvergence.StrongConvergenceScalarProjectionTrace

/-!
# Unmodified canonical projections: the unconditional norm limit in every dimension

The scalar spectral convergence of P_n itself requires no asymptotic freeness:
a finite projection already has only the eigenvalues zero and one. The floor
rank sequence ensures both eigenspaces are nonzero eventually. This file
establishes the scalar premise used in the full block-modified convergence
development; see `StrongConvergenceHaarSequenceStrong` for the general theorem.
-/

open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace ProjectionChannels.ScalarStrong
set_option maxHeartbeats 800000

lemma canonical_projection_mem_spectrum_all (k : ℕ) (t : ℝ) (ω : Canonical.Sample k) (n : ℕ)
    (i : Canonical.Index k n) :
    (if (Canonical.coordinateNumber k n i).val<Canonical.rankSequence k t n then (1:ℝ) else 0)
      ∈ spectrum ℝ (Canonical.projection k t ω n) := by
  unfold Canonical.projection
  change _∈spectrum ℝ ((ω n:Matrix _ _ ℂ)*Canonical.baseProjection k t n*star (ω n:Matrix _ _ ℂ))
  rw [unitary.spectrum.unitary_conjugate,←spectrum.algebraMap_mem_iff ℂ]
  unfold Canonical.baseProjection
  rw [spectrum_diagonal]
  refine ⟨i,?_⟩
  split_ifs <;> simp_all [Algebra.algebraMap_eq_smul_one]

lemma canonical_rank_eventually_nontrivial_all {k : ℕ} (hk : 0<k) {t : ℝ}
    (ht0 : 0<t) (ht1 : t<1) :
    ∀ᶠ n:ℕ in atTop, 0<Canonical.rankSequence k t n ∧
      Canonical.rankSequence k t n<Fintype.card (Canonical.Index k n) := by
  have h := Canonical.rank_density_tendsto hk ht0.le
  have he := h.eventually (Ioo_mem_nhds ht0 ht1)
  filter_upwards [he] with n hn
  have hd : (0:ℝ)<(k:ℝ)*((n:ℝ)+1) := mul_pos (Nat.cast_pos.mpr hk) (by positivity)
  have hpos : (0:ℝ)<(Canonical.rankSequence k t n:ℝ) :=
    (div_pos_iff_of_pos_right hd).mp hn.1
  have hlt : (Canonical.rankSequence k t n:ℝ)<(k:ℝ)*((n:ℝ)+1) :=
    (div_lt_one hd).mp hn.2
  constructor
  · exact_mod_cast hpos
  · have heq : (Fintype.card (Canonical.Index k n):ℝ)=(k:ℝ)*((n:ℝ)+1) := by
      simp [Canonical.Index,Fintype.card_prod]
      ring
    rw [←heq] at hlt
    exact_mod_cast hlt

/-- Eventual exact affine operator norms hold for every canonical sample
and every fixed positive output dimension. -/
theorem canonical_projection_affine_norm_eventually {k : ℕ} (hk : 0<k) {t : ℝ}
    (ht0 : 0<t) (ht1 : t<1) (ω : Canonical.Sample k) (a c : ℝ) :
    ∀ᶠ n:ℕ in atTop,
      ‖(c:ℂ) • (1:Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ)+
        (a:ℂ) • Canonical.projection k t ω n‖=max |c| |c+a| := by
  letI : NeZero k := ⟨by omega⟩
  filter_upwards [canonical_rank_eventually_nontrivial_all hk ht0 ht1] with n hn
  apply norm_affine_projection _ (Canonical.projection_isHermitian k t ω n)
    (Canonical.projection_idempotent k t ω n)
  · let j : Fin (Fintype.card (Canonical.Index k n)) := ⟨Canonical.rankSequence k t n,hn.2⟩
    have h := canonical_projection_mem_spectrum_all k t ω n ((Canonical.coordinateNumber k n).symm j)
    simpa [j] using h
  · let j : Fin (Fintype.card (Canonical.Index k n)) := ⟨0,Fintype.card_pos⟩
    have h := canonical_projection_mem_spectrum_all k t ω n ((Canonical.coordinateNumber k n).symm j)
    simpa [j,hn.1] using h

/-- Unconditional affine norm convergence for the unmodified projection,
against its actual dilated Bernoulli probability measure. -/
theorem canonical_projection_affine_norm_tendsto {k : ℕ} (hk : 0<k) {t : ℝ}
    (ht0 : 0<t) (ht1 : t<1) (ω : Canonical.Sample k) (a c : ℝ) :
    Tendsto (fun n=>‖(c:ℂ) • (1:Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ)+
        (a:ℂ) • Canonical.projection k t ω n‖) atTop
      (𝓝 (sSup ((fun x:ℝ=>|c+x|) '' realMeasureSupport (scalarBernoulliMeasure t a)))) := by
  rw [scalarBernoulliMeasure_abs_sSup ht0 ht1]
  exact tendsto_const_nhds.congr'
    ((canonical_projection_affine_norm_eventually hk ht0 ht1 ω a c).mono (fun _ h=>h.symm))

/-- The corresponding continuous empirical spectral statistics converge
for every sample, against the same actual scaled Bernoulli law. -/
theorem canonical_projection_trace_tendsto {k : ℕ} (hk : 0<k) {t : ℝ}
    (ht0 : 0≤t) (ht1 : t≤1) (ω : Canonical.Sample k) (a : ℝ)
    (f : ℝ→ℝ) (hf : Continuous f) :
    Tendsto (fun n=>(1/((k:ℝ)*(n+1)))*RevisionMatrixEntropy.spectralTrace f
      (a • Canonical.projection k t ω n)) atTop
      (𝓝 (∫x,f x∂scalarBernoulliMeasure t a)) := by
  rw [integral_scalarBernoulliMeasure ht0 ht1]
  exact canonical_projection_scalar_empirical_tendsto hk ht0 ht1 ω a f hf

/-- The unmodified canonical projections have their Bernoulli spectral law
and all affine norm limits unconditionally, in every fixed output dimension.
This is not joint convergence with the noncommuting block matrix units. -/
theorem canonical_projection_scalar_strong {k : ℕ} (hk : 0<k) {t : ℝ}
    (ht0 : 0<t) (ht1 : t<1) (ω : Canonical.Sample k) (a : ℝ) :
    (∀c:ℝ,Tendsto (fun n=>‖(c:ℂ) •
      (1:Matrix (Canonical.Index k n) (Canonical.Index k n) ℂ)+(a:ℂ) • Canonical.projection k t ω n‖)
      atTop (𝓝 (sSup ((fun x:ℝ=>|c+x|) '' realMeasureSupport (scalarBernoulliMeasure t a))))) ∧
    (∀f:ℝ→ℝ,Continuous f→Tendsto
      (fun n=>(1/((k:ℝ)*(n+1)))*RevisionMatrixEntropy.spectralTrace f
        (a • Canonical.projection k t ω n)) atTop (𝓝 (∫x,f x∂scalarBernoulliMeasure t a))) :=
  ⟨canonical_projection_affine_norm_tendsto hk ht0 ht1 ω a,
    fun f hf=>canonical_projection_trace_tendsto hk ht0.le ht1.le ω a f hf⟩

end ScalarStrong
end ProjectionChannels
