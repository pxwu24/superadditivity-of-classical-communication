import BellOutput.RevisionBellEntropyTransport
import Entropy.RevisionMatrixEntropyWitness
import Entropy.RevisionMatrixEntropyBell
import Entropy.BellOne
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Corollary IV.2 for actual channel minima and actual isotropic matrices. -/

open MeasureTheory Filter Set Matrix PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped Topology BigOperators ComplexOrder
namespace RevisionMatrixEntropy
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma isotropic_entropy_eq_bell_spectrum {k : ℕ} [NeZero k]
    (t p : ℝ) (hp : 0<p) :
    matrixRenyiEntropy p (RevisionBell.isotropic (Fin k) (BellLimitVerification.mixing k t))=
      AppendixB.renyi p (Finset.univ : Finset (Fin 2)) ![1,(k:ℝ)^2-1]
        ![AppendixB.alphaB k t,AppendixB.betaB k t] := by
  rw [matrixRenyiEntropy_isotropic p hp]
  simp [AppendixB.renyi,Fin.sum_univ_two,AppendixB.alphaB,AppendixB.betaB,
    AppendixB.rkt,BellLimitVerification.mixing,BellLimitVerification.denominator]

/-- The genuine product-channel minimum is bounded in limsup by the
entropy of the explicit Bell spectrum. Eventual lower boundedness is proved
from compactness of the full density-matrix entropy image. -/
theorem corollary_IV_2_fixed_k
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N*P ω N=P ω N)
    (hStrong : FullBlockModifiedStrongInput μ k t P hH)
    (p : ℝ) (hp : 0<p) :
    let Φ := fun ω N => normalizedOutput (P ω N)
      (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N)))
    ∀ᵐ ω ∂μ, Filter.limsup
      (fun N => minimumOutputEntropy p (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N)))) atTop ≤
        AppendixB.renyi p (Finset.univ : Finset (Fin 2)) ![1,(k:ℝ)^2-1]
          ![AppendixB.alphaB k t,AppendixB.betaB k t] := by
  let hP := fun ω N => HaarProjection.projection_posSemidef (P ω N) (hH ω N) (hId ω N)
  let D := fun ω N => marginalNormalizer (P ω N) (hP ω N)
  let Φ := fun ω N => normalizedOutput (P ω N) (D ω N)
  have hb := actual_bell_output_entropy_limit μ hk ht ht1 hkt P hH hId hStrong p hp
  have hbase : AmplifiedBlockModifiedStrongInput μ k t P := by
    simpa only [Matrix.UnitaryGroup.one_val,localConjugate_one] using hStrong.to_amplified 1
  have hn := ae_eventually_marginal_posDef μ hk ht ht1 hkt P hH hId hbase
  obtain ⟨c,hc⟩ := (isCompact_densityMatrices (A:=Fin k×Fin k)).image_of_continuousOn
    (matrixRenyiEntropy_continuousOn p hp) |>.bddBelow
  filter_upwards [hb,hn] with ω hbω hnω
  have hprops : ∀ᶠ N in atTop,
      c ≤ minimumOutputEntropy p (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N))) ∧
      minimumOutputEntropy p (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N))) ≤
        matrixRenyiEntropy p (RevisionBell.tensorMap (Φ ω N) (conjugateMap (Φ ω N))
          (RevisionBell.bellState (Fin (N+1)))) := by
    filter_upwards [hnω] with N hN
    have hD : (D ω N).IsHermitian :=
      (HaarProjection.traceB_posSemidef (P ω N) (hP ω N)).posSemidef_sqrt.isHermitian.inv
    have hnorm : D ω N*traceB (P ω N)*D ω N=1 := inverse_sqrt_normalizes hN
    constructor
    · apply le_csInf
      · exact ((densityMatrices_nonempty (A:=Fin (N+1)×Fin (N+1))).image _).image _
      · rintro _ ⟨Y,⟨ρ,hρ,rfl⟩,rfl⟩
        apply hc
        refine ⟨_,?_,rfl⟩
        have heq : Φ ω N=channel (RevisionBell.normalizedChoi (P ω N) (D ω N)) :=
          funext fun σ => (RevisionBell.channel_normalizedChoi (P ω N) (D ω N) σ).symm
        rw [heq]
        exact RevisionBell.tensor_choi_conjugate_mem_densityMatrices
          (RevisionBell.normalizedChoi_posSemidef (hP ω N) (D ω N) hD hnorm)
          (normalized_choi (D ω N) (P ω N) hD (hP ω N) hnorm).2 hρ
    · exact normalizedOutput_minimum_bell_le p hp (hP ω N) (D ω N) hD hnorm
  have hco := Filter.IsCoboundedUnder.of_frequently_ge (hprops.mono fun _ h=>h.1).frequently
  have hle := Filter.limsup_le_limsup (hprops.mono fun _ h=>h.2) hco hbω.isBoundedUnder_le
  rw [hbω.limsup_eq,isotropic_entropy_eq_bell_spectrum t p hp] at hle
  exact hle

/-- The Bell entropy expansion, now evaluated on the actual limiting
isotropic matrix, with the stronger O(k^-4) error. -/
theorem corollary_IV_2_asymptotics {t p : ℝ} (ht : 0<t) (ht1 : t<1) (hp : 0<p) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀≤(k:ℝ) →
      |matrixRenyiEntropy p (RevisionBell.isotropic (Fin k) (BellLimitVerification.mixing k t))-
        (2*Real.log k-AppendixB.Ap p t/k^2)| ≤ C/k^4 := by
  obtain ⟨C,k₀,hC⟩ := AppendixB.bell_output_r1 ht ht1 hp
  refine ⟨C,max k₀ 1,?_⟩
  intro k hk
  have hkpos : 0<k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one ((le_max_right k₀ 1).trans hk))
  letI : NeZero k := ⟨Nat.ne_of_gt hkpos⟩
  rw [isotropic_entropy_eq_bell_spectrum t p hp]
  exact hC k ((le_max_left k₀ 1).trans hk)

#print axioms corollary_IV_2_fixed_k
#print axioms corollary_IV_2_asymptotics
end
end RevisionMatrixEntropy
