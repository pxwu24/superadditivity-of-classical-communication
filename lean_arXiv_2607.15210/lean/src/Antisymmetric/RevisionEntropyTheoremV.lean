import Antisymmetric.RevisionPostprocessedBellLimit
import Antisymmetric.RevisionAntisymmetricEntropy
import Entropy.BellGeneral
import Antisymmetric.RevisionAntisymmetricBellEntropy

/-! Theorem V.1 for the actual normalized projection-induced channels after
antisymmetric postprocessing. The particle count is `r+1`, avoiding a separate
zero-particle case. Fixed-k limits require only `r+1≤k` and `k²t>1`. -/
open MeasureTheory Filter Set Matrix
open PreliminariesMatrix ProjectionChannels ProjectionChannelsCP RevisionOutput RevisionBell
open AntisymmetricVerification RevisionMatrixEntropy
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
noncomputable section
namespace RevisionMain

/-- The actual postprocessed channel, in a fixed orthonormal Slater basis. -/
def antisymmetricNormalizedChannel {A : Type} [Fintype A] [DecidableEq A]
    {k : ℕ} (r : ℕ) (P : Matrix (A×Fin k) (A×Fin k) ℂ) (hP : P.PosSemidef) :
    Matrix A A ℂ →ₗ[ℂ] Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ :=
  (antisymmetricChannel (k:=k) (r:=r)).comp (normalizedChannel P (marginalNormalizer P hP))

/-- The limiting Bell output after actual antisymmetric postprocessing. -/
def antisymmetricBellLimit (k r : ℕ) (t : ℝ) :
    Matrix (SubsetIndex k (r+1)×SubsetIndex k (r+1))
      (SubsetIndex k (r+1)×SubsetIndex k (r+1)) ℂ :=
  tensorMap (antisymmetricChannel (k:=k) (r:=r))
    (conjugateMap (antisymmetricChannel (k:=k) (r:=r)))
    (isotropic (Fin k) (BellLimitVerification.mixing k t))

/-- The two genuine fixed-k entropy limits in Theorem V.1. No restriction
`k≥2(r+1)` is needed for existence of these limits. -/
theorem theorem_V_1_fixed_k
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t) (r : ℕ) (hrk : r+1≤k)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH) (p : ℝ) (hp : 0<p) :
    let Θ := fun ω n => antisymmetricNormalizedChannel r (P ω n)
      (HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => minimumOutputEntropy p (Θ ω n)) atTop
        (nhds (AppendixB.infimumOutputEntropy p t k (r+1))) ∧
      Tendsto (fun n => matrixRenyiEntropy p
        (tensorMap (Θ ω n) (conjugateMap (Θ ω n)) (bellState (Fin (n+1)))))
        atTop (nhds (matrixRenyiEntropy p (antisymmetricBellLimit k r t))) := by
  letI := nonempty_subsetIndex hrk
  have hE := antisymmetricChannel_quantumChannel hrk
  have hsingle := postprocessed_minimum_output_entropy_limit μ hk ht0 ht1 hkt P hH hId hFull
    (antisymmetricChannel (k:=k) (r:=r)) hE p hp
  rw [antisymmetric_body_infimum hrk t p hp] at hsingle
  have hbell := postprocessed_bell_output_entropy_limit μ hk ht0 ht1 hkt P hH hId hFull
    (antisymmetricChannel (k:=k) (r:=r)) hE p hp
  exact hsingle.and hbell

/-- Proposition B.1 for the genuine matrix-body minimum, with its proved
uniform O(k^(-5/2)) error. -/
theorem theorem_V_1_single_asymptotics
    {t p : ℝ} (ht0 : 0<t) (ht1 : t<1) (hp : 0<p) (r : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∃ k₀ : ℝ, ∀ k : ℕ, k₀≤(k:ℝ) → r+1≤k ∧
      |sInf ((fun M => matrixRenyiEntropy p (antisymmetricChannel (k:=k) (r:=r) M)) ''
          spectralBody k t) -
        (Real.log (Nat.choose k (r+1))-2*p*(1-t)/(t*(r+1)*(k:ℝ)^2))|
        ≤ C/((k:ℝ)^2*Real.sqrt k) := by
  obtain ⟨C,hC,k₀,h⟩ := AppendixB.single_output_infimum ht0 ht1 hp (r+1) (by omega)
  refine ⟨C,hC,max k₀ (r+1),?_⟩
  intro k hk
  have hkr : r+1≤k := by exact_mod_cast (le_max_right k₀ ((r:ℝ)+1)).trans hk
  refine ⟨hkr,?_⟩
  rw [antisymmetric_body_infimum hkr t p hp]
  simpa only [Nat.cast_add,Nat.cast_one] using h k ((le_max_left _ _).trans hk)

/-- Exact Bell entropy spectrum, used only in the stable range k≥2(r+1). -/
theorem antisymmetricBellLimit_entropy {k r : ℕ} (hkr : 2*(r+1)≤k)
    (p : ℝ) (hp : 0<p) (t : ℝ) :
    matrixRenyiEntropy p (antisymmetricBellLimit k r t)=
      AppendixB.renyi p (Finset.range (r+2)) (AppendixB.dm k) (AppendixB.bellNu k (r+1) t) :=
  antisymmetricChannel_bell_entropy hkr p hp t

/-- Proposition B.2 and the joint asymptotic in Theorem V.1 for the actual
postprocessed Bell-limit matrix, with O(k^-3) error. -/
theorem theorem_V_1_bell_asymptotics
    {t p : ℝ} (ht0 : 0<t) (ht1 : t<1) (hp : 0<p) (r : ℕ) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀≤(k:ℝ) →
      |matrixRenyiEntropy p (antisymmetricBellLimit k r t)-
        (2*Real.log (Nat.choose k (r+1))-AppendixB.Bpr p (r+1) ((1-t)/t)/(k:ℝ)^2)|
        ≤ C/(k:ℝ)^3 :=
  antisymmetricChannel_bell_entropy_asymptotics ht0 ht1 hp r

end RevisionMain
