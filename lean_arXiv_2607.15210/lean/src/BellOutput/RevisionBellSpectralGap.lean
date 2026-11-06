import RandomCompression.RevisionFullBlockInput
import OutputStates.RevisionOutputProbability

/-! A common positive spectral interval for fixed positive compressions.
The gap is derived from the already proved compression edge, not assumed
as an additional random-matrix input. -/

open MeasureTheory Filter Set Matrix
open OutputSpaceVerification RevisionOutput
open scoped Topology BigOperators ComplexOrder Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels

lemma negative_positive_coefficients_bodySupport {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hkt : 1 < (k:ℝ)^2*t)
    (a : Fin k → ℝ) (ha : ∀ i, 0<a i) :
    bodySupport k t (fun i => -a i) < 0 := by
  obtain ⟨u,hu,heq⟩ := (bodySupport_isGreatest ht ht1 (fun i => -a i)).1
  have hp := body_mass_pos hk ht hkt u hu
  have hex : ∃ i, 0<u i := by
    by_contra h
    push_neg at h
    have hs := Finset.sum_nonpos (fun i (_ : i∈Finset.univ) => h i)
    linarith
  obtain ⟨i,hui⟩ := hex
  have hsum : 0 < ∑ j, a j*u j := Finset.sum_pos'
    (fun j _ => mul_nonneg (ha j).le (hu.1 j).1) ⟨i,Finset.mem_univ i,mul_pos (ha i) hui⟩
  rw [← heq]
  simpa only [neg_mul, Finset.sum_neg_distrib] using neg_neg_of_pos hsum

lemma eigenvalue_lower_of_largest_neg_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (m : ℝ)
    (hm : largestEigenvalue hM.neg ≤ -m) (i : n) : m ≤ hM.eigenvalues i := by
  have hp := (largest_le_iff_shift_posSemidef hM.neg (-m)).mp hm
  have hq := hp.re_dotProduct_nonneg (⇑(hM.eigenvectorBasis i))
  have hn : dotProduct (star ⇑(hM.eigenvectorBasis i)) ⇑(hM.eigenvectorBasis i) = (1:ℂ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hM.eigenvectorBasis.orthonormal.1 i]
    simp
  simp only [Matrix.sub_mulVec,Matrix.smul_mulVec_assoc,Matrix.one_mulVec,
    Matrix.neg_mulVec,dotProduct_sub,dotProduct_smul,dotProduct_neg,hn,
    smul_eq_mul,mul_one] at hq
  rw [map_sub,map_neg,← hM.eigenvalues_eq i] at hq
  change 0 ≤ -m - -(hM.eigenvalues i) at hq
  linarith

/-- For any fixed positive coefficient vector, the actual finite compression
has a deterministic positive lower spectral bound eventually almost surely. -/
theorem ae_eventually_rotatedCompression_spectral_gap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH)
    (U : Matrix.unitaryGroup (Fin k) ℂ) (a : Fin k → ℝ)
    (ha : ∀ i, 0<a i) :
    ∃ m : ℝ, 0<m ∧ ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ i,
      m ≤ (rotatedCompressionHermitian k P hH U a ω n).eigenvalues i := by
  let Q := fun ω n => localConjugate (P ω n) U
  have hQH := fun ω n => localConjugate_isHermitian (hH ω n) (U : Matrix (Fin k) (Fin k) ℂ)
  have hQI := fun ω n => localConjugate_idempotent (P ω n) (hId ω n) U
  have hconv := random_compression_from_amplified_block_strong μ k hk t ht0 ht1
    Q hQH hQI (hFull.to_amplified U)
  let L := bodySupport k t (fun i => -a i)
  have hL : L<0 := negative_positive_coefficients_bodySupport hk ht0.le ht1.le hkt a ha
  refine ⟨-L/2,by linarith,?_⟩
  filter_upwards [hconv] with ω hω
  have hc := hω (fun i => -a i)
  rw [bernoulliSupport_eq_bodySupport] at hc
  have he : ∀ᶠ n in atTop, largestEigenvalue
      (blockCompression_isHermitian (diagonalBlock (Q ω n))
        (fun i => (projection_diagonalBlock_contraction (Q ω n) (hQH ω n) (hQI ω n) i).1.1)
        (fun i => -a i)) < L/2 := hc.eventually (gt_mem_nhds (by dsimp [L] at *; linarith))
  filter_upwards [he] with n hn
  intro i
  have hneg : blockCompression (diagonalBlock (Q ω n)) (fun i => -a i) =
      -blockCompression (diagonalBlock (Q ω n)) a := by
    simp [blockCompression,Finset.sum_neg_distrib]
  apply eigenvalue_lower_of_largest_neg_le (rotatedCompressionHermitian k P hH U a ω n)
  have hh : largestEigenvalue (rotatedCompressionHermitian k P hH U a ω n).neg < L/2 := by
    simpa only [hneg] using hn
  linarith

/-- A uniform finite upper bound follows from the diagonal blocks being
positive contractions. It holds at every index and sample. -/
theorem rotatedCompression_eigenvalue_upper
    {Ω : Type*} {k : ℕ}
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (U : Matrix.unitaryGroup (Fin k) ℂ) (a : Fin k → ℝ) (ω : Ω) (n : ℕ) (i : Fin (n+1)) :
    (rotatedCompressionHermitian k P hH U a ω n).eigenvalues i ≤ ∑ j, |a j| := by
  let Q := localConjugate (P ω n) U
  have hQH := localConjugate_isHermitian (hH ω n) (U : Matrix (Fin k) (Fin k) ℂ)
  have hQI := localConjugate_idempotent (P ω n) (hId ω n) U
  have hb := fun j => projection_diagonalBlock_contraction Q hQH hQI j
  apply eigenvalue_le_of_shift_posSemidef (rotatedCompressionHermitian k P hH U a ω n)
  simpa only [sub_zero,blockCompression,Complex.ofReal_zero,zero_smul,
    Finset.sum_const_zero] using
    blockCompression_shift (diagonalBlock Q) (fun j => (hb j).1) (fun j => (hb j).2) a (fun _ => 0)

end ProjectionChannels
