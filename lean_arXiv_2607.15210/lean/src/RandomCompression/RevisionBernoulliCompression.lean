import RandomCompression.RevisionBernoulliHolomorphic
import RandomCompression.RevisionBernoulliTensor
import RandomCompression.CompressionExtension
import RandomCompression.ProjectionStrongConvergence
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Random compression from the permitted block-modified strong-convergence input

The external input is a norm-convergence statement for affine polynomial tests,
with an actual compact probability limit law specified by its additive
Bernoulli R-transform. The edge formula is proved, not assumed. All norms in
this file are the Euclidean matrix operator norm.
-/

open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder

noncomputable section
namespace ProjectionChannels

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

local instance compressionMatrixCStarAlgebra : CStarAlgebra (Matrix n n ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance
  norm_mul_self_le := CStarRing.norm_mul_self_le

/-- A positive scalar shift turns the operator norm into the largest eigenvalue. -/
theorem norm_shift_eq_largest {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (c : ℝ) (hpos : ((c : ℂ) • (1 : Matrix n n ℂ) + M).PosSemidef) :
    ‖(c : ℂ) • (1 : Matrix n n ℂ) + M‖ = c + largestEigenvalue hM := by
  have heig (i : n) : 0 ≤ c + hM.eigenvalues i := by
    have hq := hpos.re_dotProduct_nonneg (⇑(hM.eigenvectorBasis i))
    have hn : dotProduct (star ⇑(hM.eigenvectorBasis i)) ⇑(hM.eigenvectorBasis i) = (1 : ℂ) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        inner_self_eq_norm_sq_to_K, hM.eigenvectorBasis.orthonormal.1 i]
      simp
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, hn, smul_eq_mul, mul_one] at hq
    rw [map_add, show RCLike.re (c : ℂ) = c from rfl, ← hM.eigenvalues_eq i] at hq
    exact hq
  have hcf : cfc (fun x : ℝ => c+x) M = (c : ℂ) • (1 : Matrix n n ℂ) + M := by
    change cfc (fun x : ℝ => c+id x) M = _
    rw [cfc_const_add c id M (ha := hM.isSelfAdjoint), cfc_id ℝ M hM.isSelfAdjoint]
    congr 1
    ext i j
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, smul_eq_mul]
  rw [← hcf]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := n)) hM.eigenvalues
  have hil : largestEigenvalue hM = hM.eigenvalues i := hi
  apply le_antisymm
  · apply norm_cfc_le
    · rw [hil]
      exact heig i
    · intro x hx
      obtain ⟨j, rfl⟩ := hM.eigenvalues_eq_spectrum_real ▸ hx
      rw [Real.norm_eq_abs, abs_of_nonneg (heig j)]
      exact add_le_add_left (eigenvalue_le_largest hM j) c
  · have h := norm_apply_le_norm_cfc (fun x : ℝ => c+x) M
      (hM.eigenvalues_mem_spectrum_real i) (ha := hM.isSelfAdjoint)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (heig i), hil] using h

/-- Every sufficiently large scalar shift of a compression is positive. -/
theorem blockCompression_positive_shift {ι : Type*} [Fintype ι]
    (P : ι → Matrix n n ℂ) (hP : ∀ i, (P i).PosSemidef)
    (hIP : ∀ i, (1-P i).PosSemidef) (a : ι → ℝ) (c : ℝ)
    (hc : (∑ i, |a i|) ≤ c) :
    ((c : ℂ) • (1 : Matrix n n ℂ) + blockCompression P a).PosSemidef := by
  have hz : blockCompression P (fun _ => 0) = 0 := by simp [blockCompression]
  have hp : (((∑ i, |a i| : ℝ) : ℂ) • (1 : Matrix n n ℂ) + blockCompression P a).PosSemidef := by
    simpa only [hz, zero_sub, abs_neg, sub_neg_eq_add] using
      blockCompression_shift P hP hIP (fun _ => 0) a
  have he := posSemidef_real_smul (Matrix.PosSemidef.one :
      (1 : Matrix n n ℂ).PosSemidef) (c-∑ i, |a i|) (sub_nonneg.mpr hc)
  convert he.add hp using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub]
  ring

/-- Almost-sure bounds also bound every point of the topological support. -/
theorem realMeasureSupport_abs_le {μ : Measure ℝ} {M : ℝ}
    (hM : ∀ᵐ x ∂μ, |x| ≤ M) {x : ℝ} (hx : x ∈ realMeasureSupport μ) : |x| ≤ M := by
  by_contra hh
  have hzero : μ {y : ℝ | M < |y|} = 0 := by
    simpa only [ae_iff, not_le] using hM
  exact hx {y : ℝ | M < |y|} (isOpen_lt continuous_const continuous_abs)
    (lt_of_not_ge hh) hzero

theorem realMeasureSupport_le {μ : Measure ℝ} {r : ℝ}
    (hr : ∀ᵐ x ∂μ, x ≤ r) {x : ℝ} (hx : x ∈ realMeasureSupport μ) : x ≤ r := by
  by_contra hh
  have hzero : μ (Ioi r) = 0 := by simpa only [ae_iff, not_le, Ioi] using hr
  exact hx (Ioi r) isOpen_Ioi (lt_of_not_ge hh) hzero

/-- The norm of an affine test of a compact law reduces to its right edge
once the shift makes the whole support positive. -/
theorem support_shift_norm {μ : Measure ℝ} {M c r : ℝ}
    (hM : ∀ᵐ x ∂μ, |x| ≤ M) (hc : M ≤ c)
    (hr : r ∈ realMeasureSupport μ) (hu : ∀ᵐ x ∂μ, x ≤ r) :
    sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport μ) = c+r := by
  have hnonneg (x : ℝ) (hx : x ∈ realMeasureSupport μ) : 0 ≤ c+x := by
    have h := realMeasureSupport_abs_le hM hx
    have hneg := neg_abs_le x
    linarith
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨r, hr, abs_of_nonneg (hnonneg r hr)⟩
  · rintro y ⟨x, hx, rfl⟩
    change |c+x| ≤ c+r
    rw [abs_of_nonneg (hnonneg x hx)]
    exact add_le_add_left (realMeasureSupport_le hu hx) c

/-- The scalar identity output factor in the block-modification theorem
can be removed without changing any affine-test operator norm. -/
theorem norm_shift_amplified_diagonalTrace
    {ν κ : Type} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Matrix (ν × κ) (ν × κ) ℂ) (a : κ → ℝ) (c : ℝ) :
    ‖(c : ℂ) • (1 : Matrix (ν × κ) (ν × κ) ℂ) +
        ProjectionChannelsCP.amplify (diagonalTraceLinearMap a) P‖ =
      ‖(c : ℂ) • (1 : Matrix ν ν ℂ) + blockCompression (diagonalBlock P) a‖ := by
  rw [amplified_diagonalTrace]
  have heq : Matrix.kronecker ((c : ℂ) • (1 : Matrix ν ν ℂ) +
      blockCompression (diagonalBlock P) a) (1 : Matrix κ κ ℂ) =
      (c : ℂ) • (1 : Matrix (ν × κ) (ν × κ) ℂ) +
        Matrix.kronecker (blockCompression (diagonalBlock P) a) (1 : Matrix κ κ ℂ) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hij : i=j <;> by_cases hab : a=b <;>
      simp [Matrix.kronecker_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, hij, hab, Prod.mk.injEq]
  rw [← heq, norm_kronecker_identity]

/-- The precise permitted external input, restricted to the affine polynomial
norm tests needed here. Full block-modified strong convergence supplies this
statement. It supplies an actual compact probability law with the conventional
additive R-transform germ; it does not supply any spectral-edge formula.

The Euclidean operator norm is used explicitly. The input is a proposition
parameter, not an axiom or a theorem claimed to have been formalized. -/
def BlockModifiedStrongInput {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (t : ℝ)
    (P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ) : Prop :=
  ∀ a : Fin k → ℝ, ∃ ν : Measure ℝ,
    IsBernoulliFreeSumLaw k t a ν ∧
    ∀ c : ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun m => ‖(c : ℂ) • (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) +
        blockCompression (diagonalBlock (P ω m)) a‖)
        atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν)))

/-- Fixed-parameter compression convergence follows from the permitted norm
input; the conversion from norm convergence to the largest eigenvalue and the
Bernoulli spectral edge are both proved. -/
theorem fixed_random_compression_from_block_strong
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (k : ℕ) (hk : 0 < k) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ)
    (hH : ∀ ω m, (P ω m).IsHermitian)
    (hId : ∀ ω m, P ω m * P ω m = P ω m)
    (hBM : BlockModifiedStrongInput μ k t P) (a : Fin k → ℝ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun m => largestEigenvalue
        (blockCompression_isHermitian (diagonalBlock (P ω m))
          (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1.1) a))
        atTop (𝓝 (bernoulliSupport t (k : ℝ) a)) := by
  obtain ⟨ν, hν, hnorm⟩ := hBM a
  obtain ⟨M, hM⟩ := hν.compactlySupported
  let c := max M (∑ i, |a i|)
  have hnormlimit := hnorm c
  have hlim : sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν) =
      c + bernoulliSupport t (k : ℝ) a := by
    rw [support_shift_norm hM (le_max_left _ _) hν.right_edge.1 hν.right_edge.2]
    rw [bernoulli_free_sum_right_edge hk ht0 ht1 a ν hν]
    rfl
  rw [hlim] at hnormlimit
  filter_upwards [hnormlimit] with ω hω
  have heq (m : ℕ) :
      ‖(c : ℂ) • (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) +
          blockCompression (diagonalBlock (P ω m)) a‖ =
        c + largestEigenvalue (blockCompression_isHermitian (diagonalBlock (P ω m))
          (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1.1) a) := by
    apply norm_shift_eq_largest
    apply blockCompression_positive_shift _
      (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1)
      (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).2)
    exact le_max_right _ _
  have hh := hω.sub_const c
  simpa only [heq, add_sub_cancel_left] using hh

/-- **Lemma II.3.** On one event of probability one, the random-compression
formula holds simultaneously for every real coefficient vector. The only
external hypothesis is `BlockModifiedStrongInput`. -/
theorem random_compression_from_block_strong
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (k : ℕ) (hk : 0 < k) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ)
    (hH : ∀ ω m, (P ω m).IsHermitian)
    (hId : ∀ ω m, P ω m * P ω m = P ω m)
    (hBM : BlockModifiedStrongInput μ k t P) :
    ∀ᵐ ω ∂μ, ∀ a : Fin k → ℝ,
      Tendsto (fun m => largestEigenvalue
        (blockCompression_isHermitian (diagonalBlock (P ω m))
          (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1.1) a))
        atTop (𝓝 (bernoulliSupport t (k : ℝ) a)) := by
  exact ae_all_projection_compressions μ k hk t ht0 ht1 P hH hId
    (fixed_random_compression_from_block_strong μ k hk t ht0 ht1 P hH hId hBM)

/-- The external strong-convergence input stated for the exact amplified map
in the paper, before removing its identity output factor. This is just the
affine-polynomial norm portion of block-modified strong convergence. -/
def AmplifiedBlockModifiedStrongInput {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (t : ℝ)
    (P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ) : Prop :=
  ∀ a : Fin k → ℝ, ∃ ν : Measure ℝ,
    IsBernoulliFreeSumLaw k t a ν ∧
    ∀ c : ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun m => ‖(c : ℂ) •
        (1 : Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ) +
        ProjectionChannelsCP.amplify (diagonalTraceLinearMap a) (P ω m)‖)
        atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν)))

theorem AmplifiedBlockModifiedStrongInput.to_block
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ} {t : ℝ}
    {P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ}
    (hk : 0 < k) (h : AmplifiedBlockModifiedStrongInput μ k t P) :
    BlockModifiedStrongInput μ k t P := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  intro a
  obtain ⟨ν, hν, hconv⟩ := h a
  refine ⟨ν, hν, ?_⟩
  intro c
  filter_upwards [hconv c] with ω hω
  simpa only [norm_shift_amplified_diagonalTrace] using hω

/-- **Lemma II.3 with exactly the map in the permitted black box.**
The strong block theorem is the sole external input. The variational edge,
operator-norm/eigenvalue conversion, identity tensor factor, and simultaneous
probability-one event have all been proved. -/
theorem random_compression_from_amplified_block_strong
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (k : ℕ) (hk : 0 < k) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ)
    (hH : ∀ ω m, (P ω m).IsHermitian)
    (hId : ∀ ω m, P ω m * P ω m = P ω m)
    (hBM : AmplifiedBlockModifiedStrongInput μ k t P) :
    ∀ᵐ ω ∂μ, ∀ a : Fin k → ℝ,
      Tendsto (fun m => largestEigenvalue
        (blockCompression_isHermitian (diagonalBlock (P ω m))
          (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1.1) a))
        atTop (𝓝 (bernoulliSupport t (k : ℝ) a)) := by
  exact random_compression_from_block_strong μ k hk t ht0 ht1 P hH hId (hBM.to_block hk)

end ProjectionChannels


