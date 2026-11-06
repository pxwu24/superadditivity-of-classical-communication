import StrongConvergence.StrongConvergenceHaarSequenceTransfer
import StrongConvergence.StrongConvergenceVariableStrong

/-! Full block-modified strong convergence for arbitrary Haar-projection
sequences on an arbitrary probability space. Only the coordinate Haar laws
are used; no independence between dimensions is assumed. -/
open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels.HaarSequence
open Canonical TensorHaar StrongConvergenceMoments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {k : ℕ} {d : ℕ → ℕ}
variable {P₀ : (n : ℕ) → Matrix (Index k n) (Index k n) ℂ}
variable {P : Ω → (n : ℕ) → Matrix (Index k n) (Index k n) ℂ}

/-- Hermitian witness for the actual compression of an abstract Haar sequence. -/
def compressionHermitian (h : HaarSequence μ k d P₀ P) (a : Fin k → ℝ) (ω : Ω) (n : ℕ) :
    (blockCompression (diagonalBlock (P ω n)) a).IsHermitian :=
  blockCompression_isHermitian _ (fun i => (h.isHermitian ω n).submatrix (fun e => (e,i))) a

/-- Affine compression norms transfer from the canonical ensemble because
all centered deviation probabilities are summable and the marginals agree. -/
theorem ae_norm_shift_tendsto_of_genus_moments (h : HaarSequence μ k d P₀ P)
    {t : ℝ} (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (hdt : Tendsto (density k d) atTop (𝓝 t))
    (a : Fin k → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (-(∑i, |a i|)) (∑i, |a i|))
    (hmom : ∀j : ℕ, (∫x, x^j ∂ν) = (normalizedMomentCoefficient k j a 0).eval t)
    (c : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => ‖(c:ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
        blockCompression (diagonalBlock (P ω n)) a‖)
      atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν))) := by
  obtain ⟨center,htail⟩ := exists_variable_shiftedCompressionNorm_center_summable
    hk ht0 ht1 (density k d) hdt a c
  apply h.ae_tendsto_of_canonical_centered_tails hk
    (fun n Q => ‖(c:ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
      blockCompression (diagonalBlock Q) a‖)
    (fun _ => (continuous_const.add (continuous_projection_compression a)).norm.measurable)
    center _
  · exact (ae_variable_norm_shift_tendsto_of_genus_moments hk ht0 ht1
      (density_nonneg k d) (h.density_le_one hk) hdt a ν hν hmom).mono fun _ hω => hω c
  · intro m
    exact htail (1/((m:ℝ)+1)) (by positivity)

/-- Every normalized trace moment has the same almost-sure limit for arbitrary
Haar marginals, independently of how the dimensions are coupled. -/
theorem ae_normalizedTrace_tendsto_of_genus_moments (h : HaarSequence μ k d P₀ P)
    {t : ℝ} (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (hdt : Tendsto (density k d) atTop (𝓝 t))
    (a : Fin k → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmom : ∀j : ℕ, (∫x, x^j ∂ν) = (normalizedMomentCoefficient k j a 0).eval t)
    (j : ℕ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (1/((n+1:ℕ):ℝ)) *
      (Matrix.trace ((blockCompression (diagonalBlock (P ω n)) a)^j)).re)
      atTop (𝓝 (∫x, x^j ∂ν)) := by
  cases j with
  | zero =>
    have heq (ω : Ω) (n : ℕ) : (1/((n+1:ℕ):ℝ)) *
        (Matrix.trace ((blockCompression (diagonalBlock (P ω n)) a)^0)).re = 1 := by
      have hn : (n:ℝ)+1 ≠ 0 := by positivity
      simp [hn]
    exact Eventually.of_forall fun ω => by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)) using 1
      · funext n
        exact heq ω n
      · simp
  | succ m =>
    obtain ⟨center,htail⟩ := exists_variable_compressionMoment_center_summable
      hk ht0 ht1 (density k d) hdt a m
    have hsource : ∀ᵐ ω ∂probability k, Tendsto
        (fun n => (Matrix.trace ((blockCompression (diagonalBlock
          (projection k (density k d n) ω n)) a)^(m+1))).re / ((n:ℝ)+1))
        atTop (𝓝 (∫x, x^(m+1) ∂ν)) := by
      rw [hmom, normalizedMomentCoefficient]
      simp only [Nat.succ_ne_zero, if_false]
      exact (ae_variable_compressionMoment_tendsto_genus hk ht0 ht1
        (density_nonneg k d) (h.density_le_one hk) hdt a).mono fun _ hω => hω m
    have ht := h.ae_tendsto_of_canonical_centered_tails hk
      (fun n Q => (Matrix.trace ((blockCompression (diagonalBlock Q) a)^(m+1))).re / ((n:ℝ)+1))
      (fun _ => ((Complex.continuous_re.comp
        ((continuous_projection_compression a).pow (m+1)).matrix_trace).div_const _).measurable)
      center _ hsource (fun r => htail (1/((r:ℝ)+1)) (by positivity))
    simpa only [Nat.cast_add, Nat.cast_one, one_div, div_eq_mul_inv, mul_comm, one_mul] using ht

/-- The same probability law controls all continuous spectral tests of the
abstract Haar sequence on a single full-measure event. -/
theorem ae_spectral_tests_tendsto_of_genus_moments (h : HaarSequence μ k d P₀ P)
    {t : ℝ} (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (hdt : Tendsto (density k d) atTop (𝓝 t))
    (a : Fin k → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Icc (-(∑i, |a i|)) (∑i, |a i|))
    (hmom : ∀j : ℕ, (∫x, x^j ∂ν) = (normalizedMomentCoefficient k j a 0).eval t) :
    ∀ᵐ ω ∂μ, ∀f : ℝ → ℝ, ContinuousOn f (Icc (-(∑i, |a i|)) (∑i, |a i|)) →
      Tendsto (fun n => (1/((n+1:ℕ):ℝ)) * ∑i, f ((h.compressionHermitian a ω n).eigenvalues i))
        atTop (𝓝 (∫x, f x ∂ν)) := by
  apply ae_matrix_spectral_tests_of_ae_trace_moments μ
    (fun n => n+1) (fun n => Nat.succ_pos n)
    (fun ω n => blockCompression (diagonalBlock (P ω n)) a)
    (h.compressionHermitian a) ν
  · exact Eventually.of_forall fun ω n => StrongConvergence.projection_compression_norm_le
      (P ω n) (h.isHermitian ω n) (h.idempotent ω n) a
  · exact hν
  · exact h.ae_normalizedTrace_tendsto_of_genus_moments hk ht0 ht1 hdt a ν hmom

/-- Full block-modified strong convergence for every Haar-projection sequence
with convergent rank density, on any probability space. Both norm and weak
spectral convergence use the same actual Bernoulli free-sum law, and every
fixed output-basis rotation is included. -/
theorem fullBlockModifiedStrongInput (h : HaarSequence μ k d P₀ P)
    {t : ℝ} (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (hdt : Tendsto (density k d) atTop (𝓝 t)) :
    FullBlockModifiedStrongInput μ k t P h.isHermitian := by
  letI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  intro U a
  obtain ⟨ν,hprob,hν,hmom,-⟩ := exists_canonical_spectral_limit hk ht0.le ht1 a
  letI := hprob
  have hlaw := isBernoulliFreeSumLaw_of_genus_moments ν hk ht0.le ht1.le
    (Finset.sum_nonneg (fun i _ => abs_nonneg (a i)))
    (hν.mono fun _ hx => abs_le.mpr hx) hmom
  have hU := h.localConjugate U
  refine ⟨ν,hlaw,?_,?_⟩
  · intro c
    filter_upwards [hU.ae_norm_shift_tendsto_of_genus_moments hk ht0 ht1 hdt a ν hν hmom c]
      with ω hω
    simpa only [norm_shift_amplified_diagonalTrace] using hω
  · intro f hf _
    exact (hU.ae_spectral_tests_tendsto_of_genus_moments hk ht0 ht1 hdt a ν hν hmom).mono
      fun _ hω => hω f hf.continuousOn

#print axioms fullBlockModifiedStrongInput
end ProjectionChannels.HaarSequence
