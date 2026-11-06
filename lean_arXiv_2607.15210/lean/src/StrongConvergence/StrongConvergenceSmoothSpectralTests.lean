import StrongConvergence.StrongConvergenceSmoothChebyshev
import StrongConvergence.StrongConvergenceSmoothSeriesBound
import StrongConvergence.StrongConvergenceMomentMatrices
import StrongConvergence.StrongConvergenceCompressionBounds
import StrongConvergence.StrongConvergenceRotationTransfer
import StrongConvergence.StrongConvergenceTensorCanonical
import StrongConvergence.StrongConvergenceGenusExpansion
import StrongConvergence.StrongConvergencePositiveQuadratic
import Mathlib.Analysis.NormedSpace.FunctionSeries

/-! Smooth spectral tests of the actual canonical block compressions. -/
open MeasureTheory Filter Set Matrix Polynomial
open scoped Topology BigOperators Matrix.L2OpNorm ContDiff
noncomputable section
namespace ProjectionChannels.Canonical
open StrongConvergenceMoments

def spectralTest (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    (f : ℝ → ℝ) (sample : Sample k) : ℝ :=
  ∫ x, f x ∂empiricalSpectralMeasure
    (blockCompression (diagonalBlock (projection k t sample n)) a) (compressionHermitian k t a sample n)

lemma spectralTest_eq_sum (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    (f : ℝ → ℝ) (sample : Sample k) :
    spectralTest k t a n f sample = (1/((n+1:ℕ):ℝ))*
      ∑ i, f ((compressionHermitian k t a sample n).eigenvalues i) := by
  simp only [spectralTest, empiricalSpectralMeasure, integral_empiricalMeasure, Fintype.card_fin]

lemma spectralMeasure_ae_mem (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ) (sample : Sample k)
    {K : ℝ} (hK : (∑ i, |a i|) ≤ K) :
    ∀ᵐ x ∂empiricalSpectralMeasure
      (blockCompression (diagonalBlock (projection k t sample n)) a) (compressionHermitian k t a sample n),
      x ∈ Icc (-K) K := by
  apply empiricalSpectralMeasure_ae_mem_of_norm_le
  exact (StrongConvergence.projection_compression_norm_le _
    (projection_isHermitian k t sample n) (projection_idempotent k t sample n) a).trans hK

lemma spectralTest_abs_le (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    {f : ℝ → ℝ} {K H : ℝ} (hK : (∑ i, |a i|) ≤ K)
    (hf : ∀ x ∈ Icc (-K) K, |f x| ≤ H) (sample : Sample k) :
    |spectralTest k t a n f sample| ≤ H := by
  have hb := (spectralMeasure_ae_mem k t a n sample hK).mono fun x hx => hf x hx
  have hb' : ∀ᵐ x ∂empiricalSpectralMeasure
      (blockCompression (diagonalBlock (projection k t sample n)) a) (compressionHermitian k t a sample n),
      ‖f x‖ ≤ H := by simpa only [Real.norm_eq_abs] using hb
  simpa only [spectralTest, Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const hb'

lemma spectralTest_power (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n j : ℕ) (sample : Sample k) :
    spectralTest k t a n (fun x => x^j) sample =
      (1/((n+1:ℕ):ℝ))*(Matrix.trace
        ((blockCompression (diagonalBlock (projection k t sample n)) a)^j)).re := by
  simpa only [spectralTest, Fintype.card_fin] using empiricalSpectralMeasure_moment
    (blockCompression (diagonalBlock (projection k t sample n)) a) (compressionHermitian k t a sample n) j

lemma continuous_spectralTest_power (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n j : ℕ) :
    Continuous (spectralTest k t a n (fun x => x^j)) := by
  simp_rw [funext (spectralTest_power k t a n j)]
  cases j with
  | zero => simp; fun_prop
  | succ j =>
    exact continuous_const.mul (Complex.continuous_re.comp
      ((TensorHaar.continuous_compression_trace_power (baseProjection k t n) a j).comp
        (continuous_apply n)))

lemma spectralTest_polynomial (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    (p : ℝ[X]) (sample : Sample k) :
    spectralTest k t a n p.eval sample =
      ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j * spectralTest k t a n (fun x => x^j) sample := by
  exact integral_polynomial_eq_moments (spectralMeasure_ae_mem k t a n sample le_rfl) p

lemma continuous_spectralTest_polynomial (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    (p : ℝ[X]) : Continuous (spectralTest k t a n p.eval) := by
  simp_rw [funext (spectralTest_polynomial k t a n p)]
  exact continuous_finset_sum _ (fun j _ => continuous_const.mul
    (continuous_spectralTest_power k t a n j))

def scaledChebyshev (K : ℝ) (j : ℤ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ j).comp (C K⁻¹ * X)

@[simp] lemma scaledChebyshev_eval (K x : ℝ) (j : ℤ) :
    (scaledChebyshev K j).eval x = (Polynomial.Chebyshev.T ℝ j).eval (x/K) := by
  simp only [scaledChebyshev, eval_comp, eval_mul, eval_C, eval_X]
  congr 1
  ring

lemma scaledChebyshev_abs_le {K x : ℝ} (hK : 0 < K) (hx : x ∈ Icc (-K) K) (j : ℤ) :
    |(scaledChebyshev K j).eval x| ≤ 1 := by
  rw [scaledChebyshev_eval]
  apply PolyChebyshev.abs_eval_T_le_one
  exact ⟨(le_div_iff₀ hK).mpr (by linarith [hx.1]),
    (div_le_iff₀ hK).mpr (by linarith [hx.2])⟩

lemma spectralTest_chebyshev_hasSum (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    {K : ℝ} (hK : 0 < K) (hKa : (∑ i, |a i|) ≤ K)
    (c : ℤ → ℝ) (χ : ℝ → ℝ) (hc : Summable (fun j => |c j|))
    (hexp : ∀ x ∈ Icc (-K) K, HasSum
      (fun j => c j*(scaledChebyshev K j).eval x) (χ x)) (sample : Sample k) :
    HasSum (fun j => c j*spectralTest k t a n (scaledChebyshev K j).eval sample)
      (spectralTest k t a n χ sample) := by
  apply StrongConvergence.hasSum_integrals_of_bounded_expansion
  · exact hc
  · intro j
    exact (scaledChebyshev K j).continuous.aestronglyMeasurable
  · intro j
    exact (spectralMeasure_ae_mem k t a n sample hKa).mono fun x hx => scaledChebyshev_abs_le hK hx j
  · exact (spectralMeasure_ae_mem k t a n sample hKa).mono fun x hx => hexp x hx

lemma continuous_spectralTest_smooth (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (spectralTest k t a n χ) := by
  let K : ℝ := (∑ i, |a i|)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKa : (∑ i, |a i|) ≤ K := by dsimp [K]; linarith
  obtain ⟨c,hc,hexp⟩ := StrongConvergence.exists_smooth_chebyshev_expansion hχ hK
  have hc0 : Summable (fun j => |c j|) := by simpa using hc 0
  have he := spectralTest_chebyshev_hasSum k t a n hK hKa c χ hc0
    (fun x hx => by simpa only [scaledChebyshev_eval] using hexp x hx)
  have hfn : spectralTest k t a n χ =
      fun sample => ∑' j, c j*spectralTest k t a n (scaledChebyshev K j).eval sample :=
    funext fun sample => (he sample).tsum_eq.symm
  rw [hfn]
  apply continuous_tsum
    (fun j => continuous_const.mul (continuous_spectralTest_polynomial k t a n _)) hc0
  intro j sample
  rw [Real.norm_eq_abs, abs_mul]
  have hb := spectralTest_abs_le k t a n hKa (fun x hx => scaledChebyshev_abs_le hK hx j) sample
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (abs_nonneg (c j))


lemma integrable_spectralTest_smooth (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Integrable (spectralTest k t a n χ) (probability k) :=
  (continuous_spectralTest_smooth k t a n hχ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integral_spectralTest_power_succ (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n m : ℕ) :
    (∫ sample, spectralTest k t a n (fun x => x^(m+1)) sample ∂probability k) =
      (expectedNormalizedMoment k t n m a).re := by
  simp_rw [spectralTest_power]
  rw [integral_const_mul]
  have hi := ((TensorHaar.continuous_compression_trace_power (baseProjection k t n) a m).comp
      (continuous_apply n)).integrable_of_hasCompactSupport (μ := probability k) (HasCompactSupport.of_compactSpace _)
  have hir := integral_re hi
  change (∫ sample, (Matrix.trace ((blockCompression (diagonalBlock (projection k t sample n)) a)^(m+1))).re ∂probability k) =
    (∫ sample, Matrix.trace ((blockCompression (diagonalBlock (projection k t sample n)) a)^(m+1)) ∂probability k).re at hir
  rw [hir]
  simp only [expectedNormalizedMoment, Complex.div_natCast_re]
  ring

lemma expected_spectralTest_chebyshev_hasSum (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    {K : ℝ} (hK : 0 < K) (hKa : (∑ i, |a i|) ≤ K)
    (c : ℤ → ℝ) (χ : ℝ → ℝ) (hc : Summable (fun j => |c j|))
    (hexp : ∀ x ∈ Icc (-K) K, HasSum
      (fun j => c j*(scaledChebyshev K j).eval x) (χ x)) :
    HasSum (fun j => c j*(∫ sample, spectralTest k t a n (scaledChebyshev K j).eval sample
      ∂probability k)) (∫ sample, spectralTest k t a n χ sample ∂probability k) := by
  apply StrongConvergence.hasSum_integrals_of_bounded_expansion
  · exact hc
  · intro j
    exact (continuous_spectralTest_polynomial k t a n _).aestronglyMeasurable
  · intro j
    exact Eventually.of_forall fun sample => spectralTest_abs_le k t a n hKa
      (fun x hx => scaledChebyshev_abs_le hK hx j) sample
  · exact Eventually.of_forall (spectralTest_chebyshev_hasSum k t a n hK hKa c χ hc hexp)


lemma spectralTest_nonneg (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (sample : Sample k) :
    0 ≤ spectralTest k t a n f sample := integral_nonneg hf

lemma spectralTest_edgeTest_lower (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    {r ε : ℝ} (hε : 0 < ε) (sample : Sample k)
    (h : r+ε ≤ largestEigenvalue (compressionHermitian k t a sample n)) :
    1/((n+1:ℕ):ℝ) ≤ spectralTest k t a n
      (ProjectionChannels.StrongConvergence.edgeTest r ε) sample := by
  classical
  obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (n+1)))
    (compressionHermitian k t a sample n).eigenvalues
  have hei : r+ε ≤ (compressionHermitian k t a sample n).eigenvalues i := by
    rw [← hmax]
    exact h
  rw [spectralTest_eq_sum]
  have hsum : (1 : ℝ) ≤ ∑ i, ProjectionChannels.StrongConvergence.edgeTest r ε
      ((compressionHermitian k t a sample n).eigenvalues i) := by
    have hs := Finset.single_le_sum (fun j _ =>
      ProjectionChannels.StrongConvergence.edgeTest_nonneg r ε
        ((compressionHermitian k t a sample n).eigenvalues j)) (Finset.mem_univ i)
    rwa [ProjectionChannels.StrongConvergence.edgeTest_of_ge hε hei] at hs
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1/((n+1:ℕ):ℝ))

/-- Markov's inequality converts a smooth expected trace bound into an actual
upper-edge probability estimate for the canonical Haar compression. -/
theorem upper_edge_probability_le_smooth_trace (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ)
    {r ε : ℝ} (hε : 0 < ε) :
    (probability k).real {sample | r+ε ≤ largestEigenvalue (compressionHermitian k t a sample n)} ≤
      ((n+1:ℕ):ℝ) * ∫ sample, spectralTest k t a n
        (ProjectionChannels.StrongConvergence.edgeTest r ε) sample ∂probability k := by
  let F := spectralTest k t a n (ProjectionChannels.StrongConvergence.edgeTest r ε)
  have hsub : {sample | r+ε ≤ largestEigenvalue (compressionHermitian k t a sample n)} ⊆
      {sample | 1/((n+1:ℕ):ℝ) ≤ F sample} :=
    fun sample hs => spectralTest_edgeTest_lower k t a n hε sample hs
  have hi : Integrable F (probability k) :=
    integrable_spectralTest_smooth k t a n (ProjectionChannels.StrongConvergence.edgeTest_contDiff r ε)
  have hnonneg : 0 ≤ᵐ[probability k] F := Eventually.of_forall fun sample =>
    spectralTest_nonneg k t a n (ProjectionChannels.StrongConvergence.edgeTest_nonneg r ε) sample
  have hm := mul_meas_ge_le_integral_of_nonneg hnonneg hi (1/((n+1:ℕ):ℝ))
  have hmono := measureReal_mono (μ := probability k) hsub
  have hpos : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hm hpos.le
  have hid : ((n+1:ℕ):ℝ) * (1/((n+1:ℕ):ℝ) *
      (probability k).real {sample | 1/((n+1:ℕ):ℝ) ≤ F sample}) =
      (probability k).real {sample | 1/((n+1:ℕ):ℝ) ≤ F sample} := by field_simp
  rw [hid] at hh
  exact hmono.trans hh

#print axioms upper_edge_probability_le_smooth_trace
#print axioms expected_spectralTest_chebyshev_hasSum
#print axioms integral_spectralTest_power_succ
#print axioms continuous_spectralTest_smooth
#print axioms spectralTest_chebyshev_hasSum
end ProjectionChannels.Canonical
