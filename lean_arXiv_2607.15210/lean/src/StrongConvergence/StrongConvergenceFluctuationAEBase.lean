import StrongConvergence.StrongConvergenceFluctuationMoments
import StrongConvergence.StrongConvergenceHaarSecondCompression
import StrongConvergence.StrongConvergenceVarianceBorelCantelli
import StrongConvergence.StrongConvergenceSecondVarianceAsymptotics

/-!
# Almost-sure second moments of canonical Haar block compressions

The variance estimate here is obtained from the actual fourth-order Haar
integral, including the cancellation of its leading term. No concentration
or strong-convergence assertion is supplied as a hypothesis.
-/

open Matrix MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section

namespace ProjectionChannels.Canonical
open TensorHaar

def normalizedCompressionSecondTrace (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (ω : Sample k) (n : ℕ) : ℝ :=
  (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^2)).re /
    ((n:ℝ)+1)

def compressionSecondTraceCenter (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, normalizedCompressionSecondTrace k t a ω n ∂probability k

lemma continuous_compressionSecondTrace (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ) :
    Continuous (fun ω : Sample k =>
      Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^2)) := by
  exact (continuous_compression_trace_power (baseProjection k t n) a 1).comp
    (continuous_apply n)

lemma continuous_normalizedCompressionSecondTrace (k : ℕ) (t : ℝ)
    (a : Fin k → ℝ) (n : ℕ) :
    Continuous (fun ω => normalizedCompressionSecondTrace k t a ω n) :=
  (Complex.continuous_re.comp (continuous_compressionSecondTrace k t a n)).div_const _

lemma coe_re_compressionSecondTrace (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (ω : Sample k) (n : ℕ) :
    ((Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^2)).re : ℂ) =
      Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^2) := by
  have hS : (blockCompression (diagonalBlock (projection k t ω n)) a).IsHermitian := by
    apply blockCompression_isHermitian
    intro i
    exact (projection_isHermitian k t ω n).submatrix (fun u => (u,i))
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => (hS.pow 2).coe_re_apply_self i)

lemma integrable_normalizedCompressionSecondTrace (k : ℕ) (t : ℝ)
    (a : Fin k → ℝ) (n : ℕ) :
    Integrable (fun ω => normalizedCompressionSecondTrace k t a ω n) (probability k) :=
  (continuous_normalizedCompressionSecondTrace k t a n).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integrable_normalizedCompressionSecondTrace_square (k : ℕ) (t : ℝ)
    (a : Fin k → ℝ) (n : ℕ) :
    Integrable (fun ω => (normalizedCompressionSecondTrace k t a ω n)^2) (probability k) :=
  ((continuous_normalizedCompressionSecondTrace k t a n).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integrable_normalizedCompressionSecondTrace_centeredSquare (k : ℕ) (t : ℝ)
    (a : Fin k → ℝ) (n : ℕ) :
    Integrable (fun ω =>
      (normalizedCompressionSecondTrace k t a ω n-compressionSecondTraceCenter k t a n)^2)
        (probability k) :=
  (((continuous_normalizedCompressionSecondTrace k t a n).sub continuous_const).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem compressionSecondTraceCenter_tendsto {k : ℕ} {t : ℝ}
    (hk : 2 ≤ k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : Fin k → ℝ) :
    Tendsto (compressionSecondTraceCenter k t a) atTop
      (𝓝 (t^2*(∑ i,a i)^2+t*(1-t)/(k:ℝ)*(∑ i,(a i)^2))) := by
  change Tendsto (fun n => compressionSecondTraceCenter k t a n) atTop _
  simp only [compressionSecondTraceCenter, normalizedCompressionSecondTrace, integral_div]
  exact normalized_second_moment_tendsto hk ht0 ht1 a

lemma secondTrace_centered_integral (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ) :
    (∫ ω,
      (normalizedCompressionSecondTrace k t a ω n-compressionSecondTraceCenter k t a n)^2
        ∂probability k) =
      (∫ ω, (normalizedCompressionSecondTrace k t a ω n)^2 ∂probability k) -
        (compressionSecondTraceCenter k t a n)^2 := by
  let c := compressionSecondTraceCenter k t a n
  let F := fun ω => normalizedCompressionSecondTrace k t a ω n
  have hF : Integrable F (probability k) := integrable_normalizedCompressionSecondTrace k t a n
  have hF2 : Integrable (fun ω => (F ω)^2) (probability k) :=
    integrable_normalizedCompressionSecondTrace_square k t a n
  have hpoint : (fun ω => (F ω-c)^2) = (fun ω => (F ω)^2-2*c*F ω+c^2) := by
    funext ω
    ring
  change (∫ ω, (F ω-c)^2 ∂probability k) = (∫ ω, (F ω)^2 ∂probability k)-c^2
  have hA : Integrable (fun ω => (F ω)^2-2*c*F ω) (probability k) :=
    hF2.sub (hF.const_mul (2*c))
  rw [hpoint, integral_add hA (integrable_const (c^2)),
    integral_sub hF2 (hF.const_mul (2*c)), integral_const_mul, integral_const]
  have hc : (∫ ω, F ω ∂probability k) = c := rfl
  rw [hc]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
  ring

lemma normalized_second_square_complex_identity (k : ℕ) (t : ℝ)
    (a : Fin k → ℝ) (n : ℕ) :
    ((∫ ω, (normalizedCompressionSecondTrace k t a ω n)^2 ∂probability k : ℝ) : ℂ) =
      (∫ ω, (Matrix.trace
        ((blockCompression (diagonalBlock (projection k t ω n)) a)^2))^2
          ∂probability k) / ((n:ℂ)+1)^2 := by
  rw [← integral_complex_ofReal, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [normalizedCompressionSecondTrace, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    coe_re_compressionSecondTrace, div_pow]

theorem compressionSecondTraceCenter_formula {k : ℕ} {t : ℝ}
    (hk : 2 ≤ k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) (a : Fin k → ℝ) :
    compressionSecondTraceCenter k t a n =
      SecondVariance.mean (k:ℝ)
        ((rankSequence k t n:ℝ)/((k:ℝ)*((n:ℝ)+1)))
        ((1/((k:ℝ)*((n:ℝ)+1)))^2) (∑ i,a i) (∑ i,(a i)^2) := by
  simpa only [compressionSecondTraceCenter, normalizedCompressionSecondTrace,
    integral_div, SecondVariance.mean] using
      normalized_second_moment_formula hk ht0 ht1 n a

end ProjectionChannels.Canonical
