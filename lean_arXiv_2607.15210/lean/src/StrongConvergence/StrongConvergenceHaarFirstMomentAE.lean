import StrongConvergence.StrongConvergenceCanonicalVariance
import StrongConvergence.StrongConvergenceVarianceBorelCantelli

/-! The first normalized compression moment converges almost surely for the
actual canonical Haar projection ensemble.  Its summable variance was derived
from finite Haar integrals; no strong-convergence input is used. -/
open Matrix MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.Canonical

theorem ae_normalizedCompressionTrace_tendsto {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0≤t) (ht1 : t≤1) (a : Fin k → ℝ) :
    ∀ᵐ ω ∂probability k,
      Tendsto (fun n => normalizedCompressionTrace k t a ω n)
        atTop (𝓝 (t*∑ i, a i)) := by
  apply StrongConvergenceVarianceBorelCantelli.ae_tendsto_of_eventually_sq_integral_le
    (μ := probability k) (normalizedCompressionTrace k t a) (compressionTraceCenter k t a)
    (t*∑ i,a i) ((∑ i,(a i)^2)/k) (compressionTraceCenter_tendsto hk ht0 a)
    (integrable_normalizedCompressionTrace_square k t a)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact normalizedCompressionTrace_variance_le hk ht0 ht1 a n hn

lemma normalizedCompressionTrace_basis_expansion (k : ℕ) (t : ℝ)
    (a : Fin k → ℝ) (ω : Sample k) (n : ℕ) :
    normalizedCompressionTrace k t a ω n =
      ∑ i : Fin k, a i * normalizedCompressionTrace k t
        (fun j => if j=i then 1 else 0) ω n := by
  simp only [normalizedCompressionTrace,compression_trace_sum]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_div,mul_div_assoc,Finset.mul_sum]

theorem ae_normalizedCompressionTrace_tendsto_all {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0≤t) (ht1 : t≤1) :
    ∀ᵐ ω ∂probability k, ∀ a : Fin k → ℝ,
      Tendsto (fun n => normalizedCompressionTrace k t a ω n)
        atTop (𝓝 (t*∑ i, a i)) := by
  have hb : ∀ᵐ ω ∂probability k, ∀ i : Fin k,
      Tendsto (fun n => normalizedCompressionTrace k t
        (fun j => if j=i then 1 else 0) ω n) atTop (𝓝 t) := by
    apply ae_all_iff.mpr
    intro i
    simpa using ae_normalizedCompressionTrace_tendsto hk ht0 ht1
      (fun j => if j=i then 1 else 0)
  filter_upwards [hb] with ω hω
  intro a
  have h := tendsto_finset_sum Finset.univ
    (fun i _ => (hω i).const_mul (a i))
  have hs : (∑ i : Fin k, a i*t)=t*∑ i, a i := by rw [← Finset.sum_mul]; ring
  rw [hs] at h
  simpa only [← normalizedCompressionTrace_basis_expansion] using h

#print axioms ae_normalizedCompressionTrace_tendsto
#print axioms ae_normalizedCompressionTrace_tendsto_all
end ProjectionChannels.Canonical
