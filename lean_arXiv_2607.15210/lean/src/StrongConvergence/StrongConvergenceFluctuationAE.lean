import StrongConvergence.StrongConvergenceFluctuationAEBase
import StrongConvergence.StrongConvergenceFluctuationClasses
import StrongConvergence.StrongConvergenceFourthNormalization

/-! Almost-sure second moment convergence derived from the actual Haar variance. -/

open Matrix MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar

theorem normalized_second_square_formula {k : ℕ} {t : ℝ}
    (hk : 2 ≤ k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) (hn : 3 ≤ n) (a : Fin k → ℝ) :
    (∫ ω, (normalizedCompressionSecondTrace k t a ω n)^2 ∂probability k) =
      SecondVariance.squareMean (k:ℝ)
        ((rankSequence k t n:ℝ)/((k:ℝ)*((n:ℝ)+1)))
        ((1/((k:ℝ)*((n:ℝ)+1)))^2)
        (∑ i,a i) (∑ i,(a i)^2) (∑ i,(a i)^3) (∑ i,(a i)^4) := by
  have hk0 : 0 < k := by omega
  have hkR : (k:ℝ) ≠ 0 := by positivity
  have hnR : (n:ℝ)+1 ≠ 0 := by positivity
  have hN : (4:ℝ) ≤ (k:ℝ)*((n:ℝ)+1) := by
    have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have h1 : ((k:ℝ)*((n:ℝ)+1))^2-1 ≠ 0 := by nlinarith
  have h4 : ((k:ℝ)*((n:ℝ)+1))^2-4 ≠ 0 := by nlinarith
  have h9 : ((k:ℝ)*((n:ℝ)+1))^2-9 ≠ 0 := by nlinarith
  apply Complex.ofReal_injective
  rw [normalized_second_square_complex_identity,
    integral_compression_secondTrace_square_explicit hk0 ht0 ht1 n hn a]
  simpa only [fourthWeight, coefficientPowerSum_eq_coe_sum, pow_one,
    Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one] using
      fourthGramRow_normalized ((n:ℝ)+1) (k:ℝ) (rankSequence k t n:ℝ)
        (∑ i,a i) (∑ i,(a i)^2) (∑ i,(a i)^3) (∑ i,(a i)^4)
        hnR hkR h1 h4 h9

/-- The centered second spectral moment of the actual Haar ensemble has exactly
    the rational variance obtained from the fourth permutation contractions. -/
theorem secondTrace_centered_integral_eq_variance {k : ℕ} {t : ℝ}
    (hk : 2 ≤ k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) (hn : 3 ≤ n) (a : Fin k → ℝ) :
    (∫ ω,
      (normalizedCompressionSecondTrace k t a ω n-compressionSecondTraceCenter k t a n)^2
        ∂probability k) =
      SecondVariance.variance (k:ℝ)
        ((rankSequence k t n:ℝ)/((k:ℝ)*((n:ℝ)+1))) ((n:ℝ)+1)
        (∑ i,a i) (∑ i,(a i)^2) (∑ i,(a i)^3) (∑ i,(a i)^4) := by
  rw [secondTrace_centered_integral, normalized_second_square_formula hk ht0 ht1 n hn a,
    compressionSecondTraceCenter_formula hk ht0 ht1 n a]
  rfl

/-- A summable variance bound derived from Haar integration. -/
theorem exists_eventually_secondTrace_centered_integral_le {k : ℕ} {t : ℝ}
    (hk : 2 ≤ k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : Fin k → ℝ) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (∫ ω,
        (normalizedCompressionSecondTrace k t a ω n-compressionSecondTraceCenter k t a n)^2
          ∂probability k) ≤ C/((n:ℝ)+1)^2 := by
  have hk0 : 0 < k := by omega
  have hkR : (k:ℝ) ≠ 0 := by positivity
  obtain ⟨C, hC⟩ := SecondVariance.exists_eventually_variance_le
    (rank_density_tendsto hk0 ht0) hkR
    (∑ i,a i) (∑ i,(a i)^2) (∑ i,(a i)^3) (∑ i,(a i)^4)
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 3] with n hCn hn
  rw [secondTrace_centered_integral_eq_variance hk ht0 ht1 n hn a]
  exact hCn

/-- Almost-sure convergence of the second empirical moment for the canonical
    Haar block compression, with no strong-convergence or concentration input. -/
theorem ae_normalizedCompressionSecondTrace_tendsto {k : ℕ} {t : ℝ}
    (hk : 2 ≤ k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : Fin k → ℝ) :
    ∀ᵐ ω ∂probability k,
      Tendsto (fun n => normalizedCompressionSecondTrace k t a ω n) atTop
        (𝓝 (t^2*(∑ i,a i)^2+t*(1-t)/(k:ℝ)*(∑ i,(a i)^2))) := by
  obtain ⟨C, hC⟩ := exists_eventually_secondTrace_centered_integral_le hk ht0 ht1 a
  exact StrongConvergenceVarianceBorelCantelli.ae_tendsto_of_eventually_sq_integral_le
    (fun ω n => normalizedCompressionSecondTrace k t a ω n)
    (compressionSecondTraceCenter k t a) _ C
    (compressionSecondTraceCenter_tendsto hk ht0 ht1 a)
    (integrable_normalizedCompressionSecondTrace_centeredSquare k t a) hC

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.secondTrace_centered_integral_eq_variance
#print axioms ProjectionChannels.Canonical.ae_normalizedCompressionSecondTrace_tendsto
