import StrongConvergence.StrongConvergenceScalarTrace

open Matrix Filter
open scoped BigOperators Topology
noncomputable section

namespace ProjectionChannels
open RevisionMatrixEntropy
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Exact spectral statistics of the canonical projection in every positive
output dimension, for every sample and every real scalar coefficient. -/
theorem canonical_projection_scalar_spectralTrace {k : ℕ} (hk : 0 < k)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ω : Canonical.Sample k) (n : ℕ) (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    spectralTrace f (a • Canonical.projection k t ω n) =
      (((n+1)*k : ℕ) - (Canonical.rankSequence k t n : ℝ))*f 0 +
        (Canonical.rankSequence k t n : ℝ)*f a := by
  letI : NeZero k := ⟨hk.ne'⟩
  rw [spectralTrace_scalar_projection f hf _
    (Canonical.projection_isHermitian k t ω n)
    (Canonical.projection_idempotent k t ω n), Canonical.projection_rank ht0 ht1]
  simp [Canonical.Index]

/-- The empirical spectral measure of every unmodified canonical projection
converges to its actual dilated Bernoulli law, sample by sample. -/
theorem canonical_projection_scalar_empirical_tendsto {k : ℕ} (hk : 0 < k)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ω : Canonical.Sample k) (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun n : ℕ => (1 / ((k : ℝ)*(n+1))) *
      spectralTrace f (a • Canonical.projection k t ω n)) atTop
        (𝓝 ((1-t)*f 0 + t*f a)) := by
  have hr := Canonical.rank_density_tendsto hk ht0
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hr).mul_const (f 0)).add
    (hr.mul_const (f a))
  convert h using 1
  ext n
  rw [canonical_projection_scalar_spectralTrace hk ht0 ht1 ω n a f hf]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp [hk', hn]
  ring_nf
  simp

/-- Eigenvalue-list form of the exact spectral statistic. -/
theorem canonical_projection_scalar_eigenvalue_sum {k : ℕ} (hk : 0 < k)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ω : Canonical.Sample k) (n : ℕ) (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hQ : (a • Canonical.projection k t ω n).IsHermitian) :
    (∑ i, f (hQ.eigenvalues i)) =
      (((n+1)*k : ℕ) - (Canonical.rankSequence k t n : ℝ))*f 0 +
        (Canonical.rankSequence k t n : ℝ)*f a := by
  rw [← spectralTrace_eq_sum_eigenvalues f hf _ hQ]
  exact canonical_projection_scalar_spectralTrace hk ht0 ht1 ω n a f hf

end ProjectionChannels
