import HaarProjections.RevisionCanonicalEnsemble
import Entropy.RevisionMatrixEntropy
import HaarProjections.ProjectionOrbit
import RandomCompression.ProjectionStrongConvergence

open Matrix Filter
open scoped BigOperators Topology
noncomputable section

namespace ProjectionChannels
open RevisionMatrixEntropy
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {A : Type} [Fintype A] [DecidableEq A]

theorem spectralTrace_eq_sum_eigenvalues (f : ℝ → ℝ) (hf : Continuous f)
    (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    spectralTrace f M = ∑ i, f (hM.eigenvalues i) := by
  have he : M = unitaryDiagonal hM.eigenvectorUnitary hM.eigenvalues := hM.spectral_theorem
  conv_lhs => rw [he]
  exact spectralTrace_unitaryDiagonal _ _ f hf

lemma scalar_unitaryDiagonal (U : Matrix.unitaryGroup A ℂ) (v : A → ℝ) (a : ℝ) :
    a • unitaryDiagonal U v = unitaryDiagonal U (fun i => a*v i) := by
  have he : (fun i => ((a*v i : ℝ) : ℂ)) = a • (fun i => (v i : ℂ)) := by
    ext i
    simp [Complex.real_smul]
  unfold unitaryDiagonal
  rw [he, map_smul]

/-- Exact continuous spectral statistics of every scalar multiple of a
finite-dimensional orthogonal projection. -/
theorem spectralTrace_scalar_projection (f : ℝ → ℝ) (hf : Continuous f)
    [Nonempty A]
    (P : Matrix A A ℂ) (hP : P.IsHermitian) (hId : P*P=P) (a : ℝ) :
    spectralTrace f (a • P) =
      ((Fintype.card A : ℝ) - (P.rank : ℝ))*f 0 + (P.rank : ℝ)*f a := by
  have he : P = unitaryDiagonal hP.eigenvectorUnitary hP.eigenvalues := hP.spectral_theorem
  have hs : ∑ i, hP.eigenvalues i = (P.rank : ℝ) := by
    have h := RevisionOutput.trace_eq_sum_eigenvalues P hP
    rw [ProjectionStrongConvergence.trace_projection_eq_rank P hId] at h
    have hr := congrArg Complex.re h
    simpa only [Complex.natCast_re, Complex.re_sum, Complex.ofReal_re] using hr.symm
  have heach (i : A) : f (a*hP.eigenvalues i) =
      f 0 + (f a-f 0)*hP.eigenvalues i := by
    rcases ProjectionOrbit.eigenvalues_zero_or_one hP hId i with hi | hi <;> simp [hi]
  conv_lhs => rw [he, scalar_unitaryDiagonal,
    spectralTrace_unitaryDiagonal _ _ f hf]
  simp_rw [heach]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, hs]
  ring

theorem sum_eigenvalues_scalar_projection (f : ℝ → ℝ) (hf : Continuous f)
    [Nonempty A]
    (P : Matrix A A ℂ) (hP : P.IsHermitian) (hId : P*P=P) (a : ℝ)
    (hQ : (a • P).IsHermitian) :
    (∑ i, f (hQ.eigenvalues i)) =
      ((Fintype.card A : ℝ) - (P.rank : ℝ))*f 0 + (P.rank : ℝ)*f a := by
  rw [← spectralTrace_eq_sum_eigenvalues f hf _ hQ]
  exact spectralTrace_scalar_projection f hf P hP hId a

theorem canonical_scalar_spectralTrace {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ω : Canonical.Sample 1) (n : ℕ) (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    spectralTrace f (a • Canonical.projection 1 t ω n) =
      ((n+1 : ℕ) - (Canonical.rankSequence 1 t n : ℝ))*f 0 +
        (Canonical.rankSequence 1 t n : ℝ)*f a := by
  rw [spectralTrace_scalar_projection f hf _
    (Canonical.projection_isHermitian 1 t ω n)
    (Canonical.projection_idempotent 1 t ω n), Canonical.projection_rank ht0 ht1]
  simp [Canonical.Index]

theorem canonical_scalar_eigenvalue_sum {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ω : Canonical.Sample 1) (n : ℕ) (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hQ : (a • Canonical.projection 1 t ω n).IsHermitian) :
    (∑ i, f (hQ.eigenvalues i)) =
      ((n+1 : ℕ) - (Canonical.rankSequence 1 t n : ℝ))*f 0 +
        (Canonical.rankSequence 1 t n : ℝ)*f a := by
  rw [← spectralTrace_eq_sum_eigenvalues f hf _ hQ]
  exact canonical_scalar_spectralTrace ht0 ht1 ω n a f hf

theorem canonical_scalar_empirical_tendsto {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ω : Canonical.Sample 1) (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun n : ℕ => (1 / (n+1 : ℝ)) *
      spectralTrace f (a • Canonical.projection 1 t ω n)) atTop
        (𝓝 ((1-t)*f 0 + t*f a)) := by
  have hr : Tendsto (fun n : ℕ => (Canonical.rankSequence 1 t n : ℝ)/(n+1))
      atTop (𝓝 t) := by
    simpa using (Canonical.rank_density_tendsto (k := 1) (by omega) ht0)
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hr).mul_const (f 0)).add
    (hr.mul_const (f a))
  convert h using 1
  ext n
  rw [canonical_scalar_spectralTrace ht0 ht1 ω n a f hf]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  push_cast
  field_simp

end ProjectionChannels
