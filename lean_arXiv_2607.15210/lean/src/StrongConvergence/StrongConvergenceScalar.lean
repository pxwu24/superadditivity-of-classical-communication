import StrongConvergence.StrongConvergenceScalarLaw
import StrongConvergence.StrongConvergenceScalarTrace
import StrongConvergence.StrongConvergenceScalarBridge

/-!
# Unconditional block-modified strong convergence for output dimension one

For k=1 every block modification is a scalar multiple of a projection.
Consequently the asserted affine norms and empirical spectral statistics
are deterministic: they hold for every unitary sample, without using Haar
measure, independence, or a strong-convergence assumption. This proves the
actual existing `FullBlockModifiedStrongInput` proposition in this base case.
No assertion for k≥2 is made here.
-/

open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace ProjectionChannels
open ScalarStrong

/-- Every continuous spectral statistic converges for every sample in the
canonical one-output ensemble. Boundedness of the test is unnecessary here. -/
theorem canonical_rotated_scalar_empirical_tendsto {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1)
    (ω : Canonical.Sample 1) (U : Matrix.unitaryGroup (Fin 1) ℂ) (a : Fin 1→ℝ)
    (f : ℝ→ℝ) (hf : Continuous f) :
    Tendsto (fun n => (1/((n+1:ℕ):ℝ))*∑i,
      f ((rotatedCompressionHermitian 1 (Canonical.projection 1 t)
        (Canonical.projection_isHermitian 1 t) U a ω n).eigenvalues i)) atTop
      (𝓝 (∫x,f x∂scalarBernoulliMeasure t (a 0))) := by
  rw [integral_scalarBernoulliMeasure ht0 ht1]
  have h := canonical_scalar_empirical_tendsto ht0 ht1 ω (a 0) f hf
  convert h using 1
  ext n
  rw [rotated_compression_eigenvalues_sum t ω n U a f hf]
  congr 2
  · push_cast
    rfl

/-- **Proved base case of block-modified strong convergence.** All real
coefficients, all affine shifts, all bounded continuous tests, and all output
unitary rotations in the existing theorem interface are covered.

The proof uses no `FullBlockModifiedStrongInput` hypothesis or other
probabilistic convergence assumption. -/
theorem canonical_fullBlockModifiedStrongInput_one {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    FullBlockModifiedStrongInput (Canonical.probability 1) 1 t
      (Canonical.projection 1 t) (Canonical.projection_isHermitian 1 t) := by
  intro U a
  have ha : (fun _ : Fin 1=>a 0)=a := by
    funext i
    exact congrArg a (Subsingleton.elim 0 i)
  refine ⟨scalarBernoulliMeasure t (a 0),?_,?_,?_⟩
  · simpa only [ha] using scalarBernoulliMeasure_isFreeSumLaw ht0 ht1 (a 0)
  · intro c
    rw [scalarBernoulliMeasure_abs_sSup ht0 ht1]
    apply Filter.Eventually.of_forall
    intro ω
    exact tendsto_const_nhds.congr' ((canonical_scalar_norm_eventually ht0 ht1 ω U a c).mono (fun _ h=>h.symm))
  · intro f hf _hbound
    exact Filter.Eventually.of_forall fun ω=>
      canonical_rotated_scalar_empirical_tendsto ht0.le ht1.le ω U a f hf

end ProjectionChannels
