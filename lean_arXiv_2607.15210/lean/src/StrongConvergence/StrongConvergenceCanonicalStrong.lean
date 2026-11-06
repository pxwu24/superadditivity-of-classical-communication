import StrongConvergence.StrongConvergenceCanonicalStrongLimit
import StrongConvergence.StrongConvergenceGenusLawIdentification

/-! The canonical block-modified strong-convergence theorem, proved from the
Haar moment expansion, polynomial method, Gaussian concentration, and the
formal free-cumulant identification. -/
open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels.Canonical

/-- The concrete canonical Haar-projection ensemble satisfies the full
block-modified strong-convergence input used by the channel-existence proofs. -/
theorem canonicalStrongInput : CanonicalStrongInput := by
  intro k hk t ht0 ht1
  apply fullBlockModifiedStrongInput_of_compression hk t
  intro a
  obtain ⟨ν,hprob,hν,hmom,hnorm,hweak⟩ :=
    exists_canonical_strong_spectral_limit hk ht0 ht1 a
  letI := hprob
  have hlaw : IsBernoulliFreeSumLaw k t a ν :=
    isBernoulliFreeSumLaw_of_genus_moments ν hk ht0.le ht1.le
      (Finset.sum_nonneg (fun i _ => abs_nonneg (a i)))
      (hν.mono fun x hx => abs_le.mpr hx) hmom
  refine ⟨ν,hlaw,?_,?_⟩
  · intro c
    exact hnorm.mono fun ω hω => hω c
  · intro f hf hb
    exact hweak.mono fun ω hω => hω f hf.continuousOn

#print axioms canonicalStrongInput
end ProjectionChannels.Canonical
