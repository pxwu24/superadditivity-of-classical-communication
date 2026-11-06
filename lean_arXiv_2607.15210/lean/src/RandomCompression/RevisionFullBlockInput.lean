import RandomCompression.RevisionBernoulliCompression
import OutputStates.RevisionOutputUnitary

/-!
# The block-modified strong-convergence interface

The full block-modified strong-convergence theorem supplies one and the same
compact probability law for operator norms and empirical spectral measures.
Here weak convergence of the latter is expressed by bounded continuous real
test functions, its standard definition. Deterministic unitary changes of
output basis are included, as required by both Sections III and IV.

This proposition is proved for arbitrary admissible Haar projection sequences
by `ProjectionChannels.HaarSequence.fullBlockModifiedStrongInput` in
`StrongConvergence.StrongConvergenceHaarSequenceStrong`. It remains available
as an interface for the generic downstream deductions.
It contains no spectral-edge formula, logarithmic test, normalized Choi
moment, entropy formula, or nonadditivity conclusion.
-/

open MeasureTheory Filter
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels

def rotatedCompressionHermitian
    {Ω : Type*} (k : ℕ)
    (P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ)
    (hP : ∀ ω m, (P ω m).IsHermitian)
    (U : Matrix.unitaryGroup (Fin k) ℂ) (a : Fin k → ℝ) (ω : Ω) (m : ℕ) :
    (blockCompression (diagonalBlock (RevisionOutput.localConjugate (P ω m) U)) a).IsHermitian := by
  apply blockCompression_isHermitian
  intro i
  exact (RevisionOutput.localConjugate_isHermitian (hP ω m) U).submatrix (fun b => (b,i))

/-- The permitted full strong-convergence input, with its norm and weak-trace
parts tied to the same Bernoulli free-sum law for every fixed test/basis. -/
def FullBlockModifiedStrongInput {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (t : ℝ)
    (P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ)
    (hP : ∀ ω m, (P ω m).IsHermitian) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin k) ℂ, ∀ a : Fin k → ℝ,
    ∃ ν : Measure ℝ, IsBernoulliFreeSumLaw k t a ν ∧
      (∀ c : ℝ, ∀ᵐ ω ∂μ,
        Tendsto (fun m => ‖(c : ℂ) •
          (1 : Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ) +
          ProjectionChannelsCP.amplify (diagonalTraceLinearMap a)
            (RevisionOutput.localConjugate (P ω m) U)‖)
          atTop (nhds (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν)))) ∧
      (∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        ∀ᵐ ω ∂μ, Tendsto
          (fun m => (1/((m+1 : ℕ) : ℝ))*∑ i,
            f ((rotatedCompressionHermitian k P hP U a ω m).eigenvalues i))
          atTop (nhds (∫ x, f x ∂ν)))

theorem FullBlockModifiedStrongInput.to_amplified
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ} {t : ℝ}
    {P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ}
    {hP : ∀ ω m, (P ω m).IsHermitian}
    (h : FullBlockModifiedStrongInput μ k t P hP)
    (U : Matrix.unitaryGroup (Fin k) ℂ) :
    AmplifiedBlockModifiedStrongInput μ k t
      (fun ω m => RevisionOutput.localConjugate (P ω m) U) := by
  intro a
  obtain ⟨ν,hν,hnorm,hweak⟩ := h U a
  exact ⟨ν,hν,hnorm⟩

end ProjectionChannels
