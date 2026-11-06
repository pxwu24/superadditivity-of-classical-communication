import HaarProjections.RevisionCanonicalEnsemble
import Mathlib.MeasureTheory.Group.Measure

/-!
# Output rotations of the canonical Haar ensemble

Left multiplication by the fixed lifted output unitary preserves the
canonical probability measure. Consequently, almost-sure assertions about
the entire projection sequence transfer to every fixed output basis.
This transport lemma is used in the completed convergence theorem in
`StrongConvergenceCanonicalStrong`.
-/

open MeasureTheory Filter Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section

namespace ProjectionChannels.Canonical

/-- The sequence of lifted output unitaries `1 ⊗ Uᴴ`. -/
def outputRotation (k : ℕ) (U : Matrix.unitaryGroup (Fin k) ℂ) : Sample k :=
  fun n => RevisionOutput.liftedOutputUnitary (A := Fin (n+1)) U

/-- Rotating the output is exactly a left translation of the Haar sample. -/
theorem projection_outputRotation (k : ℕ) (t : ℝ)
    (U : Matrix.unitaryGroup (Fin k) ℂ) (ω : Sample k) (n : ℕ) :
    projection k t (outputRotation k U * ω) n =
      RevisionOutput.localConjugate (projection k t ω n) U := by
  simp only [projection, Pi.mul_apply, Matrix.UnitaryGroup.mul_val,
    outputRotation, RevisionOutput.liftedOutputUnitary,
    Matrix.conjTranspose_mul, RevisionOutput.local_kronecker_conjTranspose,
    Matrix.conjTranspose_conjTranspose, RevisionOutput.localConjugate,
    Matrix.mul_assoc]

/-- Output rotation preserves the measure on the whole sample sequence. -/
theorem outputRotation_measurePreserving (k : ℕ)
    (U : Matrix.unitaryGroup (Fin k) ℂ) :
    MeasurePreserving (fun ω : Sample k => outputRotation k U * ω)
      (probability k) (probability k) := by
  letI : MeasurableMul (Sample k) := ContinuousMul.measurableMul
  exact measurePreserving_mul_left (probability k) (outputRotation k U)

/-- Any almost-sure property of the projection sequence transfers to the
same property of its output-conjugated sequence. No measurability assumption
on the predicate is needed. -/
theorem ae_projection_localConjugate (k : ℕ) (t : ℝ)
    (U : Matrix.unitaryGroup (Fin k) ℂ)
    (R : ((n : ℕ) → Matrix (Index k n) (Index k n) ℂ) → Prop)
    (hR : ∀ᵐ ω ∂probability k, R (projection k t ω)) :
    ∀ᵐ ω ∂probability k,
      R (fun n => RevisionOutput.localConjugate (projection k t ω n) U) := by
  have h := (outputRotation_measurePreserving k U).quasiMeasurePreserving.ae hR
  filter_upwards [h] with ω hω
  have hseq : projection k t (outputRotation k U * ω) =
      fun n => RevisionOutput.localConjugate (projection k t ω n) U :=
    funext (projection_outputRotation k t U ω)
  exact hseq ▸ hω

/-- A convenient Hermitian witness for the unrotated canonical compression. -/
def compressionHermitian (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (ω : Sample k) (n : ℕ) :
    (blockCompression (diagonalBlock (projection k t ω n)) a).IsHermitian := by
  apply blockCompression_isHermitian
  intro i
  exact (projection_isHermitian k t ω n).submatrix (fun b => (b,i))

private lemma eigenvalues_congr {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A = B) :
    hA.eigenvalues = hB.eigenvalues := by
  subst B
  rfl

/-- The rotated compression has the same eigenvalue enumeration as the
unrotated compression at the translated sample. Proof irrelevance removes
the difference between the two Hermitian witnesses. -/
theorem rotatedCompression_eigenvalues (k : ℕ) (t : ℝ)
    (U : Matrix.unitaryGroup (Fin k) ℂ) (a : Fin k → ℝ)
    (ω : Sample k) (n : ℕ) :
    (rotatedCompressionHermitian k (projection k t) (projection_isHermitian k t)
      U a ω n).eigenvalues =
      (compressionHermitian k t a (outputRotation k U * ω) n).eigenvalues := by
  apply eigenvalues_congr
  rw [projection_outputRotation]

/-- It is enough to prove the norm and weak spectral limits in the original
output basis. The same deterministic law then works for every fixed output
unitary, with the probability-one event allowed to depend on the test. -/
theorem fullBlockModifiedStrongInput_of_unrotated (k : ℕ) (t : ℝ)
    (h : ∀ a : Fin k → ℝ, ∃ ν : Measure ℝ,
      IsBernoulliFreeSumLaw k t a ν ∧
      (∀ c : ℝ, ∀ᵐ ω ∂probability k,
        Tendsto (fun n => ‖(c : ℂ) • (1 : Matrix (Index k n) (Index k n) ℂ) +
          ProjectionChannelsCP.amplify (diagonalTraceLinearMap a) (projection k t ω n)‖)
          atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν)))) ∧
      (∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        ∀ᵐ ω ∂probability k, Tendsto
          (fun n => (1/((n+1 : ℕ) : ℝ)) * ∑ i,
            f ((compressionHermitian k t a ω n).eigenvalues i))
          atTop (𝓝 (∫ x, f x ∂ν)))) :
    FullBlockModifiedStrongInput (probability k) k t
      (projection k t) (projection_isHermitian k t) := by
  intro U a
  obtain ⟨ν, hν, hnorm, hweak⟩ := h a
  refine ⟨ν, hν, ?_, ?_⟩
  · intro c
    have h := (outputRotation_measurePreserving k U).quasiMeasurePreserving.ae (hnorm c)
    filter_upwards [h] with ω hω
    simpa only [projection_outputRotation] using hω
  · intro f hf hb
    have h := (outputRotation_measurePreserving k U).quasiMeasurePreserving.ae
      (hweak f hf hb)
    filter_upwards [h] with ω hω
    apply hω.congr'
    filter_upwards [] with n
    exact congrArg
      (fun g : Fin (n+1) → ℝ => (1/((n+1 : ℕ) : ℝ)) * ∑ i, f (g i))
      (rotatedCompression_eigenvalues k t U a ω n).symm

/-- The final assembly may work entirely with the smaller block compression:
tensoring with the output identity and changing output basis cost no further
probabilistic estimates. -/
theorem fullBlockModifiedStrongInput_of_compression {k : ℕ} (hk : 0 < k) (t : ℝ)
    (h : ∀ a : Fin k → ℝ, ∃ ν : Measure ℝ,
      IsBernoulliFreeSumLaw k t a ν ∧
      (∀ c : ℝ, ∀ᵐ ω ∂probability k,
        Tendsto (fun n => ‖(c : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
          blockCompression (diagonalBlock (projection k t ω n)) a‖)
          atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν)))) ∧
      (∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        ∀ᵐ ω ∂probability k, Tendsto
          (fun n => (1/((n+1 : ℕ) : ℝ)) * ∑ i,
            f ((compressionHermitian k t a ω n).eigenvalues i))
          atTop (𝓝 (∫ x, f x ∂ν)))) :
    FullBlockModifiedStrongInput (probability k) k t
      (projection k t) (projection_isHermitian k t) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  apply fullBlockModifiedStrongInput_of_unrotated k t
  intro a
  obtain ⟨ν, hν, hnorm, hweak⟩ := h a
  refine ⟨ν, hν, ?_, hweak⟩
  intro c
  filter_upwards [hnorm c] with ω hω
  simpa only [norm_shift_amplified_diagonalTrace] using hω

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.projection_outputRotation
#print axioms ProjectionChannels.Canonical.outputRotation_measurePreserving
#print axioms ProjectionChannels.Canonical.ae_projection_localConjugate
#print axioms ProjectionChannels.Canonical.rotatedCompression_eigenvalues
#print axioms ProjectionChannels.Canonical.fullBlockModifiedStrongInput_of_unrotated
#print axioms ProjectionChannels.Canonical.fullBlockModifiedStrongInput_of_compression
