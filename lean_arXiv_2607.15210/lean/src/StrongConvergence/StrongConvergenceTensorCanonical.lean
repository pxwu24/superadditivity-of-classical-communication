import StrongConvergence.StrongConvergenceTensorBlockMoments
import StrongConvergence.StrongConvergenceTensorProjection
import StrongConvergence.StrongConvergenceTensorCompressionCycles

/-! Exact all-order Haar integration for the actual canonical ensemble.
The conclusions are finite-dimensional identities, with no convergence
hypothesis. The stable-range embedding merely bounds the tensor order by
the ambient dimension. -/

open Matrix MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section

namespace ProjectionChannels.TensorHaar

variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A] [DecidableEq K]

lemma continuous_compression_trace_power (P : Matrix (A×K) (A×K) ℂ)
    (a : K → ℝ) (m : ℕ) :
    Continuous (fun U : Matrix.unitaryGroup (A×K) ℂ =>
      Matrix.trace ((blockCompression (diagonalBlock (HaarMoment.orbit P U)) a) ^ (m+1))) := by
  simp_rw [trace_pow_path, HaarMoment.compression_entry]
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro x _
  apply continuous_finset_prod
  intro l _
  apply continuous_finset_sum
  intro b _
  exact continuous_const.mul
    ((HaarProjection.continuous_unitary_orbit P).matrix_elem _ _)

end ProjectionChannels.TensorHaar

namespace ProjectionChannels.Canonical
open TensorHaar

lemma integral_evaluation_continuous (k n : ℕ)
    (f : Matrix.unitaryGroup (Index k n) ℂ → ℂ) (hf : Continuous f) :
    (∫ ω, f (evaluation k n ω) ∂probability k) =
      ∫ U, f U ∂HaarProjection.unitaryHaar := by
  have hmp := evaluation_measurePreserving k n
  have hmap := integral_map (μ := probability k) hmp.measurable.aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  exact hmap.symm

lemma baseProjection_tensor_contractions {k : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n m : ℕ) :
    permutationContractions (tensorPower m (baseProjection k t n)) =
      fun σ : Equiv.Perm (Fin m) =>
        (rankSequence k t n : ℂ) ^ cycleCount σ.symm := by
  rw [permutationContractions_tensorPower_projection
    (baseProjection_isHermitian k t n) (baseProjection_idempotent k t n),
    baseProjection_rank ht0 ht1]

/-- Exact products of entries of the canonical Haar projection, at every
finite order in the stable dimension range. -/
theorem integral_projection_entry_product {k : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n m : ℕ)
    (e : Fin m ↪ Index k n) (i j : Fin m → Index k n) :
    (∫ ω, (∏ l, projection k t ω n (i l) (j l)) ∂probability k) =
      ∑ σ : Equiv.Perm (Fin m),
        ((permutationGram (Index k n) m)⁻¹ *ᵥ
          (fun τ : Equiv.Perm (Fin m) =>
            (rankSequence k t n : ℂ) ^ cycleCount τ.symm)) σ *
          (if i = (fun l => j (σ l)) then 1 else 0) := by
  change (∫ ω, tensorPower m
    (HaarMoment.orbit (baseProjection k t n) (evaluation k n ω)) i j ∂probability k) = _
  rw [integral_evaluation_continuous k n _
    (continuous_tensorPower_orbit_entry m (baseProjection k t n) i j)]
  change (∫ U : Matrix.unitaryGroup (Index k n) ℂ,
    (∏ l, HaarMoment.orbit (baseProjection k t n) U (i l) (j l))
      ∂HaarProjection.unitaryHaar) = _
  rw [integral_orbit_entry_product e (baseProjection k t n),
    baseProjection_tensor_contractions ht0 ht1]

/-- Exact expected powers of the actual canonical block compression. The
right-hand side is a deterministic finite permutation sum depending on the
rank sequence, the dimension, and the coefficient vector. -/
theorem integral_compression_trace_power {k : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n m : ℕ)
    (e : Fin (m+1) ↪ Index k n) (a : Fin k → ℝ) :
    (∫ ω, Matrix.trace
      ((blockCompression (diagonalBlock (projection k t ω n)) a) ^ (m+1))
        ∂probability k) =
      ∑ i : Fin (n+1), ∑ x : Fin m → Fin (n+1), ∑ b : Fin (m+1) → Fin k,
        (∏ l, (a (b l) : ℂ)) *
          ∑ σ : Equiv.Perm (Fin (m+1)),
            ((permutationGram (Index k n) (m+1))⁻¹ *ᵥ
              (fun τ : Equiv.Perm (Fin (m+1)) =>
                (rankSequence k t n : ℂ) ^ cycleCount τ.symm)) σ *
              (if (fun l => (pathRows i x l, b l)) =
                (fun l => (pathCols x i (σ l), b (σ l))) then 1 else 0) := by
  change (∫ ω, Matrix.trace ((blockCompression (diagonalBlock
    (HaarMoment.orbit (baseProjection k t n) (evaluation k n ω))) a) ^ (m+1))
      ∂probability k) = _
  rw [integral_evaluation_continuous k n _
    (continuous_compression_trace_power (baseProjection k t n) a m),
    TensorHaar.integral_compression_trace_power m e (baseProjection k t n) a,
    baseProjection_tensor_contractions ht0 ht1]

/-- The canonical compression moment with all input-coordinate sums evaluated.
For each fixed moment order this formula applies at every sufficiently large
input dimension, without an embedding hypothesis. -/
theorem integral_compression_trace_cycles {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n m : ℕ)
    (hmn : m ≤ n) (a : Fin k → ℝ) :
    (∫ ω, Matrix.trace
      ((blockCompression (diagonalBlock (projection k t ω n)) a) ^ (m+1))
        ∂probability k) =
      ∑ σ : Equiv.Perm (Fin (m+1)),
        projectionMomentCoefficients (Index k n) (m+1) (rankSequence k t n) σ *
          ((n+1 : ℕ) : ℂ) ^ cycleCount (finRotate (m+1) * σ) *
          weightedCycleMoment a σ := by
  let e : Fin (m+1) ↪ Index k n :=
    { toFun := fun i => (Fin.castLE (Nat.succ_le_succ hmn) i, ⟨0,hk⟩)
      inj' := by
        intro i j h
        apply Fin.ext
        exact congrArg (fun z : Index k n => z.1.val) h }
  change (∫ ω, Matrix.trace ((blockCompression (diagonalBlock
    (HaarMoment.orbit (baseProjection k t n) (evaluation k n ω))) a) ^ (m+1))
      ∂probability k) = _
  rw [integral_evaluation_continuous k n _
    (continuous_compression_trace_power (baseProjection k t n) a m),
    integral_projection_compression_trace_cycles m e
      (baseProjection_isHermitian k t n) (baseProjection_idempotent k t n) a,
    baseProjection_rank ht0 ht1]
  simp only [Fintype.card_fin]

/-- Each arbitrary fixed positive order has an eventual exact permutation
formula for the canonical ensemble. No convergence of these expressions is
asserted here. -/
theorem eventually_integral_compression_trace_cycles {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (m : ℕ) (a : Fin k → ℝ) :
    ∀ᶠ n in atTop,
      (∫ ω, Matrix.trace
        ((blockCompression (diagonalBlock (projection k t ω n)) a) ^ (m+1))
          ∂probability k) =
        ∑ σ : Equiv.Perm (Fin (m+1)),
          projectionMomentCoefficients (Index k n) (m+1) (rankSequence k t n) σ *
            ((n+1 : ℕ) : ℂ) ^ cycleCount (finRotate (m+1) * σ) *
            weightedCycleMoment a σ := by
  exact eventually_atTop.2 ⟨m,fun n hmn =>
    integral_compression_trace_cycles hk ht0 ht1 n m hmn a⟩

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.Canonical.integral_projection_entry_product
#print axioms ProjectionChannels.Canonical.integral_compression_trace_power
#print axioms ProjectionChannels.Canonical.integral_compression_trace_cycles
#print axioms ProjectionChannels.Canonical.eventually_integral_compression_trace_cycles
