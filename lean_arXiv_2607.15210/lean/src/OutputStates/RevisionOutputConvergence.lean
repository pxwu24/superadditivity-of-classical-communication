import OutputStates.RevisionOutputChannel
import OutputStates.RevisionOutputDuality
import OutputStates.OutputSpaceCompressionBridge

/-!
# Deterministic convergence mechanisms for Theorem III.1

The first theorem connects random-compression spectral limits to the
support of the actual locally normalized matrix channel. The second proves
Hausdorff convergence of actual nonempty compact convex sets from convergence
of their support functions, not from an assumed support/Hausdorff identity.
The matrix trace/operator norm identification and unitary-orbit description
of the limiting output body are not asserted by this file.
-/

open Filter Matrix Set Metric
open scoped Topology BigOperators ComplexOrder
set_option maxHeartbeats 800000
namespace RevisionOutput
open ProjectionChannels OutputSpaceVerification PreliminariesMatrix
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Diagonal blocks in the fixed tensor-product basis. -/
def diagonalBlocks (P : Matrix (A × B) (A × B) ℂ) (i : B) : Matrix A A ℂ :=
  fun a b => P (a,i) (b,i)

lemma diagonalBlocks_isHermitian {P : Matrix (A × B) (A × B) ℂ}
    (hP : P.IsHermitian) (i : B) : (diagonalBlocks P i).IsHermitian :=
  hP.submatrix (fun a => (a,i))

lemma traceB_eq_diagonalBlocks (P : Matrix (A × B) (A × B) ℂ) :
    traceB P = blockCompression (diagonalBlocks P) (fun _ => 1) := by
  ext a b
  simp [traceB, blockCompression, diagonalBlocks, Matrix.sum_apply]

lemma contraction_diagonal [Nonempty A] (P : Matrix (A × B) (A × B) ℂ) (a : B → ℝ) :
    contraction P (Matrix.diagonal (fun i => (a i : ℂ))) =
      blockCompression (diagonalBlocks P) a := by
  ext i j
  simp [contraction_entry, Matrix.diagonal_apply, blockCompression,
    diagonalBlocks, Matrix.sum_apply, mul_comm]

/-- Actual-channel diagonal support convergence: all finite matrix
normalizations, trace pairings, and maxima are derived from the definitions.
The input `hconv` is exactly the unnormalized compression limit, rather than
a hypothesis about the normalized channel's support. -/
theorem actual_output_diagonal_support_tendsto
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hthreshold : 1 < (k : ℝ) ^ 2 * t)
    (P : (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hP : ∀ N, (P N).IsHermitian)
    (hA : ∀ N, (traceB (P N)).PosDef)
    (hconv : ∀ c : Fin k → ℝ,
      Tendsto (fun N => largestEigenvalue
        (blockCompression_isHermitian (diagonalBlocks (P N))
          (fun i => diagonalBlocks_isHermitian (hP N) i) c))
        atTop (𝓝 (bodySupport k t c)))
    (a : Fin k → ℝ) :
    Tendsto (fun N => outputSupport (P N) (hA N).posSemidef.sqrt⁻¹
      (Matrix.diagonal (fun i => (a i : ℂ))))
      atTop (𝓝 (normalizedBodySupport k t a)) := by
  have hdiag : (Matrix.diagonal (fun i => (a i : ℂ))).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply, hij, Ne.symm hij]
  apply concrete_normalized_support_tendsto hk ht ht1 hthreshold a
    (fun N z => largestEigenvalue
      (blockCompression_isHermitian (diagonalBlocks (P N))
        (fun i => diagonalBlocks_isHermitian (hP N) i) (fun i => a i - z)))
  · intro N z
    rw [normalized_output_support (P N) (hP N) _
      (hA N).posSemidef.posSemidef_sqrt.isHermitian.inv _ hdiag]
    have ht := inverse_sqrt_threshold (traceB (P N))
      (contraction (P N) (Matrix.diagonal (fun i => (a i : ℂ))))
      (hA N) (contraction_isHermitian (hP N) hdiag) z
    have heq : contraction (P N) (Matrix.diagonal (fun i => (a i : ℂ))) -
        (z : ℂ) • traceB (P N) =
        blockCompression (diagonalBlocks (P N)) (fun i => a i - z) := by
      rw [contraction_diagonal, traceB_eq_diagonalBlocks, blockCompression_sub_constant]
    simpa only [heq] using ht
  · intro z
    exact hconv (fun i => a i - z)

section ConvexSets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma support_sub_le_dual_dist {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hunit : ∀ x ∈ K, ‖x‖ ≤ 1) (f g : E →L[ℝ] ℝ) :
    support K f - support K g ≤ dist f g := by
  obtain ⟨x, hx, hfx⟩ := (support_isGreatest hK hne f).1
  have hg := le_support hK hne g hx
  have hnorm := (f-g).le_opNorm x
  have hmul := mul_le_mul_of_nonneg_left (hunit x hx) (norm_nonneg (f-g))
  have hle : f x - g x ≤ ‖(f-g) x‖ := le_abs_self _
  simp only [ContinuousLinearMap.sub_apply, mul_one] at hnorm hmul hle
  rw [← hfx, dist_eq_norm]
  linarith

lemma support_lipschitz {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hunit : ∀ x ∈ K, ‖x‖ ≤ 1) (f g : E →L[ℝ] ℝ) :
    dist (support K f) (support K g) ≤ dist f g := by
  rw [Real.dist_eq, abs_le]
  have hu := support_sub_le_dual_dist hK hne hunit f g
  have hl := support_sub_le_dual_dist hK hne hunit g f
  rw [dist_comm g f] at hl
  exact ⟨by linarith, hu⟩

variable [ProperSpace E] [ProperSpace (E →L[ℝ] ℝ)]

/-- Pointwise support convergence yields Hausdorff convergence. The
support/Hausdorff duality and compact finite-net argument are proved in the
dependency chain; neither is assumed here. -/
theorem hausdorffDist_tendsto_of_support_tendsto
    (C : ℕ → Set E) (K : Set E)
    (hC : ∀ n, IsCompact (C n)) (hK : IsCompact K)
    (hneC : ∀ n, (C n).Nonempty) (hneK : K.Nonempty)
    (hcC : ∀ n, Convex ℝ (C n)) (hcK : Convex ℝ K)
    (hbC : ∀ n x, x ∈ C n → ‖x‖ ≤ 1) (hbK : ∀ x ∈ K, ‖x‖ ≤ 1)
    (hconv : ∀ f : E →L[ℝ] ℝ, ‖f‖ ≤ 1 →
      Tendsto (fun n => support (C n) f) atTop (𝓝 (support K f))) :
    Tendsto (fun n => hausdorffDist (C n) K) atTop (𝓝 0) := by
  have hu := uniform_tendsto_on_compact (closedBall (0 : E →L[ℝ] ℝ) 1)
    (isCompact_closedBall _ _)
    (fun n f => support (C n) f) (support K)
    (fun n f _ g _ => support_lipschitz (hC n) (hneC n) (hbC n) f g)
    (fun f _ g _ => support_lipschitz hK hneK hbK f g)
    (fun f hf => hconv f (mem_closedBall_zero_iff.mp hf))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hu (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound : hausdorffDist (C n) K ≤ ε / 2 := by
    apply hausdorffDist_le_of_support_le (hC n) hK (hneC n) hneK (hcC n) hcK
      (by positivity)
    intro f hf
    exact (hN n hn f (mem_closedBall_zero_iff.mpr hf)).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hausdorffDist_nonneg]
  linarith

end ConvexSets
end
end RevisionOutput
