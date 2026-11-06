import HaarProjections.HaarMeasure
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Tactic

/-!
# Measurability of matrix rank and partial-trace rank events

The proof uses the open condition that finitely many images are linearly
independent. It does not assume measurability or a minor characterization.
-/

open Matrix Set MeasureTheory

namespace ProjectionChannels

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Rank at least `r` is an open condition for complex rectangular matrices. -/
theorem isOpen_matrix_rank_ge (r : ℕ) :
    IsOpen {M : Matrix I J ℂ | r ≤ M.rank} := by
  classical
  have heq : {M : Matrix I J ℂ | r ≤ M.rank} =
      {M : Matrix I J ℂ | (r : Cardinal) ≤ M.mulVecLin.rank} := by
    ext M
    simp only [mem_setOf_eq, Matrix.rank, LinearMap.rank,
      ← Module.finrank_eq_rank, Nat.cast_le]
  rw [heq]
  simp only [LinearMap.le_rank_iff_exists_linearIndependent_finset,
    setOf_exists, ← exists_prop]
  apply isOpen_biUnion
  intro s hs
  have hcont : Continuous (fun M : Matrix I J ℂ =>
      fun x : (s : Set (J → ℂ)) => M *ᵥ (x : J → ℂ)) := by
    apply continuous_pi
    intro x
    exact continuous_id.matrix_mulVec continuous_const
  exact isOpen_setOf_linearIndependent.preimage hcont

/-- Every fixed matrix-rank event is Borel measurable. -/
theorem measurableSet_matrix_rank_eq (r : ℕ) :
    MeasurableSet {M : Matrix I J ℂ | M.rank = r} := by
  have heq : {M : Matrix I J ℂ | M.rank = r} =
      {M : Matrix I J ℂ | r ≤ M.rank} \ {M : Matrix I J ℂ | r + 1 ≤ M.rank} := by
    ext M
    simp only [mem_setOf_eq, mem_diff]
    omega
  rw [heq]
  exact (isOpen_matrix_rank_ge r).measurableSet.diff
    (isOpen_matrix_rank_ge (r + 1)).measurableSet

/-- Matrix rank is a measurable natural-valued function. -/
theorem measurable_matrix_rank : Measurable (Matrix.rank : Matrix I J ℂ → ℕ) := by
  intro t ht
  have heq : Matrix.rank ⁻¹' t = ⋃ r ∈ t, {M : Matrix I J ℂ | M.rank = r} := by
    ext M
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ =>
    measurableSet_matrix_rank_eq r

/-- Partial trace is continuous in the standard finite product topology. -/
theorem continuous_traceB {A B : Type*} [Fintype A] [Fintype B] :
    Continuous (PreliminariesMatrix.traceB :
      Matrix (A × B) (A × B) ℂ → Matrix A A ℂ) := by
  apply continuous_matrix
  intro a b
  unfold PreliminariesMatrix.traceB
  fun_prop

/-- The rank of the reduced operator is a measurable function. -/
theorem measurable_traceB_rank {A B : Type*} [Fintype A] [Fintype B] :
    Measurable (fun P : Matrix (A × B) (A × B) ℂ =>
      (PreliminariesMatrix.traceB P).rank) :=
  measurable_matrix_rank.comp continuous_traceB.measurable

/-- The precise event needed to transfer Gaussian full support to Haar projections. -/
theorem measurableSet_traceB_rank_eq {A B : Type*} [Fintype A] [Fintype B] (r : ℕ) :
    MeasurableSet {P : Matrix (A × B) (A × B) ℂ |
      (PreliminariesMatrix.traceB P).rank = r} :=
  measurable_traceB_rank (measurableSet_singleton r)

end ProjectionChannels

