import StrongConvergence.StrongConvergenceNorm
import Entropy.RevisionMatrixEntropy
import Mathlib.Analysis.SpecificLimits.Basic

/-! An explicit obstruction to replacing strong convergence by moment
convergence: one fixed spectral outlier has vanishing normalized mass. -/
open Matrix MeasureTheory Filter Set
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergence

def spikeProjection (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  Matrix.diagonal (fun i => if i=0 then 1 else 0)

def spikeMatrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (2:ℂ) • spikeProjection n

theorem spikeProjection_hermitian (n : ℕ) : (spikeProjection n).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  split_ifs <;> simp

theorem spikeProjection_idempotent (n : ℕ) : spikeProjection n * spikeProjection n = spikeProjection n := by
  unfold spikeProjection
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  split_ifs <;> simp

theorem spikeProjection_norm (n : ℕ) : ‖spikeProjection n‖ = 1 := by
  have hpos : 0 < ‖spikeProjection n‖ := norm_pos_iff.mpr (by
    intro h
    have h00 := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => M 0 0) h
    simpa [spikeProjection] using h00)
  have hn := Matrix.l2_opNorm_conjTranspose_mul_self (spikeProjection n)
  rw [(spikeProjection_hermitian n).eq, spikeProjection_idempotent] at hn
  nlinarith

theorem spikeMatrix_norm (n : ℕ) : ‖spikeMatrix n‖ = 2 := by
  rw [spikeMatrix, norm_smul, spikeProjection_norm]
  norm_num

lemma spikeMatrix_unitaryDiagonal (n : ℕ) : spikeMatrix n =
    RevisionMatrixEntropy.unitaryDiagonal 1 (fun i : Fin (n+1) => if i=0 then 2 else 0) := by
  ext i j
  simp [spikeMatrix, spikeProjection, RevisionMatrixEntropy.unitaryDiagonal,
    RevisionMatrixEntropy.unitaryConjugateDiagonalHom, Matrix.diagonal_apply]
  split_ifs <;> norm_num

theorem spikeMatrix_spectralTrace (n : ℕ) (f : ℝ → ℝ) (hf : Continuous f) :
    RevisionMatrixEntropy.spectralTrace f (spikeMatrix n) =
      ((n+1:ℕ):ℝ)*f 0 + (f 2-f 0) := by
  rw [spikeMatrix_unitaryDiagonal,
    RevisionMatrixEntropy.spectralTrace_unitaryDiagonal _ _ f hf]
  have hterm (i : Fin (n+1)) : f (if i=0 then 2 else 0) =
      f 0 + if i=0 then f 2-f 0 else 0 := by split_ifs <;> ring
  simp_rw [hterm]
  simp [Finset.sum_add_distrib]

/-- Every continuous spectral test converges to its value at zero, although
operator norms remain exactly two. In particular, all fixed moments converge. -/
theorem spikeMatrix_weak_spectral_limit (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun n => (1/((n+1:ℕ):ℝ))*
      RevisionMatrixEntropy.spectralTrace f (spikeMatrix n)) atTop (𝓝 (f 0)) := by
  have hinv : Tendsto (fun n : ℕ => (1/((n+1:ℕ):ℝ))) atTop (𝓝 0) := by
    apply tendsto_one_div_atTop_nhds_zero_nat.comp
    exact tendsto_add_atTop_nat 1
  have heq (n : ℕ) : (1/((n+1:ℕ):ℝ))*
      RevisionMatrixEntropy.spectralTrace f (spikeMatrix n) =
      f 0 + (1/((n+1:ℕ):ℝ))*(f 2-f 0) := by
    rw [spikeMatrix_spectralTrace n f hf]
    have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [heq]
  simpa using tendsto_const_nhds.add (hinv.mul_const (f 2-f 0))

#print axioms spikeMatrix_norm
#print axioms spikeMatrix_weak_spectral_limit
end StrongConvergence
