import StrongConvergence.StrongConvergenceScalarMatrix
import Entropy.RevisionMatrixEntropy

/-! The weak-trace part uses the compression matrix, whereas the norm part
uses its amplification. For the singleton output these are the same actual
spectral trace, as follows from naturality of continuous functional calculus. -/

open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace ProjectionChannels.ScalarStrong
open RevisionMatrixEntropy
variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

lemma spectralTrace_eigenvalues (f : ℝ→ℝ) (hf : Continuous f)
    (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    spectralTrace f M=∑i,f (hM.eigenvalues i) := by
  have heq : M=unitaryDiagonal hM.eigenvectorUnitary hM.eigenvalues := hM.spectral_theorem
  conv_lhs => rw [heq]
  exact spectralTrace_unitaryDiagonal _ _ f hf

lemma spectralTrace_kronecker_identity_one (f : ℝ→ℝ) (hf : Continuous f)
    (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    spectralTrace f (Matrix.kronecker M (1:Matrix (Fin 1) (Fin 1) ℂ))=spectralTrace f M := by
  let φ := matrixTensorIdentity (n:=A) (k:=Fin 1)
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun X:Matrix A A ℂ=>X i.1 j.1*(1:Matrix (Fin 1) (Fin 1) ℂ) i.2 j.2)
    fun_prop
  have hφM : (φ M).IsHermitian := by
    change star (φ M)=φ M
    rw [←map_star,hM.isSelfAdjoint.star_eq]
  have hc := φ.map_cfc f M hf.continuousOn hφ hM hφM
  unfold spectralTrace
  change (Matrix.trace (cfc f (φ M))).re=(Matrix.trace (cfc f M)).re
  rw [←hc]
  change (Matrix.trace (Matrix.kronecker (cfc f M) (1:Matrix (Fin 1) (Fin 1) ℂ))).re=_
  simp [Matrix.trace_kronecker]

lemma scalar_compression_spectralTrace (P : Matrix (A×Fin 1) (A×Fin 1) ℂ)
    (hP : P.IsHermitian) (a : Fin 1→ℝ) (f : ℝ→ℝ) (hf : Continuous f) :
    spectralTrace f (blockCompression (diagonalBlock P) a)=spectralTrace f ((a 0:ℂ) • P) := by
  have hM : (blockCompression (diagonalBlock P) a).IsHermitian :=
    blockCompression_isHermitian _ (fun i=>hP.submatrix (fun b=>(b,i))) a
  rw [←spectralTrace_kronecker_identity_one f hf _ hM,←amplified_diagonalTrace,
    amplified_one_output]

lemma rotated_compression_eigenvalues_sum (t : ℝ) (ω : Canonical.Sample 1) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin 1) ℂ) (a : Fin 1→ℝ) (f : ℝ→ℝ) (hf : Continuous f) :
    (∑i,f ((rotatedCompressionHermitian 1 (Canonical.projection 1 t)
      (Canonical.projection_isHermitian 1 t) U a ω n).eigenvalues i))=
      spectralTrace f ((a 0:ℂ) • Canonical.projection 1 t ω n) := by
  rw [←spectralTrace_eigenvalues f hf _
    (rotatedCompressionHermitian 1 (Canonical.projection 1 t) (Canonical.projection_isHermitian 1 t) U a ω n)]
  rw [localConjugate_one_output]
  exact scalar_compression_spectralTrace _ (Canonical.projection_isHermitian 1 t ω n) a f hf

end ScalarStrong
end ProjectionChannels
