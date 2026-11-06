import Entropy.RevisionMatrixEntropyConjugate
import HaarProjections.ProjectionOrbit

open Matrix PreliminariesMatrix ProjectionChannels RevisionOutput Set
open scoped BigOperators ComplexOrder Topology
noncomputable section
namespace RevisionMatrixEntropy
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

lemma unitaryDiagonal_affine (U : Matrix.unitaryGroup A ℂ) (v : A→ℝ) (r b : ℝ) :
    unitaryDiagonal U (fun i=>r*v i+b)=r • unitaryDiagonal U v+b • (1:Matrix A A ℂ) := by
  have heq : (fun i=>((r*v i+b:ℝ):ℂ)) = r • (fun i=>(v i:ℂ))+b • (1:A→ℂ) := by
    ext i
    simp [Complex.real_smul]
  unfold unitaryDiagonal
  rw [heq,map_add,map_smul,map_smul,map_one]

/-- Exact functional-calculus trace of an affine combination of a rank-one
orthogonal projection and the identity. -/
theorem spectralTrace_affine_rankOne (f : ℝ→ℝ) (hf : Continuous f)
    (P : Matrix A A ℂ) (hP : P.IsHermitian) (hp : P*P=P) (htr : Matrix.trace P=1)
    (r b : ℝ) :
    spectralTrace f (r • P+b • (1:Matrix A A ℂ))=
      f (r+b)+((Fintype.card A:ℝ)-1)*f b := by
  have heq : P=unitaryDiagonal hP.eigenvectorUnitary hP.eigenvalues := hP.spectral_theorem
  have hs : ∑ i,hP.eigenvalues i=1 := by
    have hh := RevisionOutput.trace_eq_sum_eigenvalues P hP
    rw [htr] at hh
    have hh' := congrArg Complex.re hh
    simpa only [Complex.one_re,Complex.re_sum,Complex.ofReal_re] using hh'.symm
  have heach (i:A) : f (r*hP.eigenvalues i+b)=
      f b+(f (r+b)-f b)*hP.eigenvalues i := by
    rcases ProjectionOrbit.eigenvalues_zero_or_one hP hp i with hi|hi <;> simp [hi]
  conv_lhs => rw [heq,←unitaryDiagonal_affine,spectralTrace_unitaryDiagonal _ _ f hf]
  simp_rw [heach]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ←Finset.mul_sum,hs]
  ring

/-- The two-level Rényi formula, including the von Neumann value. -/
theorem matrixRenyiEntropy_affine_rankOne (p : ℝ) (hp0 : 0<p)
    (P : Matrix A A ℂ) (hP : P.IsHermitian) (hp : P*P=P) (htr : Matrix.trace P=1)
    (r b : ℝ) :
    matrixRenyiEntropy p (r • P+b • (1:Matrix A A ℂ))=
      if p=1 then -((r+b)*Real.log (r+b)+((Fintype.card A:ℝ)-1)*(b*Real.log b))
      else Real.log ((r+b)^p+((Fintype.card A:ℝ)-1)*b^p)/(1-p) := by
  unfold matrixRenyiEntropy
  split_ifs
  · rw [spectralTrace_affine_rankOne _ Real.continuous_mul_log P hP hp htr]
  · rw [spectralTrace_affine_rankOne _ (Real.continuous_rpow_const hp0.le) P hP hp htr]

end RevisionMatrixEntropy
