import Entropy.RevisionMatrixEntropyProjection
import Preliminaries.RevisionTensorChannels

open Matrix PreliminariesMatrix ProjectionChannels RevisionOutput RevisionBell Set
open scoped BigOperators ComplexOrder Topology
noncomputable section
namespace RevisionMatrixEntropy
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

lemma bellState_idempotent : bellState A*bellState A=bellState A := by
  have hc : (Fintype.card A:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  ext ⟨i,p⟩ ⟨j,q⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,bellState]
  by_cases hip : i=p
  · by_cases hjq : j=q
    · simp [hip,hjq,hc]
    · simp [hip,hjq]
  · simp [hip]

/-- The actual isotropic Bell matrix has one exceptional eigenvalue and
k²−1 equal eigenvalues, expressed directly at entropy level. -/
theorem matrixRenyiEntropy_isotropic (p : ℝ) (hp : 0<p) (r : ℝ) :
    matrixRenyiEntropy p (isotropic A r)=
      let b := (1-r)/(Fintype.card A:ℝ)^2
      let a := r+b
      if p=1 then -(a*Real.log a+((Fintype.card A:ℝ)^2-1)*(b*Real.log b))
      else Real.log (a^p+((Fintype.card A:ℝ)^2-1)*b^p)/(1-p) := by
  have heq : isotropic A r = r • bellState A+
      ((1-r)/(Fintype.card A:ℝ)^2) • (1:Matrix (A×A) (A×A) ℂ) := by
    ext i j
    simp [isotropic,Matrix.smul_apply,Complex.real_smul]
  rw [heq,matrixRenyiEntropy_affine_rankOne p hp (bellState A)
    bellState_posSemidef.isHermitian bellState_idempotent bellState_trace]
  simp [Fintype.card_prod,Nat.cast_mul,pow_two]

end RevisionMatrixEntropy
