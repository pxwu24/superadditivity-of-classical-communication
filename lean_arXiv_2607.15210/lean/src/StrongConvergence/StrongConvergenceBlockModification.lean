import StrongConvergence.StrongConvergenceBlockPolynomials

/-! The exact arbitrary square block-modification polynomial, and its
strong-convergence reduction. No random convergence or law identification
is assumed as an axiom or proved by this deterministic module. -/
open Matrix Finset Filter PreliminariesMatrix ProjectionChannelsCP
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergenceBlock
variable {A K : Type} [Fintype A] [Fintype K] [DecidableEq A] [DecidableEq K]

/-- The copy of a matrix unit in the fixed tensor factor. -/
def tensorUnit (A : Type) [Fintype A] [DecidableEq A] (i j : K) :
    Matrix (A×K) (A×K) ℂ := Matrix.kronecker (1 : Matrix A A ℂ) (matrixUnit i j)

lemma tensorUnit_sandwich_entry (X : Matrix (A×K) (A×K) ℂ)
    (p i j q : K) (a b : A) (u v : K) :
    (tensorUnit A p i*X*tensorUnit A j q) (a,u) (b,v)=
      if u=p ∧ v=q then X (a,i) (b,j) else 0 := by
  simp [tensorUnit,Matrix.mul_apply,Matrix.kronecker_apply,matrixUnit,
    Matrix.one_apply,Fintype.sum_prod_type,ite_and,Finset.sum_ite_eq,
    Finset.sum_ite_eq',eq_comm]
  split_ifs <;> rfl

lemma linearMap_entry_matrixUnits
    (Φ : Matrix K K ℂ →ₗ[ℂ] Matrix K K ℂ) (X : Matrix K K ℂ) (p q : K) :
    Φ X p q=∑ i,∑ j,X i j*Φ (matrixUnit i j) p q := by
  have h := congrArg (fun M => Φ M p q) (ProjectionChannels.matrixUnit_expansion X)
  simpa only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using h.symm

/-- Nechita's finite sandwich-polynomial decomposition for every complex
linear square block map, not only the weighted diagonal-trace map. -/
theorem amplify_eq_matrixUnit_polynomial
    (Φ : Matrix K K ℂ →ₗ[ℂ] Matrix K K ℂ) (X : Matrix (A×K) (A×K) ℂ) :
    amplify Φ X=∑ i,∑ j,∑ p,∑ q,Φ (matrixUnit i j) p q •
      (tensorUnit A p i*X*tensorUnit A j q) := by
  ext ⟨a,u⟩ ⟨b,v⟩
  change Φ (fun i j => X (a,i) (b,j)) u v = _
  rw [linearMap_entry_matrixUnits]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,tensorUnit_sandwich_entry,
    mul_ite,mul_zero]
  simp [ite_and,eq_comm,mul_comm,Finset.sum_ite_irrel]

/-- One variable for the matrix; all other variables are fixed tensor units. -/
def blockVariables (X : Matrix (A×K) (A×K) ℂ) : Option (K×K) → Matrix (A×K) (A×K) ℂ
  | none => X
  | some (i,j) => tensorUnit A i j

/-- The block polynomial is independent of the growing input dimension. -/
def blockModificationPolynomial (Φ : Matrix K K ℂ →ₗ[ℂ] Matrix K K ℂ) :
    StarPolynomial (Option (K×K)) :=
  StarPolynomial.sum univ fun i => StarPolynomial.sum univ fun j =>
    StarPolynomial.sum univ fun p => StarPolynomial.sum univ fun q =>
      .mul (.scalar (Φ (matrixUnit i j) p q))
        (.mul (.mul (.var (some (p,i))) (.var none)) (.var (some (j,q))))

theorem eval_blockModificationPolynomial
    (Φ : Matrix K K ℂ →ₗ[ℂ] Matrix K K ℂ) (X : Matrix (A×K) (A×K) ℂ) :
    (blockModificationPolynomial Φ).eval (blockVariables X)=amplify Φ X := by
  unfold blockModificationPolynomial
  simp only [StarPolynomial.eval_sum,StarPolynomial.eval,blockVariables,
    Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
  exact (amplify_eq_matrixUnit_polynomial Φ X).symm

/-- Joint strong convergence of the original matrix and the tensor units
implies strong convergence of every fixed block modification. The joint
convergence itself is the deep unresolved probabilistic step. -/
theorem stronglyConverges_blockModification
    (I : ℕ → Type) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]
    (τ : ∀ n,Matrix (I n×K) (I n×K) ℂ → ℂ) (σ : B → ℂ)
    (X : ∀ n,Matrix (I n×K) (I n×K) ℂ) (y : Option (K×K) → B)
    (h : StronglyConverges τ σ (fun n => blockVariables (X n)) y)
    (Φ : Matrix K K ℂ →ₗ[ℂ] Matrix K K ℂ) :
    StronglyConverges τ σ (fun n (_ : Unit) => amplify Φ (X n))
      (fun (_ : Unit) => (blockModificationPolynomial Φ).eval y) := by
  have hh := h.polynomial_map (fun (_ : Unit) => blockModificationPolynomial Φ)
  simpa only [eval_blockModificationPolynomial] using hh

end StrongConvergenceBlock
