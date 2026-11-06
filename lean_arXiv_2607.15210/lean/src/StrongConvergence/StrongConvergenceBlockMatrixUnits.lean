import StrongConvergence.StrongConvergenceBlockModification
import RandomCompression.RevisionBernoulliTensor

/-! The deterministic tensor-matrix-unit family has an exact joint strong
limit. Unlike the Haar-mixed tuple, this prerequisite needs no probability
or freeness theorem: every polynomial is carried by an isometric star
algebra embedding, and its normalized trace is unchanged. -/
open Matrix Finset Filter PreliminariesMatrix ProjectionChannelsCP
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergenceBlock

local instance matrixCStarAlgebra {n : Type*} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance
  norm_mul_self_le := CStarRing.norm_mul_self_le

variable {A K : Type} [Fintype A] [Fintype K] [DecidableEq A] [DecidableEq K]

def matrixIdentityTensor : Matrix K K ℂ →⋆ₐ[ℂ] Matrix (A×K) (A×K) ℂ where
  toFun M := Matrix.kronecker (1 : Matrix A A ℂ) M
  map_zero' := by simp
  map_one' := Matrix.one_kronecker_one
  map_add' M N := Matrix.kronecker_add 1 M N
  map_mul' M N := by
    simpa only [Matrix.one_mul] using Matrix.mul_kronecker_mul (1 : Matrix A A ℂ) 1 M N
  commutes' c := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [Matrix.kronecker_apply,Matrix.algebraMap_eq_diagonal,Matrix.diagonal_apply,Matrix.one_apply]
    split_ifs <;> simp_all
  map_star' M := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Matrix.kronecker_apply,Matrix.one_apply]
    split_ifs <;> simp_all

lemma matrixIdentityTensor_injective [Nonempty A] :
    Function.Injective (matrixIdentityTensor (A:=A) (K:=K)) := by
  intro M N h
  let a : A := Classical.choice inferInstance
  ext i j
  have hh := congrArg (fun X : Matrix (A×K) (A×K) ℂ => X (a,i) (a,j)) h
  simpa [matrixIdentityTensor,Matrix.kronecker_apply] using hh

lemma norm_identity_kronecker [Nonempty A] (M : Matrix K K ℂ) :
    ‖Matrix.kronecker (1 : Matrix A A ℂ) M‖=‖M‖ :=
  NonUnitalStarAlgHom.norm_map (matrixIdentityTensor (A:=A) (K:=K)) matrixIdentityTensor_injective M

lemma StarPolynomial.map_eval {ι R S : Type*}
    [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
    [Ring S] [Algebra ℂ S] [StarRing S] [StarModule ℂ S]
    (F : R →⋆ₐ[ℂ] S) (x : ι → R) (p : StarPolynomial ι) :
    F (p.eval x)=p.eval (fun i => F (x i)) := by
  induction p with
  | scalar c => exact F.commutes c
  | var i => rfl
  | add p q hp hq => simp only [StarPolynomial.eval,map_add,hp,hq]
  | mul p q hp hq => simp only [StarPolynomial.eval,map_mul,hp,hq]
  | adjoint p hp => simp only [StarPolynomial.eval,map_star,hp]

/-- Actual normalized trace. -/
def matrixTrace {N : Type} [Fintype N] (X : Matrix N N ℂ) : ℂ :=
  Matrix.trace X/(Fintype.card N:ℂ)

lemma matrixTrace_identity_tensor [Nonempty A] [Nonempty K] (M : Matrix K K ℂ) :
    matrixTrace (Matrix.kronecker (1 : Matrix A A ℂ) M)=matrixTrace M := by
  have hA : (Fintype.card A:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  unfold matrixTrace
  rw [Matrix.kronecker,Matrix.trace_kronecker,Matrix.trace_one,Fintype.card_prod,Nat.cast_mul]
  field_simp
  ring

lemma eval_tensorUnits (p : StarPolynomial (K×K)) :
    p.eval (fun ij => tensorUnit A ij.1 ij.2)=
      Matrix.kronecker (1 : Matrix A A ℂ) (p.eval (fun ij => matrixUnit ij.1 ij.2)) :=
  (p.map_eval (matrixIdentityTensor (A:=A)) (fun ij => matrixUnit ij.1 ij.2)).symm

/-- The full deterministic matrix-unit tuple converges jointly strongly,
with exact equality of every polynomial norm and normalized trace. -/
theorem tensorUnits_stronglyConverge [Nonempty K]
    (I : ℕ → Type) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)] :
    StronglyConverges (fun n => @matrixTrace (I n×K) _) matrixTrace
      (fun n (ij : K×K) => tensorUnit (I n) ij.1 ij.2)
      (fun ij : K×K => matrixUnit ij.1 ij.2) := by
  intro p
  simp only [eval_tensorUnits,matrixTrace_identity_tensor,norm_identity_kronecker]
  exact ⟨tendsto_const_nhds,tendsto_const_nhds⟩

end StrongConvergenceBlock
