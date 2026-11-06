import Preliminaries.RevisionTensorChannels

/-! Exact functoriality of the finite matrix tensor product. -/

open Matrix PreliminariesMatrix ProjectionChannels
open scoped BigOperators
noncomputable section
namespace RevisionBell
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- The matrix-unit tensor formula is a complex-linear map on the input. -/
def tensorLinearMap (Φ Ψ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    Matrix (A×A) (A×A) ℂ →ₗ[ℂ] Matrix (B×B) (B×B) ℂ where
  toFun := tensorMap Φ Ψ
  map_add' X Y := by
    ext i j
    simp only [tensorMap,Matrix.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' z X := by
    ext i j
    simp only [tensorMap,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring

lemma linearMap_eq_of_matrixUnit
    (F G : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (h : ∀ a b, F (matrixUnit a b)=G (matrixUnit a b)) : F=G := by
  ext X i j
  rw [linearMap_entry_expansion,linearMap_entry_expansion]
  simp_rw [h]

lemma matrixUnit_prod (a b c d : A) :
    matrixUnit (a,c) (b,d)=Matrix.kronecker (matrixUnit a b) (matrixUnit c d) := by
  ext ⟨i,p⟩ ⟨j,q⟩
  by_cases hia : i=a <;> by_cases hjb : j=b <;>
    by_cases hpc : p=c <;> by_cases hqd : q=d <;>
    simp [matrixUnit,Matrix.kronecker,Matrix.kroneckerMap_apply,hia,hjb,hpc,hqd]

/-- Applying tensor products successively equals the tensor product of
the two composed maps, on every input matrix. -/
theorem tensorMap_comp
    (Φ Ψ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (E F : Matrix B B ℂ →ₗ[ℂ] Matrix C C ℂ)
    (X : Matrix (A×A) (A×A) ℂ) :
    tensorMap (E.comp Φ) (F.comp Ψ) X =
      tensorMap E F (tensorMap Φ Ψ X) := by
  have heq : tensorLinearMap (E.comp Φ) (F.comp Ψ)=
      (tensorLinearMap E F).comp (tensorLinearMap Φ Ψ) := by
    apply linearMap_eq_of_matrixUnit
    rintro ⟨a,c⟩ ⟨b,d⟩
    simp only [tensorLinearMap,LinearMap.comp_apply,LinearMap.coe_mk,AddHom.coe_mk,
      matrixUnit_prod,tensorMap_kronecker]
  exact congrArg (fun H : Matrix (A×A) (A×A) ℂ →ₗ[ℂ] Matrix (C×C) (C×C) ℂ => H X) heq

/-- Complex conjugation of maps respects composition. -/
theorem conjugateMap_comp
    (Φ : Matrix A A ℂ → Matrix B B ℂ) (E : Matrix B B ℂ → Matrix C C ℂ) :
    conjugateMap (E ∘ Φ)=(conjugateMap E) ∘ (conjugateMap Φ) := by
  funext X
  have hi (Y : Matrix B B ℂ) : entrywiseConjugate (entrywiseConjugate Y)=Y := by
    ext i j
    simp [entrywiseConjugate]
  simp only [conjugateMap,Function.comp_def,hi]

#print axioms tensorMap_comp
end RevisionBell
