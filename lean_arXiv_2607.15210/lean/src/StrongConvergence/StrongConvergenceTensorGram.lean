import StrongConvergence.StrongConvergenceTensorSpanning
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The finite permutation Gram matrix and its inverse.  In the stable range
`m ≤ dim`, positivity is proved by evaluating a linear combination at tuples
of distinct coordinates.  This provides the finite matrix inverse needed by
unitary Haar integration, without assuming a Weingarten formula. -/

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

def permutationColumns (E : Type*) [Fintype E] [DecidableEq E] (m : ℕ) :
    Matrix ((Fin m → E) × (Fin m → E)) (Equiv.Perm (Fin m)) ℂ :=
  fun ij σ => permutationTensor σ ij.1 ij.2

def permutationGram (E : Type*) [Fintype E] [DecidableEq E] (m : ℕ) :
    Matrix (Equiv.Perm (Fin m)) (Equiv.Perm (Fin m)) ℂ :=
  (permutationColumns E m).conjTranspose * permutationColumns E m

lemma permutationTensor_embedding (e : Fin m ↪ E) (σ τ : Equiv.Perm (Fin m)) :
    permutationTensor σ (fun l => e (τ l)) e = if τ = σ then 1 else 0 := by
  simp only [permutationTensor, (tuple_permutation_injective e).eq_iff]

lemma permutationColumns_mulVec_embedding (e : Fin m ↪ E)
    (c : Equiv.Perm (Fin m) → ℂ) (σ : Equiv.Perm (Fin m)) :
    (permutationColumns E m *ᵥ c) ((fun l => e (σ l)), e) = c σ := by
  classical
  simp [Matrix.mulVec, dotProduct, permutationColumns, permutationTensor_embedding]

lemma permutationColumns_mulVec_injective (e : Fin m ↪ E) :
    Function.Injective (permutationColumns E m).mulVec := by
  intro c d h
  funext σ
  have hh := congrFun h ((fun l => e (σ l)), e)
  simpa only [permutationColumns_mulVec_embedding] using hh

/-- The permutation Gram matrix is nonsingular whenever the coordinate
dimension is at least the tensor degree. -/
theorem permutationGram_posDef (e : Fin m ↪ E) : (permutationGram E m).PosDef := by
  have h := (Matrix.PosDef.one (n := (Fin m → E) × (Fin m → E)) (R := ℂ)).conjTranspose_mul_mul_same
    (permutationColumns_mulVec_injective e)
  simpa [permutationGram] using h

theorem permutationGram_isUnit (e : Fin m ↪ E) : IsUnit (permutationGram E m) :=
  (permutationGram_posDef e).isUnit

lemma permutationGram_apply (σ τ : Equiv.Perm (Fin m)) :
    permutationGram E m σ τ =
      Matrix.trace ((permutationTensor (E := E) σ).conjTranspose *
        permutationTensor τ) := by
  classical
  simp only [permutationGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    permutationColumns, Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_comm

def permutationContractions (T : Matrix (Fin m → E) (Fin m → E) ℂ) :
    Equiv.Perm (Fin m) → ℂ :=
  fun σ => Matrix.trace ((permutationTensor (E := E) σ).conjTranspose * T)

lemma permutationContractions_sum (c : Equiv.Perm (Fin m) → ℂ) :
    permutationContractions (∑ τ, c τ • permutationTensor (E := E) τ) =
      permutationGram E m *ᵥ c := by
  classical
  funext σ
  simp only [permutationContractions, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Matrix.mulVec, dotProduct,
    permutationGram_apply]
  apply Finset.sum_congr rfl
  intro τ _
  exact mul_comm _ _

lemma coefficients_eq_invGram_contractions (e : Fin m ↪ E)
    (c : Equiv.Perm (Fin m) → ℂ) :
    c = (permutationGram E m)⁻¹ *ᵥ
      permutationContractions (∑ τ, c τ • permutationTensor (E := E) τ) := by
  rw [permutationContractions_sum, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (permutationGram_isUnit e)), Matrix.one_mulVec]

/-- Explicit inverse Gram coefficient formula for every invariant tensor in
the stable dimension range. -/
theorem eq_sum_permutationTensor_invGram_of_commutes
    (e : Fin m ↪ E) (T : Matrix (Fin m → E) (Fin m → E) ℂ)
    (hT : ∀ A : Matrix E E ℂ, T * tensorPower m A = tensorPower m A * T) :
    T = ∑ σ : Equiv.Perm (Fin m),
      ((permutationGram E m)⁻¹ *ᵥ permutationContractions T) σ •
        permutationTensor (E := E) σ := by
  classical
  let c : Equiv.Perm (Fin m) → ℂ := fun σ => T (fun l => e (σ l)) e
  have heq : T = ∑ σ, c σ • permutationTensor (E := E) σ :=
    eq_sum_permutationTensor_of_commutes e T hT
  have hc := coefficients_eq_invGram_contractions e c
  rw [← heq] at hc
  conv_lhs => rw [heq]
  rw [← hc]

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.permutationGram_posDef
#print axioms ProjectionChannels.TensorHaar.eq_sum_permutationTensor_invGram_of_commutes
