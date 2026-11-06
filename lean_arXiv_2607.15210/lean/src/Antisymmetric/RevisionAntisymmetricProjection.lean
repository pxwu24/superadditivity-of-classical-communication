import Antisymmetric.RevisionAntisymmetricShuffling

/-! The signed permutation average is an actual orthogonal projection matrix. -/
noncomputable section
open Finset Equiv
namespace AntisymmetricVerification
variable {k r : ℕ}

def antisymMatrix : Matrix (TensorIndex k r) (TensorIndex k r) ℂ :=
  fun x y => (r.factorial : ℂ)⁻¹ *
    ∑ σ : Perm (Fin r), signC σ * if x ∘ σ = y then 1 else 0

lemma antisymMatrix_mulVec (f : TensorVector k r) :
    (antisymMatrix (k := k) (r := r)).mulVec f = antisymmetrize f := by
  ext x
  simp only [Matrix.mulVec, dotProduct, antisymMatrix, antisymmetrize, permute]
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  simp [ite_mul]

lemma signC_symm (σ : Perm (Fin r)) : signC σ.symm = signC σ := by
  simp [signC]

lemma permute_eq_iff (x y : TensorIndex k r) (σ : Perm (Fin r)) :
    y ∘ σ.symm = x ↔ x ∘ σ = y := by
  constructor
  · intro h
    rw [← h]
    ext j
    simp [Function.comp_def]
  · intro h
    rw [← h]
    ext j
    simp [Function.comp_def]

/-- Hermiticity is checked from the actual permutation sum. -/
theorem antisymMatrix_isHermitian : (antisymMatrix (k := k) (r := r)).IsHermitian := by
  classical
  ext x y
  simp only [Matrix.conjTranspose_apply, antisymMatrix, star_mul, star_inv₀,
    star_natCast, star_sum, signC, star_intCast]
  have hsum := Equiv.sum_comp (Equiv.inv (Perm (Fin r)))
    (fun σ : Perm (Fin r) => ((Perm.sign σ : ℤ) : ℂ) * star (if y ∘ σ = x then (1 : ℂ) else 0))
  conv_lhs => rw [mul_comm]
  congr 1
  calc
    (∑ σ : Perm (Fin r), star (if y ∘ σ = x then (1 : ℂ) else 0) * ((Perm.sign σ : ℤ) : ℂ)) =
        ∑ σ : Perm (Fin r), ((Perm.sign σ : ℤ) : ℂ) * star (if y ∘ σ = x then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ = _ := by
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro σ hσ
      simp only [Equiv.inv_apply, Perm.sign_inv]
      change ((Perm.sign σ : ℤ) : ℂ) * star (if y ∘ σ.symm = x then (1 : ℂ) else 0) = _
      simp only [permute_eq_iff]
      split_ifs <;> simp

/-- Idempotence as a genuine finite matrix identity. -/
theorem antisymMatrix_idempotent :
    (antisymMatrix (k := k) (r := r)) * antisymMatrix = antisymMatrix := by
  classical
  apply Matrix.ext_of_mulVec_single
  intro y
  rw [← Matrix.mulVec_mulVec, antisymMatrix_mulVec, antisymMatrix_mulVec,
    antisymmetrize_idempotent]

end AntisymmetricVerification
