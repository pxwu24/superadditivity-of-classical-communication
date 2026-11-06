import Antisymmetric.RevisionAntisymmetricLegMatrix

/-! First-leg swaps in tensor coordinates and their matrix-unit expansion. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

def swapFirstIndex (j : Fin r) (x : Fin k × TensorIndex k r) : Fin k × TensorIndex k r :=
  (x.2 j, Function.update x.2 j x.1)

def swapFirstMatrix (j : Fin r) :
    Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ :=
  fun x y => if swapFirstIndex j x = y then 1 else 0

lemma swapFirstIndex_involutive (j : Fin r) : Function.Involutive (swapFirstIndex (k := k) j) := by
  intro x
  rcases x with ⟨a,x⟩
  simp [swapFirstIndex, Function.update_idem]

lemma swapFirstMatrix_mulVec (j : Fin r) (f : (Fin k × TensorIndex k r) → ℂ) :
    (swapFirstMatrix j).mulVec f = fun x => f (swapFirstIndex j x) := by
  ext x
  simp [Matrix.mulVec, dotProduct, swapFirstMatrix, ite_mul]

lemma swapFirstIndex_cons (j : Fin r) (x : Fin k × TensorIndex k r) :
    firstTensorEquiv (swapFirstIndex j x) =
      firstTensorEquiv x ∘ Equiv.swap 0 j.succ := by
  ext l
  refine Fin.cases ?_ (fun l => ?_) l
  · simp [firstTensorEquiv, Fin.consEquiv, swapFirstIndex]
  · by_cases h : l = j
    · subst l
      simp [firstTensorEquiv, Fin.consEquiv, swapFirstIndex]
    · have hne : l.succ ≠ j.succ := by simpa using h
      simp [firstTensorEquiv, Fin.consEquiv, swapFirstIndex, h, hne,
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero l) hne]

lemma oneLegMatrix_matrixUnit_apply (a b : Fin k) (j : Fin r) (x y : TensorIndex k r) :
    oneLegMatrix (matrixUnit a b) j x y =
      if x j = a then (if Function.update x j b = y then 1 else 0) else 0 := by
  rw [oneLegMatrix, LinearMap.toMatrix'_apply]
  change (∑ c, matrixUnit a b (x j) c *
    (if Function.update x j c = y then (1 : ℂ) else 0)) = _
  by_cases ha : x j = a
  · rw [Finset.sum_eq_single b]
    · simp [matrixUnit, ha]
    · intro c hc hcb
      simp [matrixUnit, hcb]
    · simp
  · simp [matrixUnit, ha]

/-- A physical first-leg swap is the sum of matrix units on the two selected
 tensor legs. -/
theorem swapFirstMatrix_matrixUnits (j : Fin r) :
    swapFirstMatrix (k := k) j = ∑ a : Fin k, ∑ b : Fin k,
      Matrix.kronecker (matrixUnit a b) (oneLegMatrix (matrixUnit b a) j) := by
  ext ⟨a,x⟩ ⟨b,y⟩
  simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, matrixUnit,
    ite_mul, one_mul, zero_mul]
  simp only [ite_and]
  rw [Finset.sum_eq_single a]
  · simp only [if_pos rfl]
    rw [Finset.sum_eq_single b]
    · simp only [if_pos rfl]
      rw [oneLegMatrix_matrixUnit_apply]
      simp only [swapFirstMatrix, swapFirstIndex, Prod.mk.injEq, ite_and, ite_true]
    · intro c hc hcb
      simp [Ne.symm hcb]
    · simp
  · intro c hc hca
    simp [Ne.symm hca]
  · simp

end AntisymmetricVerification
