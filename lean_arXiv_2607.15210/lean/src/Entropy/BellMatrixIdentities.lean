import Entropy.Defs

/-! Finite Choi-block contractions used by the Bell-limit theorem. `bellEntry`
is the coefficient formula obtained by applying a map and its conjugate to the
normalized Bell input. The channel/complete-positivity framework is not defined
here; the identities themselves hold for every Hermitian Choi array. -/

open Finset
noncomputable section
namespace BellLimitVerification

variable {A B : Type*} [Fintype A] [Fintype B]

def choiBlock (J : Matrix (A × B) (A × B) ℂ) (i j : B) : Matrix A A ℂ :=
  fun a b => J (a,i) (b,j)

def bellEntry (J : Matrix (A × B) (A × B) ℂ) (i p j q : B) : ℂ :=
  (1 / (Fintype.card A : ℂ)) *
    ∑ a, ∑ b, J (a,i) (b,j) * star (J (a,p) (b,q))

/-- Equation (Z-block-entry), under explicit entrywise Hermiticity. -/
theorem bellEntry_eq_block_trace (J : Matrix (A × B) (A × B) ℂ)
    (hJ : ∀ x y, star (J x y) = J y x) (i p j q : B) :
    bellEntry J i p j q =
      (1 / (Fintype.card A : ℂ)) * Matrix.trace (choiBlock J i j * choiBlock J q p) := by
  unfold bellEntry Matrix.trace Matrix.diag
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [choiBlock, hJ]

/-- Sum of block purities is the full Choi purity. -/
theorem sum_block_trace_eq_trace_square (J : Matrix (A × B) (A × B) ℂ) :
    (∑ i, ∑ j, Matrix.trace (choiBlock J i j * choiBlock J j i)) =
      Matrix.trace (J * J) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, choiBlock, Fintype.sum_prod_type]
  calc
    (∑ i : B, ∑ j : B, ∑ a : A, ∑ b : A, J (a,i) (b,j) * J (b,j) (a,i)) =
        ∑ i : B, ∑ a : A, ∑ j : B, ∑ b : A, J (a,i) (b,j) * J (b,j) (a,i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ a : A, ∑ i : B, ∑ j : B, ∑ b : A, J (a,i) (b,j) * J (b,j) (a,i) := by
      rw [Finset.sum_comm]
    _ = ∑ a : A, ∑ i : B, ∑ b : A, ∑ j : B, J (a,i) (b,j) * J (b,j) (a,i) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]

/-- Bell overlap contraction equals Choi purity divided by input and output
 dimensions, as in equation (bell-overlap-purity). -/
theorem bell_overlap_eq_normalized_purity (J : Matrix (A × B) (A × B) ℂ)
    (hJ : ∀ x y, star (J x y) = J y x) :
    (1 / (Fintype.card B : ℂ)) * (∑ i, ∑ j, bellEntry J i i j j) =
      Matrix.trace (J * J) / ((Fintype.card A : ℂ) * (Fintype.card B : ℂ)) := by
  simp_rw [bellEntry_eq_block_trace J hJ, ← Finset.mul_sum]
  rw [sum_block_trace_eq_trace_square]
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
  ring

#print axioms bellEntry_eq_block_trace
#print axioms sum_block_trace_eq_trace_square
#print axioms bell_overlap_eq_normalized_purity
end BellLimitVerification
