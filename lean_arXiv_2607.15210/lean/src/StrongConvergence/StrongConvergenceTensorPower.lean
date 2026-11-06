import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Algebra.BigOperators.Ring.Finset

open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Concrete tensor power in the tensor product coordinate basis. -/
def tensorPower (m : ℕ) (M : Matrix E E ℂ) :
    Matrix (Fin m → E) (Fin m → E) ℂ :=
  fun i j => ∏ l, M (i l) (j l)

lemma tensorPower_mul (m : ℕ) (A B : Matrix E E ℂ) :
    tensorPower m (A * B) = tensorPower m A * tensorPower m B := by
  ext i j
  simp only [tensorPower, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]

lemma tensorPower_diagonal (m : ℕ) (a : E → ℂ) :
    tensorPower m (Matrix.diagonal a) =
      Matrix.diagonal (fun i : Fin m → E => ∏ l, a (i l)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [tensorPower]
  · have hne : ∃ l, i l ≠ j l := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨l, hl⟩ := hne
    simp only [tensorPower, Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (Matrix.diagonal_apply_ne a hl)

@[simp] lemma tensorPower_one (m : ℕ) :
    tensorPower m (1 : Matrix E E ℂ) = 1 := by
  rw [← Matrix.diagonal_one, tensorPower_diagonal]
  simp

lemma tensorPower_conjTranspose (m : ℕ) (A : Matrix E E ℂ) :
    tensorPower m A.conjTranspose = (tensorPower m A).conjTranspose := by
  ext i j
  simp [tensorPower, Matrix.conjTranspose_apply, map_prod]

lemma tensorPower_smul (m : ℕ) (z : ℂ) (A : Matrix E E ℂ) :
    tensorPower m (z • A) = z ^ m • tensorPower m A := by
  ext i j
  simp [tensorPower, Finset.prod_mul_distrib]

lemma tensorPower_trace (m : ℕ) (A : Matrix E E ℂ) :
    Matrix.trace (tensorPower m A) = Matrix.trace A ^ m := by
  simp only [Matrix.trace, Matrix.diag, tensorPower]
  exact (Fintype.sum_pow (fun i => A i i) m).symm

lemma tensorPower_mem_unitary (m : ℕ) (U : Matrix.unitaryGroup E ℂ) :
    tensorPower m (U : Matrix E E ℂ) ∈ Matrix.unitaryGroup (Fin m → E) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, ← tensorPower_conjTranspose, ← tensorPower_mul]
  have h := Matrix.mem_unitaryGroup_iff.mp U.property
  rw [Matrix.star_eq_conjTranspose] at h
  rw [h, tensorPower_one]

/-- Tensor power of an actual finite-dimensional unitary. -/
def tensorUnitary (m : ℕ) (U : Matrix.unitaryGroup E ℂ) :
    Matrix.unitaryGroup (Fin m → E) ℂ :=
  ⟨tensorPower m (U : Matrix E E ℂ), tensorPower_mem_unitary m U⟩

lemma continuous_tensorPower (m : ℕ) :
    Continuous (tensorPower (E := E) m) := by
  unfold tensorPower
  fun_prop

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.tensorPower_mul
#print axioms ProjectionChannels.TensorHaar.tensorPower_mem_unitary
#print axioms ProjectionChannels.TensorHaar.tensorPower_trace
