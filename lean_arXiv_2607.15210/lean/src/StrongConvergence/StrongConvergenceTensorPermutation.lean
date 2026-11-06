import StrongConvergence.StrongConvergenceTensorSpanning

open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

lemma tuple_permute_eq_iff (σ : Equiv.Perm (Fin m)) (i j : Fin m → E) :
    i = (fun l => j (σ l)) ↔ (fun l => i (σ.symm l)) = j := by
  constructor
  · intro h
    funext l
    simpa using congrFun h (σ.symm l)
  · intro h
    funext l
    simpa using congrFun h (σ l)

lemma permutationTensor_mul_apply (σ : Equiv.Perm (Fin m))
    (T : Matrix (Fin m → E) (Fin m → E) ℂ) (i j : Fin m → E) :
    (permutationTensor (E := E) σ * T) i j = T (fun l => i (σ.symm l)) j := by
  simp only [Matrix.mul_apply, permutationTensor, tuple_permute_eq_iff,
    ite_mul, one_mul, zero_mul]
  simp

lemma mul_permutationTensor_apply (σ : Equiv.Perm (Fin m))
    (T : Matrix (Fin m → E) (Fin m → E) ℂ) (i j : Fin m → E) :
    (T * permutationTensor (E := E) σ) i j = T i (fun l => j (σ l)) := by
  simp [Matrix.mul_apply, permutationTensor]

@[simp] lemma permutationTensor_one :
    permutationTensor (E := E) (1 : Equiv.Perm (Fin m)) = 1 := by
  ext i j
  simp [permutationTensor, Matrix.one_apply]

/-- This coordinate convention is an anti-representation. -/
lemma permutationTensor_mul (σ τ : Equiv.Perm (Fin m)) :
    permutationTensor (E := E) σ * permutationTensor τ = permutationTensor (τ * σ) := by
  ext i j
  rw [mul_permutationTensor_apply]
  rfl

lemma permutationTensor_conjTranspose (σ : Equiv.Perm (Fin m)) :
    (permutationTensor (E := E) σ).conjTranspose = permutationTensor σ.symm := by
  ext i j
  simp only [Matrix.conjTranspose_apply, permutationTensor]
  simp only [tuple_permute_eq_iff σ j i, eq_comm]
  split_ifs <;> simp

lemma permutationTensor_mem_unitary (σ : Equiv.Perm (Fin m)) :
    permutationTensor (E := E) σ ∈ Matrix.unitaryGroup (Fin m → E) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, permutationTensor_conjTranspose, permutationTensor_mul]
  simpa using (permutationTensor_one (E := E) (m := m))

/-- Permuting tensor positions commutes with every identical-factor tensor power. -/
theorem permutationTensor_commutes_tensorPower (σ : Equiv.Perm (Fin m))
    (A : Matrix E E ℂ) :
    permutationTensor (E := E) σ * tensorPower m A =
      tensorPower m A * permutationTensor σ := by
  ext i j
  rw [permutationTensor_mul_apply, mul_permutationTensor_apply]
  simp only [tensorPower]
  simpa using (Equiv.prod_comp σ (fun l => A (i (σ.symm l)) (j l))).symm

lemma permutationTensor_trace (σ : Equiv.Perm (Fin m)) :
    Matrix.trace (permutationTensor (E := E) σ) =
      ((Finset.univ.filter (fun i : Fin m → E => i = fun l => i (σ l))).card : ℂ) := by
  simp [Matrix.trace, Matrix.diag, permutationTensor]

lemma permutationTensor_gram (σ τ : Equiv.Perm (Fin m)) :
    Matrix.trace (permutationTensor (E := E) σ * (permutationTensor τ).conjTranspose) =
      Matrix.trace (permutationTensor (E := E) (τ.symm * σ)) := by
  rw [permutationTensor_conjTranspose, permutationTensor_mul]

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.permutationTensor_commutes_tensorPower
#print axioms ProjectionChannels.TensorHaar.permutationTensor_gram
