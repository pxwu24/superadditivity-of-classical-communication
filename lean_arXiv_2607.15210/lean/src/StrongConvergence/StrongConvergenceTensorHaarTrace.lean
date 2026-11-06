import StrongConvergence.StrongConvergenceTensorHaarIntegral
import StrongConvergence.StrongConvergenceTensorPermutation

/-! Exact trace contractions of actual Haar tensor moments. -/
open Matrix MeasureTheory
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

lemma trace_mul_tensorHaarMoment (P : Matrix E E ℂ)
    (C : Matrix (Fin m → E) (Fin m → E) ℂ) :
    Matrix.trace (C * tensorHaarMoment m P) =
      ∫ U : Matrix.unitaryGroup E ℂ,
        Matrix.trace (C * tensorPower m (HaarMoment.orbit P U))
          ∂HaarProjection.unitaryHaar := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    (integrable_tensorPower_orbit_entry m P j i).const_mul _))]
  simp_rw [integral_finset_sum _ (fun j _ =>
    (integrable_tensorPower_orbit_entry m P j _).const_mul _),integral_const_mul]
  rfl

lemma tensorPower_orbit (P : Matrix E E ℂ) (U : Matrix.unitaryGroup E ℂ) :
    tensorPower m (HaarMoment.orbit P U) =
      tensorPower m (U : Matrix E E ℂ) * tensorPower m P *
        (tensorPower m (U : Matrix E E ℂ)).conjTranspose := by
  rw [HaarMoment.orbit,tensorPower_mul,tensorPower_mul,tensorPower_conjTranspose]

/-- An invariant contraction has its original value after actual Haar averaging. -/
theorem trace_mul_tensorHaarMoment_eq (P : Matrix E E ℂ)
    (C : Matrix (Fin m → E) (Fin m → E) ℂ)
    (hC : ∀ U : Matrix.unitaryGroup E ℂ,
      C * tensorPower m (U : Matrix E E ℂ) = tensorPower m (U : Matrix E E ℂ) * C) :
    Matrix.trace (C * tensorHaarMoment m P) = Matrix.trace (C * tensorPower m P) := by
  rw [trace_mul_tensorHaarMoment]
  have heach (U : Matrix.unitaryGroup E ℂ) :
      Matrix.trace (C * tensorPower m (HaarMoment.orbit P U)) =
        Matrix.trace (C * tensorPower m P) := by
    rw [tensorPower_orbit]
    calc
      _ = Matrix.trace (tensorPower m (U : Matrix E E ℂ) *
          (C * tensorPower m P) * (tensorPower m (U : Matrix E E ℂ)).conjTranspose) := by
        congr 1
        simp only [← Matrix.mul_assoc]
        rw [hC U]
      _ = _ := by rw [Matrix.trace_mul_cycle,tensorPower_unitary_left,Matrix.one_mul]
  simp_rw [heach]
  simp

/-- The permutation contractions required by inverse-Gram Haar integration. -/
theorem permutation_trace_tensorHaarMoment (P : Matrix E E ℂ)
    (σ : Equiv.Perm (Fin m)) :
    Matrix.trace ((permutationTensor (E := E) σ).conjTranspose * tensorHaarMoment m P) =
      Matrix.trace ((permutationTensor (E := E) σ).conjTranspose * tensorPower m P) := by
  apply trace_mul_tensorHaarMoment_eq
  intro U
  rw [permutationTensor_conjTranspose]
  exact permutationTensor_commutes_tensorPower σ.symm (U : Matrix E E ℂ)

#print axioms permutation_trace_tensorHaarMoment

end ProjectionChannels.TensorHaar
