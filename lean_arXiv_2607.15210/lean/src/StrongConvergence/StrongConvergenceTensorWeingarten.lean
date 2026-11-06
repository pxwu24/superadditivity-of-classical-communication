import StrongConvergence.StrongConvergenceTensorComplexification
import StrongConvergence.StrongConvergenceTensorHaarIntegral
import StrongConvergence.StrongConvergenceTensorHaarTrace
import StrongConvergence.StrongConvergenceTensorGram
import StrongConvergence.StrongConvergenceTensorProjection

/-! An all-order finite Haar integration formula.  Its inverse Gram coefficients
are derived from unitary invariance and an elementary proof of invariant-tensor
spanning.  No integration, moment-limit, or freeness formula is assumed. -/

open Matrix MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

/-- Elementary unitary invariant-tensor spanning in the stable dimension
range: commutation with the unitary group alone forces permutation spanning. -/
theorem eq_sum_permutationTensor_of_unitary_commutes
    (e : Fin m ↪ E) (T : Matrix (Fin m → E) (Fin m → E) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup E ℂ,
      T * tensorPower m (U : Matrix E E ℂ) = tensorPower m (U : Matrix E E ℂ) * T) :
    T = ∑ σ : Equiv.Perm (Fin m),
      T (fun l => e (σ l)) e • permutationTensor (E := E) σ :=
  eq_sum_permutationTensor_of_commutes e T (commutes_tensorPower_of_unitary m T hT)

/-- Every finite tensor moment of an actual Haar orbit belongs to the span of
the permutation tensors, with its uniquely determined inverse Gram coefficients.
The stable dimension range is expressed by `e : Fin m ↪ E`. -/
theorem tensorHaarMoment_eq_invGram
    (e : Fin m ↪ E) (P : Matrix E E ℂ) :
    tensorHaarMoment m P = ∑ σ : Equiv.Perm (Fin m),
      ((permutationGram E m)⁻¹ *ᵥ permutationContractions (tensorHaarMoment m P)) σ •
        permutationTensor (E := E) σ := by
  apply eq_sum_permutationTensor_invGram_of_commutes e
  exact commutes_tensorPower_of_unitary m _ (tensorHaarMoment_commutes m P)

lemma permutationContractions_tensorHaarMoment (P : Matrix E E ℂ) :
    permutationContractions (tensorHaarMoment m P) =
      permutationContractions (tensorPower m P) := by
  funext σ
  exact permutation_trace_tensorHaarMoment P σ

/-- The exact finite Haar integration formula at arbitrary tensor order, with
every coefficient computed from the original matrix and the finite permutation
Gram inverse.  The right side contains no Haar integral. -/
theorem tensorHaarMoment_weingarten (e : Fin m ↪ E) (P : Matrix E E ℂ) :
    tensorHaarMoment m P = ∑ σ : Equiv.Perm (Fin m),
      ((permutationGram E m)⁻¹ *ᵥ permutationContractions (tensorPower m P)) σ •
        permutationTensor (E := E) σ := by
  rw [← permutationContractions_tensorHaarMoment]
  exact tensorHaarMoment_eq_invGram e P

/-- Entrywise form: a product of arbitrarily many entries of a Haar conjugate
is evaluated by a completely deterministic finite permutation sum. -/
theorem integral_orbit_entry_product (e : Fin m ↪ E) (P : Matrix E E ℂ)
    (i j : Fin m → E) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (∏ l, HaarMoment.orbit P U (i l) (j l)) ∂HaarProjection.unitaryHaar) =
      ∑ σ : Equiv.Perm (Fin m),
        ((permutationGram E m)⁻¹ *ᵥ permutationContractions (tensorPower m P)) σ *
          (if i = (fun l => j (σ l)) then 1 else 0) := by
  have h := congrFun (congrFun (tensorHaarMoment_weingarten e P) i) j
  simpa only [tensorHaarMoment, tensorPower, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, permutationTensor] using h

/-- Rank-dependent coefficients of every Haar projection moment. -/
def projectionMomentCoefficients (E : Type*) [Fintype E] [DecidableEq E]
    (m d : ℕ) : Equiv.Perm (Fin m) → ℂ :=
  (permutationGram E m)⁻¹ *ᵥ
    (fun σ : Equiv.Perm (Fin m) => (d : ℂ) ^ cycleCount σ.symm)

/-- Every order of the finite Haar projection law is computed solely from its
rank and ambient dimension.  The Gram entries are `N ^ cycleCount (τ * σ⁻¹)`.
No random-matrix limit theorem is an input. -/
theorem tensorHaarMoment_projection (e : Fin m ↪ E) {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hp : P * P = P) :
    tensorHaarMoment m P = ∑ σ : Equiv.Perm (Fin m),
      projectionMomentCoefficients E m P.rank σ • permutationTensor (E := E) σ := by
  rw [tensorHaarMoment_weingarten e P,
    permutationContractions_tensorPower_projection hP hp]
  rfl

theorem integral_projection_entry_product (e : Fin m ↪ E) {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hp : P * P = P) (i j : Fin m → E) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (∏ l, HaarMoment.orbit P U (i l) (j l)) ∂HaarProjection.unitaryHaar) =
      ∑ σ : Equiv.Perm (Fin m), projectionMomentCoefficients E m P.rank σ *
        (if i = (fun l => j (σ l)) then 1 else 0) := by
  rw [integral_orbit_entry_product e P,
    permutationContractions_tensorPower_projection hP hp]
  rfl

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.tensorHaarMoment_eq_invGram
#print axioms ProjectionChannels.TensorHaar.eq_sum_permutationTensor_of_unitary_commutes
#print axioms ProjectionChannels.TensorHaar.tensorHaarMoment_weingarten
#print axioms ProjectionChannels.TensorHaar.integral_orbit_entry_product
#print axioms ProjectionChannels.TensorHaar.tensorHaarMoment_projection
#print axioms ProjectionChannels.TensorHaar.integral_projection_entry_product
