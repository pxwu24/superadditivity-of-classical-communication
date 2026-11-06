import StrongConvergence.StrongConvergenceTensorPower
import StrongConvergence.StrongConvergenceHaarMoment

/-! Actual tensor moments of Haar-conjugated matrices at every finite order.
The averaging and commutation identities below follow from Haar invariance;
no asymptotic or representation-theoretic assertion is assumed. -/
open Matrix MeasureTheory
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma continuous_tensorPower_orbit_entry (m : ℕ) (P : Matrix E E ℂ)
    (i j : Fin m → E) :
    Continuous (fun U : Matrix.unitaryGroup E ℂ => tensorPower m (HaarMoment.orbit P U) i j) := by
  unfold tensorPower
  exact continuous_finset_prod _ fun l _ =>
    (HaarProjection.continuous_unitary_orbit P).matrix_elem (i l) (j l)

lemma integrable_tensorPower_orbit_entry (m : ℕ) (P : Matrix E E ℂ)
    (i j : Fin m → E) :
    Integrable (fun U : Matrix.unitaryGroup E ℂ => tensorPower m (HaarMoment.orbit P U) i j)
      HaarProjection.unitaryHaar :=
  (continuous_tensorPower_orbit_entry m P i j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The actual entrywise Haar integral of the m-th tensor power. -/
def tensorHaarMoment (m : ℕ) (P : Matrix E E ℂ) :
    Matrix (Fin m → E) (Fin m → E) ℂ :=
  fun i j => ∫ U : Matrix.unitaryGroup E ℂ,
    tensorPower m (HaarMoment.orbit P U) i j ∂HaarProjection.unitaryHaar

lemma tensorPower_orbit_mul (m : ℕ) (P : Matrix E E ℂ)
    (V U : Matrix.unitaryGroup E ℂ) :
    tensorPower m (HaarMoment.orbit P (V*U)) =
      tensorPower m (V : Matrix E E ℂ) * tensorPower m (HaarMoment.orbit P U) *
        (tensorPower m (V : Matrix E E ℂ)).conjTranspose := by
  have h : HaarMoment.orbit P (V*U) = (V : Matrix E E ℂ)*HaarMoment.orbit P U*
      (V : Matrix E E ℂ).conjTranspose := by
    simp only [HaarMoment.orbit,Matrix.UnitaryGroup.mul_val,Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
  rw [h,tensorPower_mul,tensorPower_mul,tensorPower_conjTranspose]

lemma tensorPower_unitary_left (m : ℕ) (U : Matrix.unitaryGroup E ℂ) :
    (tensorPower m (U : Matrix E E ℂ)).conjTranspose *
      tensorPower m (U : Matrix E E ℂ) = 1 := by
  have hU : (U : Matrix E E ℂ).conjTranspose * (U : Matrix E E ℂ) = 1 := U.prop.1
  rw [← tensorPower_conjTranspose,← tensorPower_mul,hU,tensorPower_one]

lemma tensorPower_unitary_right (m : ℕ) (U : Matrix.unitaryGroup E ℂ) :
    tensorPower m (U : Matrix E E ℂ) *
      (tensorPower m (U : Matrix E E ℂ)).conjTranspose = 1 := by
  have hU : (U : Matrix E E ℂ) * (U : Matrix E E ℂ).conjTranspose = 1 := U.prop.2
  rw [← tensorPower_conjTranspose,← tensorPower_mul,hU,tensorPower_one]

/-- Conjugating a Haar tensor moment by a fixed tensor unitary leaves it unchanged. -/
theorem tensorHaarMoment_conjugate_invariant (m : ℕ) (P : Matrix E E ℂ)
    (V : Matrix.unitaryGroup E ℂ) :
    tensorPower m (V : Matrix E E ℂ) * tensorHaarMoment m P *
      (tensorPower m (V : Matrix E E ℂ)).conjTranspose = tensorHaarMoment m P := by
  ext i j
  have hinv := integral_mul_left_eq_self (μ := HaarProjection.unitaryHaar)
    (fun U : Matrix.unitaryGroup E ℂ => tensorPower m (HaarMoment.orbit P U) i j) V
  change (tensorPower m (V : Matrix E E ℂ) * tensorHaarMoment m P *
      (tensorPower m (V : Matrix E E ℂ)).conjTranspose) i j =
    ∫ U : Matrix.unitaryGroup E ℂ,
      tensorPower m (HaarMoment.orbit P U) i j ∂HaarProjection.unitaryHaar
  rw [← hinv]
  simp_rw [tensorPower_orbit_mul,Matrix.mul_apply,Finset.sum_mul]
  rw [integral_finset_sum _ (fun x _ => integrable_finset_sum _ (fun y _ =>
    ((integrable_tensorPower_orbit_entry m P y x).const_mul _).mul_const _))]
  simp_rw [integral_finset_sum _ (fun y _ =>
    ((integrable_tensorPower_orbit_entry m P y _).const_mul _).mul_const _),
    integral_mul_const,integral_const_mul]
  rfl

/-- At every finite order, the actual Haar moment lies in the tensor-unitary commutant. -/
theorem tensorHaarMoment_commutes (m : ℕ) (P : Matrix E E ℂ)
    (V : Matrix.unitaryGroup E ℂ) :
    tensorHaarMoment m P * tensorPower m (V : Matrix E E ℂ) =
      tensorPower m (V : Matrix E E ℂ) * tensorHaarMoment m P := by
  have h := congrArg (fun X => X * tensorPower m (V : Matrix E E ℂ))
    (tensorHaarMoment_conjugate_invariant m P V)
  simpa only [Matrix.mul_assoc,tensorPower_unitary_left,Matrix.mul_one] using h.symm

#print axioms tensorHaarMoment_conjugate_invariant
#print axioms tensorHaarMoment_commutes

end ProjectionChannels.TensorHaar
