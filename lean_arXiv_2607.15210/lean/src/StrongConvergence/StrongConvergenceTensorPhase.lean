import StrongConvergence.StrongConvergenceTensorPower
import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Polynomial.Roots

open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Number of occurrences of one index in a tensor coordinate. -/
def tupleCount {m : ℕ} (i : Fin m → E) (e : E) : ℕ :=
  (Finset.univ.filter (fun l => i l = e)).card

lemma unit_norm_infinite : Set.Infinite {z : ℂ | ‖z‖ = 1} := by
  apply Set.Infinite.of_image Complex.re
  apply Real.range_cos_infinite.mono
  rintro x ⟨r, rfl⟩
  refine ⟨(Real.cos r : ℂ) + Real.sin r * Complex.I, ?_, ?_⟩
  · change ‖(Real.cos r : ℂ) + Real.sin r * Complex.I‖ = 1
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    exact Complex.norm_cos_add_sin_mul_I r
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

lemma diagonal_mem_unitary (a : E → ℂ) (ha : ∀ e, ‖a e‖ = 1) :
    Matrix.diagonal a ∈ Matrix.unitaryGroup E ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  have hi : a i * star (a i) = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, ha i, one_pow,
      Complex.ofReal_one] using (Complex.mul_conj (a i))
  by_cases h : i = j
  · subst j
    simpa using hi
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

lemma tuple_phase_product {m : ℕ} (i : Fin m → E) (e : E) (z : ℂ) :
    (∏ l, if i l = e then z else 1) = z ^ tupleCount i e := by
  rw [← Finset.prod_filter]
  simp [tupleCount]

/-- Commutation with unitary tensor powers forces conservation of every
coordinate multiplicity at every nonzero matrix entry. -/
theorem tupleCount_eq_of_commutes_unitary {m : ℕ}
    (T : Matrix (Fin m → E) (Fin m → E) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup E ℂ,
      T * tensorPower m (U : Matrix E E ℂ) = tensorPower m (U : Matrix E E ℂ) * T)
    {i j : Fin m → E} (hij : T i j ≠ 0) (e : E) :
    tupleCount i e = tupleCount j e := by
  have hpow (z : ℂ) (hz : ‖z‖ = 1) : z ^ tupleCount i e = z ^ tupleCount j e := by
    let a : E → ℂ := fun x => if x = e then z else 1
    have ha : ∀ x, ‖a x‖ = 1 := by
      intro x
      simp only [a]
      split_ifs <;> simp_all
    let U : Matrix.unitaryGroup E ℂ := ⟨Matrix.diagonal a, diagonal_mem_unitary a ha⟩
    have h := congrFun (congrFun (hT U) i) j
    change (T * tensorPower m (Matrix.diagonal a)) i j =
      (tensorPower m (Matrix.diagonal a) * T) i j at h
    rw [tensorPower_diagonal] at h
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, a, tuple_phase_product] at h
    exact (mul_left_cancel₀ hij (by simpa [mul_comm] using h)).symm
  have hp : (Polynomial.X : Polynomial ℂ) ^ tupleCount i e =
      Polynomial.X ^ tupleCount j e := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply unit_norm_infinite.mono
    intro z hz
    simpa using hpow z hz
  have hd := congrArg Polynomial.natDegree hp
  simpa using hd

lemma prod_eq_of_tupleCount_eq {m : ℕ} {i j : Fin m → E}
    (hij : ∀ e, tupleCount i e = tupleCount j e) (a : E → ℂ) :
    (∏ l, a (i l)) = ∏ l, a (j l) := by
  rw [← Finset.prod_fiberwise' Finset.univ i a,
    ← Finset.prod_fiberwise' Finset.univ j a]
  apply Finset.prod_congr rfl
  intro e _
  simp only [Finset.prod_const]
  exact congrArg (fun n => a e ^ n) (hij e)

/-- Unitary tensor commutation extends to all diagonal complex matrices. -/
theorem commutes_tensorPower_diagonal {m : ℕ}
    (T : Matrix (Fin m → E) (Fin m → E) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup E ℂ,
      T * tensorPower m (U : Matrix E E ℂ) = tensorPower m (U : Matrix E E ℂ) * T)
    (a : E → ℂ) :
    T * tensorPower m (Matrix.diagonal a) = tensorPower m (Matrix.diagonal a) * T := by
  rw [tensorPower_diagonal]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : T i j = 0
  · simp [hij]
  · rw [prod_eq_of_tupleCount_eq (tupleCount_eq_of_commutes_unitary T hT hij) a]
    exact mul_comm _ _

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.tupleCount_eq_of_commutes_unitary
#print axioms ProjectionChannels.TensorHaar.commutes_tensorPower_diagonal
