import StrongConvergence.StrongConvergenceTensorPhase
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Polynomial complexification for concrete tensor powers. -/
open Matrix Polynomial
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma polynomial_eq_zero_of_eval_real (p : Polynomial ℂ)
    (h : ∀ x : ℝ, p.eval (x : ℂ) = 0) : p = 0 := by
  apply p.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro z ⟨x, rfl⟩
  exact h x

def tensorPowerPolynomial (m : ℕ) (B C : Matrix E E ℂ) :
    Matrix (Fin m → E) (Fin m → E) (Polynomial ℂ) :=
  fun i j => ∏ l, (Polynomial.C (B (i l) (j l)) +
    Polynomial.X * Polynomial.C (C (i l) (j l)))

lemma eval_tensorPowerPolynomial (m : ℕ) (B C : Matrix E E ℂ)
    (z : ℂ) (i j : Fin m → E) :
    (tensorPowerPolynomial m B C i j).eval z = tensorPower m (B + z • C) i j := by
  simp only [tensorPowerPolynomial, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    tensorPower, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

lemma commutes_tensorPower_complex_of_real (m : ℕ)
    (T : Matrix (Fin m → E) (Fin m → E) ℂ) (B C : Matrix E E ℂ)
    (h : ∀ x : ℝ, T * tensorPower m (B + (x : ℂ) • C) =
      tensorPower m (B + (x : ℂ) • C) * T) (z : ℂ) :
    T * tensorPower m (B + z • C) = tensorPower m (B + z • C) * T := by
  ext i j
  let p : Polynomial ℂ :=
    (∑ l, Polynomial.C (T i l) * tensorPowerPolynomial m B C l j) -
    ∑ l, tensorPowerPolynomial m B C i l * Polynomial.C (T l j)
  have heval (w : ℂ) : p.eval w =
      (T * tensorPower m (B + w • C)) i j -
      (tensorPower m (B + w • C) * T) i j := by
    simp [p, Matrix.mul_apply, Polynomial.eval_finset_sum, eval_tensorPowerPolynomial]
  have hp : p = 0 := polynomial_eq_zero_of_eval_real p (fun x => by
    rw [heval, h x, sub_self])
  have hz := heval z
  rw [hp, Polynomial.eval_zero] at hz
  exact sub_eq_zero.mp hz.symm

def hermitianRealPart (A : Matrix E E ℂ) : Matrix E E ℂ :=
  (1 / 2 : ℂ) • (A + A.conjTranspose)

def hermitianImagPart (A : Matrix E E ℂ) : Matrix E E ℂ :=
  (-Complex.I / 2 : ℂ) • (A - A.conjTranspose)

lemma hermitianRealPart_isHermitian (A : Matrix E E ℂ) :
    (hermitianRealPart A).IsHermitian := by
  unfold hermitianRealPart Matrix.IsHermitian
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]

lemma hermitianImagPart_isHermitian (A : Matrix E E ℂ) :
    (hermitianImagPart A).IsHermitian := by
  unfold hermitianImagPart Matrix.IsHermitian
  ext i j
  simp [Matrix.conjTranspose_apply, map_sub, _root_.map_div, map_neg]
  ring

lemma realPart_add_I_imagPart (A : Matrix E E ℂ) :
    hermitianRealPart A + Complex.I • hermitianImagPart A = A := by
  ext i j
  simp only [hermitianRealPart, hermitianImagPart, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  linear_combination (-(A i j - A.conjTranspose i j) / 2) * Complex.I_sq

/-- Commutation on Hermitian tensor powers determines commutation on all
complex tensor powers, by a polynomial identity on the real line. -/
theorem commutes_tensorPower_of_hermitian (m : ℕ)
    (T : Matrix (Fin m → E) (Fin m → E) ℂ)
    (h : ∀ H : Matrix E E ℂ, H.IsHermitian → T * tensorPower m H = tensorPower m H * T)
    (A : Matrix E E ℂ) : T * tensorPower m A = tensorPower m A * T := by
  have hh (x : ℝ) : (hermitianRealPart A + (x : ℂ) • hermitianImagPart A).IsHermitian := by
    apply (hermitianRealPart_isHermitian A).add
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (hermitianImagPart_isHermitian A).eq]
    simp
  have hc := commutes_tensorPower_complex_of_real m T (hermitianRealPart A)
    (hermitianImagPart A) (fun x => h _ (hh x)) Complex.I
  simpa only [realPart_add_I_imagPart] using hc

/-- Unitary tensor commutation extends to Hermitian matrices by the finite
spectral theorem and the diagonal multiplicity identity. -/
theorem commutes_tensorPower_hermitian_of_unitary (m : ℕ)
    (T : Matrix (Fin m → E) (Fin m → E) ℂ)
    (h : ∀ U : Matrix.unitaryGroup E ℂ,
      T * tensorPower m (U : Matrix E E ℂ) = tensorPower m (U : Matrix E E ℂ) * T)
    (H : Matrix E E ℂ) (hH : H.IsHermitian) :
    T * tensorPower m H = tensorPower m H * T := by
  have hU := h hH.eigenvectorUnitary
  have hV := h (star hH.eigenvectorUnitary)
  simp only [unitary.coe_star] at hV
  have hD := commutes_tensorPower_diagonal T h (fun e => (hH.eigenvalues e : ℂ))
  rw [hH.spectral_theorem]
  simp only [tensorPower_mul]
  change T * (tensorPower m (hH.eigenvectorUnitary : Matrix E E ℂ) *
    tensorPower m (Matrix.diagonal (fun e => (hH.eigenvalues e : ℂ))) *
    tensorPower m (star hH.eigenvectorUnitary : Matrix E E ℂ)) = _
  calc
    _ = (T * tensorPower m (hH.eigenvectorUnitary : Matrix E E ℂ)) *
        tensorPower m (Matrix.diagonal (fun e => (hH.eigenvalues e : ℂ))) *
        tensorPower m (star hH.eigenvectorUnitary : Matrix E E ℂ) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hU]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc T, hD]
      simp only [Matrix.mul_assoc]
      rw [hV]
      rfl

/-- The full complex tensor commutant is already determined by the unitary
group. No invariant-theory theorem is assumed. -/
theorem commutes_tensorPower_of_unitary (m : ℕ)
    (T : Matrix (Fin m → E) (Fin m → E) ℂ)
    (h : ∀ U : Matrix.unitaryGroup E ℂ,
      T * tensorPower m (U : Matrix E E ℂ) = tensorPower m (U : Matrix E E ℂ) * T)
    (A : Matrix E E ℂ) : T * tensorPower m A = tensorPower m A * T :=
  commutes_tensorPower_of_hermitian m T
    (commutes_tensorPower_hermitian_of_unitary m T h) A

#print axioms commutes_tensorPower_of_unitary

end ProjectionChannels.TensorHaar
