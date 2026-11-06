import Antisymmetric.RevisionAntisymmetricMatrixRecursion

/-! Partial-trace identities for the actual first-leg swap matrices. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

variable {A B : Type*} [Fintype A] [Fintype B]
def partialTraceLinear : Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun := traceA
  map_add' Y Z := by ext i j; simp [traceA, Finset.sum_add_distrib]
  map_smul' c Y := by ext i j; simp [traceA, Finset.mul_sum]

lemma traceA_fintype_sum {ι : Type*} [Fintype ι]
    (Y : ι → Matrix (A × B) (A × B) ℂ) : traceA (∑ i, Y i) = ∑ i, traceA (Y i) :=
  map_sum partialTraceLinear Y univ

lemma traceA_kronecker (H : Matrix A A ℂ) (Z : Matrix B B ℂ) :
    traceA (Matrix.kronecker H Z) = Matrix.trace H • Z := by
  ext i j
  simp [traceA, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.trace, Matrix.diag,
    Finset.sum_mul]

lemma traceA_smul (c : ℂ) (Y : Matrix (A × B) (A × B) ℂ) :
    traceA (c • Y) = c • traceA Y := map_smul partialTraceLinear c Y

lemma traceA_add (Y Z : Matrix (A × B) (A × B) ℂ) :
    traceA (Y + Z) = traceA Y + traceA Z := map_add partialTraceLinear Y Z

lemma traceA_sub (Y Z : Matrix (A × B) (A × B) ℂ) :
    traceA (Y - Z) = traceA Y - traceA Z := map_sub partialTraceLinear Y Z

variable [DecidableEq A] [DecidableEq B]
lemma kronecker_multiply (H K : Matrix A A ℂ) (L R : Matrix B B ℂ) :
    Matrix.kronecker H L * Matrix.kronecker K R = Matrix.kronecker (H * K) (L * R) :=
  (Matrix.mul_kronecker_mul H K L R).symm

lemma traceA_kronecker_units (a b c d : A) (L Z R : Matrix B B ℂ) :
    traceA (Matrix.kronecker (matrixUnit a b) L * Matrix.kronecker (1 : Matrix A A ℂ) Z *
      Matrix.kronecker (matrixUnit c d) R) =
      if b = c ∧ a = d then L * Z * R else 0 := by
  rw [kronecker_multiply, kronecker_multiply, traceA_kronecker,
    Matrix.mul_one]
  have htrace : Matrix.trace (matrixUnit a b * matrixUnit c d) =
      if b = c ∧ a = d then (1 : ℂ) else 0 := by
    by_cases hbc : b = c <;> by_cases had : a = d <;>
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, matrixUnit, ite_and, hbc, had, eq_comm]
  rw [htrace]
  split_ifs <;> simp

lemma swapFirstMatrix_mul (j : Fin r)
    (Y : Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ)
    (x y : Fin k × TensorIndex k r) :
    (swapFirstMatrix (k := k) j * Y) x y = Y (swapFirstIndex j x) y := by
  simp [Matrix.mul_apply, swapFirstMatrix, ite_mul]

lemma mul_swapFirstMatrix (j : Fin r)
    (Y : Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ)
    (x y : Fin k × TensorIndex k r) :
    (Y * swapFirstMatrix (k := k) j) x y = Y x (swapFirstIndex j y) := by
  simp only [Matrix.mul_apply, swapFirstMatrix, (swapFirstIndex_involutive j).eq_iff, mul_ite,
    mul_one, mul_zero]
  simp

/-- Every term containing a single first-leg swap traces to `Z`. -/
theorem traceA_swapFirst_left (j : Fin r) (Z : Matrix (TensorIndex k r) (TensorIndex k r) ℂ) :
    traceA (swapFirstMatrix j * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z) = Z := by
  ext x y
  simp only [traceA, swapFirstMatrix_mul, swapFirstIndex, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp

theorem traceA_swapFirst_right (j : Fin r) (Z : Matrix (TensorIndex k r) (TensorIndex k r) ℂ) :
    traceA (Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * swapFirstMatrix j) = Z := by
  ext x y
  simp only [traceA, mul_swapFirstMatrix, swapFirstIndex, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp

/-- The two-swap terms are matrix-unit contractions on the chosen tail legs. -/
theorem traceA_two_swaps (i j : Fin r)
    (Z : Matrix (TensorIndex k r) (TensorIndex k r) ℂ) :
    traceA (swapFirstMatrix i * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z *
      swapFirstMatrix j) = ∑ a : Fin k, ∑ b : Fin k,
        oneLegMatrix (matrixUnit b a) i * Z * oneLegMatrix (matrixUnit a b) j := by
  simp only [swapFirstMatrix_matrixUnits, Finset.sum_mul, Finset.mul_sum, traceA_fintype_sum,
    traceA_kronecker_units]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sum_const_zero]
  rw [Finset.sum_comm]

/-- On the antisymmetric tail space every two-swap term is the same compressed
 one-leg Gram map. This is the two-sign cancellation required by B.2. -/
theorem compressed_traceA_two_swaps (i j h : Fin r)
    (Z : Matrix (TensorIndex k r) (TensorIndex k r) ℂ)
    (hPZ : antisymMatrix * Z = Z) (hZP : Z * antisymMatrix = Z) :
    antisymMatrix * traceA (swapFirstMatrix i *
      Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ) Z * swapFirstMatrix j) * antisymMatrix =
      ∑ a : Fin k, ∑ b : Fin k,
        (antisymMatrix * oneLegMatrix (matrixUnit b a) h * antisymMatrix) * Z *
          (antisymMatrix * oneLegMatrix (matrixUnit a b) h * antisymMatrix) := by
  rw [traceA_two_swaps]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  calc
    _ = (antisymMatrix * oneLegMatrix (matrixUnit b a) i * antisymMatrix) * Z *
        (antisymMatrix * oneLegMatrix (matrixUnit a b) j * antisymMatrix) := by
      calc
        _ = antisymMatrix * oneLegMatrix (matrixUnit b a) i *
            (antisymMatrix * Z * antisymMatrix) * oneLegMatrix (matrixUnit a b) j * antisymMatrix := by
          rw [hPZ, hZP]
          simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [compressed_oneLegMatrix_independent _ i h, compressed_oneLegMatrix_independent _ j h]

end AntisymmetricVerification
