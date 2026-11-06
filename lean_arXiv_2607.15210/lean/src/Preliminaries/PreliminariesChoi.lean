import Preliminaries.PreliminariesMatrix

/-!
# Choi reconstruction and the convention for a diagonal trace map

The manuscript uses input-first Choi matrices.  The block-modification source
uses output-first matrices.  This file checks the two formulas on matrix
entries and checks the scalar partial-trace condition for the relevant
eigenspace projections.  No probabilistic or free-probability limit theorem
is assumed or asserted here.
-/

open scoped BigOperators
open Matrix PreliminariesMatrix Classical

noncomputable section

namespace ProjectionChannels

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Input-first Choi matrix, with row and column order `(input, output)`. -/
def choiInput [DecidableEq A] (Φ : Matrix A A ℂ → Matrix B B ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  fun ai bj => Φ (matrixUnit ai.1 bj.1) ai.2 bj.2

/-- Output-first Choi matrix, with row and column order `(output, input)`. -/
def choiOutput [DecidableEq A] (Φ : Matrix A A ℂ → Matrix B B ℂ) :
    Matrix (B × A) (B × A) ℂ :=
  fun ia jb => Φ (matrixUnit ia.2 jb.2) ia.1 jb.1

/-- The two conventions differ only by swapping the tensor factors. -/
theorem choi_conventions [DecidableEq A]
    (Φ : Matrix A A ℂ → Matrix B B ℂ) (i j : B) (a b : A) :
    choiOutput Φ (i, a) (j, b) = choiInput Φ (a, i) (b, j) := rfl

/-- Expansion in standard matrix units. -/
theorem matrixUnit_expansion [DecidableEq A] (X : Matrix A A ℂ) :
    (∑ a : A, ∑ b : A, X a b • matrixUnit a b) = X := by
  classical
  ext c d
  simp [matrixUnit, Matrix.sum_apply, Pi.smul_apply, smul_eq_mul, ite_and]

/-- Encoding a linear map and applying Choi inversion recovers that map. -/
theorem choi_reconstructs_linearMap [DecidableEq A]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (X : Matrix A A ℂ) :
    channel (choiInput Φ) X = Φ X := by
  classical
  have h := congrArg Φ (matrixUnit_expansion X)
  simp only [map_sum, map_smul] at h
  rw [← h]
  ext i j
  simp [channel, choiInput, Matrix.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Complex conjugation of entries, without taking a transpose. -/
def entrywiseConjugate {M N : Type*} (X : Matrix M N ℂ) : Matrix M N ℂ :=
  fun i j => starRingEnd ℂ (X i j)

/-- The conjugate map in the fixed product bases. -/
def conjugateMap (Φ : Matrix A A ℂ → Matrix B B ℂ)
    (X : Matrix A A ℂ) : Matrix B B ℂ :=
  entrywiseConjugate (Φ (entrywiseConjugate X))

theorem conjugate_matrixUnit [DecidableEq A] (a b : A) :
    entrywiseConjugate (matrixUnit a b) = matrixUnit a b := by
  ext i j
  simp [entrywiseConjugate, matrixUnit]

/-- Conjugating the channel conjugates the entries of its Choi matrix. -/
theorem conjugateMap_choi [DecidableEq A]
    (Φ : Matrix A A ℂ → Matrix B B ℂ) :
    choiInput (conjugateMap Φ) = entrywiseConjugate (choiInput Φ) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [choiInput, conjugateMap, conjugate_matrixUnit, entrywiseConjugate]

/-- The diagonal trace map used in the random compression proof. -/
def diagonalTraceMap [DecidableEq A] [DecidableEq B]
    (a : A → ℂ) (X : Matrix A A ℂ) : Matrix B B ℂ :=
  Matrix.trace (Matrix.diagonal a * X) • (1 : Matrix B B ℂ)

/-- Entry formula for the weighted trace. -/
theorem diagonal_trace_formula [DecidableEq A]
    (a : A → ℂ) (X : Matrix A A ℂ) :
    Matrix.trace (Matrix.diagonal a * X) = ∑ i : A, a i * X i i := by
  simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

/-- The diagonal trace functional on matrix units. -/
theorem diagonal_trace_matrixUnit [DecidableEq A]
    (a : A → ℂ) (r s : A) :
    Matrix.trace (Matrix.diagonal a * matrixUnit r s) =
      if r = s then a r else 0 := by
  classical
  rw [diagonal_trace_formula]
  simp [matrixUnit, ite_and]

/-- In the manuscript's input-first convention the Choi matrix is `A ⊗ I`. -/
theorem diagonalTraceMap_choiInput [DecidableEq A] [DecidableEq B]
    (a : A → ℂ) :
    choiInput (diagonalTraceMap (B := B) a) =
      Matrix.kronecker (Matrix.diagonal a) (1 : Matrix B B ℂ) := by
  classical
  ext ⟨r, i⟩ ⟨s, j⟩
  simp [choiInput, diagonalTraceMap, diagonal_trace_matrixUnit,
    Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Pi.smul_apply, smul_eq_mul]

/-- In the source's output-first convention the same Choi matrix is `I ⊗ A`. -/
theorem diagonalTraceMap_choiOutput [DecidableEq A] [DecidableEq B]
    (a : A → ℂ) :
    choiOutput (diagonalTraceMap (B := B) a) =
      Matrix.kronecker (1 : Matrix B B ℂ) (Matrix.diagonal a) := by
  classical
  ext ⟨i, r⟩ ⟨j, s⟩
  simp [choiOutput, diagonalTraceMap, diagonal_trace_matrixUnit,
    Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Tracing the input factor of an output-first tensor product gives a scalar identity. -/
theorem outputFirst_partialTrace [DecidableEq B] (E : Matrix A A ℂ) :
    traceB (Matrix.kronecker (1 : Matrix B B ℂ) E) =
      Matrix.trace E • (1 : Matrix B B ℂ) := by
  classical
  ext i j
  simp [traceB, Matrix.kronecker_apply, Matrix.trace, Matrix.diag,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_comm]

/-- The diagonal projection onto the coordinates with eigenvalue `x`. -/
noncomputable def levelProjection (a : A → ℝ) (x : ℝ) : Matrix A A ℂ :=
  Matrix.diagonal (fun i => if a i = x then 1 else 0)

/-- These coordinate eigenspace matrices are idempotent. -/
theorem levelProjection_idempotent (a : A → ℝ) (x : ℝ) :
    levelProjection a x * levelProjection a x = levelProjection a x := by
  classical
  rw [levelProjection, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  split_ifs <;> norm_num

/-- The coordinate projections are self-adjoint. -/
theorem levelProjection_isHermitian (a : A → ℝ) (x : ℝ) :
    (levelProjection a x).IsHermitian := by
  classical
  rw [Matrix.IsHermitian]
  ext i j
  by_cases h : i = j
  · subst j
    simp [levelProjection, Matrix.conjTranspose_apply]
  · simp [levelProjection, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h]

/-- Their ranges lie in the indicated eigenspaces of the real diagonal matrix. -/
theorem diagonal_mul_levelProjection (a : A → ℝ) (x : ℝ) :
    Matrix.diagonal (fun i => (a i : ℂ)) * levelProjection a x =
      (x : ℂ) • levelProjection a x := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hx : a i = x <;>
      simp [levelProjection, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul, hx]
  · simp [levelProjection, Matrix.diagonal_mul, Matrix.diagonal_apply, h]

/-- Their trace is precisely the eigenvalue multiplicity. -/
theorem levelProjection_trace (a : A → ℝ) (x : ℝ) :
    Matrix.trace (levelProjection a x) =
      ((Finset.univ.filter (fun i => a i = x)).card : ℂ) := by
  classical
  simp [levelProjection, Matrix.trace_diagonal]

/-- The required partial trace is the multiplicity times the output identity. -/
theorem spectralProjection_partialTrace [DecidableEq B] (a : A → ℝ) (x : ℝ) :
    traceB (Matrix.kronecker (1 : Matrix B B ℂ) (levelProjection a x)) =
      ((Finset.univ.filter (fun i => a i = x)).card : ℂ) • (1 : Matrix B B ℂ) := by
  classical
  rw [outputFirst_partialTrace, levelProjection_trace]

end ProjectionChannels

