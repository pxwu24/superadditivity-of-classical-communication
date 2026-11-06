import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Deterministic matrix identities in the preliminaries

These proofs check the Choi convention, trace preservation, normalization by a
local congruence, and the deterministic rank reduction used in the Gaussian
proof. They do not assert a probabilistic Haar theorem or a free-probability
strong-convergence theorem.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace PreliminariesMatrix

noncomputable section

variable {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]

/-- Trace over the second factor, in the prescribed product basis. -/
def traceB (J : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  fun a b => ∑ i : B, J (a, i) (b, i)

/-- Trace over the first factor. -/
def traceA (J : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  fun i j => ∑ a : A, J (a, i) (a, j)

/-- The map associated with an unnormalized Choi matrix. -/
def channel (J : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) : Matrix B B ℂ :=
  fun i j => ∑ a : A, ∑ b : A, J (a, i) (b, j) * X a b

/-- The standard matrix unit. -/
def matrixUnit [DecidableEq A] (a b : A) : Matrix A A ℂ :=
  fun c d => if c = a ∧ d = b then 1 else 0

omit [Fintype B] in
/-- Recovering the Choi entries gives exactly the original matrix. -/
theorem choi_recovery [DecidableEq A]
    (J : Matrix (A × B) (A × B) ℂ) (a b : A) (i j : B) :
    channel J (matrixUnit a b) i j = J (a, i) (b, j) := by
  classical
  simp [channel, matrixUnit, ite_and]

/-- Checks the transpose placement in the Choi inversion formula. -/
theorem choi_inversion [DecidableEq B]
    (J : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :
    traceA (J * Matrix.kronecker X.transpose (1 : Matrix B B ℂ)) = channel J X := by
  classical
  ext i j
  simp [traceA, channel, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply]

/-- The channel's trace is the pairing with the input marginal of its Choi matrix. -/
theorem channel_trace (J : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :
    Matrix.trace (channel J X) = ∑ a : A, ∑ b : A, traceB J a b * X a b := by
  classical
  simp only [Matrix.trace, Matrix.diag, channel, traceB, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]

/-- Normalized input marginal implies trace preservation for every input matrix. -/
theorem channel_trace_preserving [DecidableEq A]
    (J : Matrix (A × B) (A × B) ℂ) (hJ : traceB J = 1) (X : Matrix A A ℂ) :
    Matrix.trace (channel J X) = Matrix.trace X := by
  rw [channel_trace, hJ]
  simp [Matrix.trace, Matrix.diag, Matrix.one_apply]

/-- The partial trace intertwines left multiplication on the first factor. -/
theorem traceB_left [DecidableEq B]
    (H : Matrix A A ℂ) (R : Matrix (A × B) (A × B) ℂ) :
    traceB (Matrix.kronecker H (1 : Matrix B B ℂ) * R) = H * traceB R := by
  classical
  ext a b
  simp only [traceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- The partial trace intertwines right multiplication on the first factor. -/
theorem traceB_right [DecidableEq B]
    (H : Matrix A A ℂ) (R : Matrix (A × B) (A × B) ℂ) :
    traceB (R * Matrix.kronecker H (1 : Matrix B B ℂ)) = traceB R * H := by
  classical
  ext a b
  simp only [traceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- Exact local congruence identity used to normalize the generalized Choi operator. -/
theorem traceB_congruence [DecidableEq B]
    (H : Matrix A A ℂ) (R : Matrix (A × B) (A × B) ℂ) :
    traceB (Matrix.kronecker H (1 : Matrix B B ℂ) * R *
      Matrix.kronecker H (1 : Matrix B B ℂ)) = H * traceB R * H := by
  rw [traceB_right, traceB_left]

/-- Any Hermitian normalizer with `H R_A H = I` yields a positive normalized Choi matrix.
    In the manuscript, `H = R_A^(-1/2)`; this theorem isolates the algebraic step. -/
theorem normalized_choi [DecidableEq A] [DecidableEq B]
    (H : Matrix A A ℂ) (R : Matrix (A × B) (A × B) ℂ)
    (hH : H.IsHermitian) (hR : R.PosSemidef)
    (hN : H * traceB R * H = 1) :
    let J := Matrix.kronecker H (1 : Matrix B B ℂ) * R *
      Matrix.kronecker H (1 : Matrix B B ℂ)
    J.PosSemidef ∧ traceB J = 1 := by
  dsimp only
  constructor
  · have hK : (Matrix.kronecker H (1 : Matrix B B ℂ)).IsHermitian := by
      apply Matrix.IsHermitian.ext
      rintro ⟨a, i⟩ ⟨b, j⟩
      by_cases hij : i = j
      · subst j
        simpa only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
          mul_one] using hH.apply a b
      · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, hij, Ne.symm hij]
    simpa only [hK.eq] using
      hR.mul_mul_conjTranspose_same (Matrix.kronecker H (1 : Matrix B B ℂ))
  · rw [traceB_congruence, hN]

/-- The normalizer in the paper can actually be chosen as the inverse of the
positive square root of the input marginal. -/
theorem inverse_sqrt_normalized_choi [DecidableEq A] [DecidableEq B]
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef)
    (hRA : (traceB R).PosDef) :
    let H := hRA.posSemidef.sqrt⁻¹
    let J := Matrix.kronecker H (1 : Matrix B B ℂ) * R *
      Matrix.kronecker H (1 : Matrix B B ℂ)
    J.PosSemidef ∧ traceB J = 1 := by
  let S := hRA.posSemidef.sqrt
  have hS : S.IsHermitian := hRA.posSemidef.posSemidef_sqrt.isHermitian
  have hSsq : S * S = traceB R := hRA.posSemidef.sqrt_mul_self
  have hdet : IsUnit S.det := by
    have h : IsUnit (S.det * S.det) := by
      rw [← Matrix.det_mul, hSsq]
      exact (Matrix.isUnit_iff_isUnit_det _).mp hRA.isUnit
    exact (IsUnit.mul_iff.mp h).1
  apply normalized_choi S⁻¹ R hS.inv hR
  rw [← hSsq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hdet,
    Matrix.one_mul, Matrix.mul_nonsing_inv S hdet]

/-- Reshape the columns of a bipartite Gaussian matrix into an `A × (B × D)` matrix. -/
def flatten (G : Matrix (A × B) D ℂ) : Matrix A (B × D) ℂ :=
  fun a il => G (a, il.1) il.2

omit [Fintype A] in
/-- Reduced Gram matrices equal Gram matrices of the reshaped matrix. -/
theorem reduced_gram (G : Matrix (A × B) D ℂ) :
    traceB (G * G.conjTranspose) = flatten G * (flatten G).conjTranspose := by
  classical
  ext a b
  simp [traceB, flatten, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply]

omit [Fintype A] in
/-- The weighted reduced Gram matrix appearing in Gaussian whitening. -/
theorem reduced_weighted_gram [DecidableEq B]
    (G : Matrix (A × B) D ℂ) (M : Matrix D D ℂ) :
    traceB (G * M * G.conjTranspose) =
      flatten G * Matrix.kronecker (1 : Matrix B B ℂ) M *
        (flatten G).conjTranspose := by
  classical
  ext a b
  simp [traceB, flatten, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply, Matrix.one_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]

/-- Deterministic rank identity behind the full local support argument. -/
theorem reduced_gram_rank (G : Matrix (A × B) D ℂ) :
    (traceB (G * G.conjTranspose)).rank = (flatten G).rank := by
  rw [reduced_gram, Matrix.rank_self_mul_conjTranspose]

/-- For positive definite `M`, a congruence has the same kernel as `Hᴴ`. -/
theorem posDef_congruence_kernel
    (H : Matrix A D ℂ) (M : Matrix D D ℂ) (hM : M.PosDef) :
    LinearMap.ker (H * M * H.conjTranspose).mulVecLin =
      LinearMap.ker H.conjTranspose.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hx
    by_contra hn
    have hp := hM.2 (H.conjTranspose *ᵥ x) hn
    have hz : star (H.conjTranspose *ᵥ x) ⬝ᵥ M *ᵥ (H.conjTranspose *ᵥ x) = 0 := by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, hx, dotProduct_zero]
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · intro hx
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- A positive definite middle factor does not change the rank of a congruence. -/
theorem posDef_congruence_rank
    (H : Matrix A D ℂ) (M : Matrix D D ℂ) (hM : M.PosDef) :
    (H * M * H.conjTranspose).rank = H.rank := by
  rw [← Matrix.rank_conjTranspose H]
  unfold Matrix.rank
  have h1 := LinearMap.finrank_range_add_finrank_ker (H * M * H.conjTranspose).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker H.conjTranspose.mulVecLin
  rw [posDef_congruence_kernel H M hM] at h1
  omega

end

end PreliminariesMatrix

