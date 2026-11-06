import Antisymmetric.RevisionAntisymmetricBellOperators

/-! Matrix realization of the one-body action and its compression. -/
noncomputable section
open Finset Equiv PreliminariesMatrix
namespace AntisymmetricVerification
variable {k r : ℕ}

def oneLegLinear (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r) :
    TensorVector k r →ₗ[ℂ] TensorVector k r where
  toFun := oneLeg X i
  map_add' := oneLeg_add X i
  map_smul' := oneLeg_smul X i

def oneLegMatrix (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r) :
    Matrix (TensorIndex k r) (TensorIndex k r) ℂ :=
  LinearMap.toMatrix' (oneLegLinear X i)

lemma oneLegMatrix_mulVec (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r)
    (f : TensorVector k r) : (oneLegMatrix X i).mulVec f = oneLeg X i f := by
  exact congrArg (fun L => L f) (Matrix.toLin'_toMatrix' (oneLegLinear X i))

lemma compressed_oneLegMatrix_independent (X : Matrix (Fin k) (Fin k) ℂ)
    (i j : Fin r) :
    antisymMatrix * oneLegMatrix X i * antisymMatrix =
      antisymMatrix * oneLegMatrix X j * antisymMatrix := by
  classical
  apply Matrix.ext_of_mulVec_single
  intro x
  simp only [← Matrix.mulVec_mulVec, antisymMatrix_mulVec, oneLegMatrix_mulVec]
  exact antisymmetrize_oneLeg_eq X i j (antisymmetrize_alternating _)

/-- The compressed sum of one-body terms is `r` times one compressed leg. -/
theorem compressed_allLegsMatrix (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r) :
    antisymMatrix * (∑ j : Fin r, oneLegMatrix X j) * antisymMatrix =
      (r : ℂ) • (antisymMatrix * oneLegMatrix X i * antisymMatrix) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp_rw [compressed_oneLegMatrix_independent X _ i]
  simp only [sum_const, card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul ℂ]

def firstTensorEquiv : (Fin k × TensorIndex k r) ≃ TensorIndex k (r + 1) :=
  Fin.consEquiv (fun _ => Fin k)

lemma update_zero_eq_cons (x : TensorIndex k (r + 1)) (a : Fin k) :
    Function.update x 0 a = Fin.cons a (Fin.tail x) := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.tail]

/-- The explicitly defined first-leg action is precisely `X ⊗ I` under the
 standard product identification of the tensor coordinates. -/
theorem oneLegMatrix_zero_product (X : Matrix (Fin k) (Fin k) ℂ) :
    (oneLegMatrix X (0 : Fin (r + 1))).submatrix
      (firstTensorEquiv (k := k) (r := r)) firstTensorEquiv =
      Matrix.kronecker X (1 : Matrix (TensorIndex k r) (TensorIndex k r) ℂ) := by
  classical
  ext ⟨a,x⟩ ⟨b,y⟩
  rw [Matrix.submatrix_apply, oneLegMatrix, LinearMap.toMatrix'_apply]
  change oneLeg X 0 (fun z => if z = firstTensorEquiv (b,y) then 1 else 0)
    (firstTensorEquiv (a,x)) = _
  simp only [oneLeg, firstTensorEquiv, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero,
    update_zero_eq_cons, Fin.tail_cons]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  have heq : ∀ c : Fin k, (Fin.cons c x : TensorIndex k (r + 1)) =
      (Fin.cons b y : TensorIndex k (r + 1)) ↔ c = b ∧ x = y := by
    intro c
    constructor
    · intro h
      exact ⟨congrFun h 0, congrArg Fin.tail h⟩
    · rintro ⟨rfl,rfl⟩
      rfl
  simp only [heq, ite_and, mul_ite, mul_one, mul_zero]
  simp [eq_comm]

def antisymMatrixProduct : Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ :=
  (antisymMatrix (k := k) (r := r + 1)).submatrix firstTensorEquiv firstTensorEquiv

/-- The actual compressed second-quantized matrix unit used in B.2. -/
def oneBodyGenerator (a b : Fin k) : Matrix (TensorIndex k r) (TensorIndex k r) ℂ :=
  antisymMatrix * (∑ j : Fin r, oneLegMatrix (matrixUnit a b) j) * antisymMatrix

lemma generator_in_product_coordinates (a b : Fin k) :
    (oneBodyGenerator (r := r + 1) a b).submatrix firstTensorEquiv firstTensorEquiv =
      ((r + 1 : ℕ) : ℂ) •
        (antisymMatrixProduct * Matrix.kronecker (matrixUnit a b)
          (1 : Matrix (TensorIndex k r) (TensorIndex k r) ℂ) * antisymMatrixProduct) := by
  unfold oneBodyGenerator
  rw [compressed_allLegsMatrix _ 0]
  simp only [Matrix.submatrix_smul, Pi.smul_apply]
  congr 1
  rw [← Matrix.submatrix_mul_equiv _ _ firstTensorEquiv firstTensorEquiv firstTensorEquiv,
    ← Matrix.submatrix_mul_equiv _ _ firstTensorEquiv firstTensorEquiv firstTensorEquiv,
    oneLegMatrix_zero_product]
  rfl

/-- The actual one-body generators have precisely the partial-trace Gram
 contraction stated in B.2. The support hypotheses express `Y ∈ B(A_(r+1))`. -/
theorem antisymmetric_bell_gram_identity
    (Y : Matrix (Fin k × TensorIndex k r) (Fin k × TensorIndex k r) ℂ)
    (hPY : antisymMatrixProduct * Y = Y) (hYP : Y * antisymMatrixProduct = Y) :
    (∑ a : Fin k, ∑ b : Fin k,
      ((oneBodyGenerator (r := r + 1) a b).submatrix firstTensorEquiv firstTensorEquiv) * Y *
        ((oneBodyGenerator (r := r + 1) b a).submatrix firstTensorEquiv firstTensorEquiv)) =
      (((r + 1 : ℕ) : ℂ) ^ 2) •
        (antisymMatrixProduct * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
          (traceA Y) * antisymMatrixProduct) := by
  simp only [generator_in_product_coordinates]
  exact scaled_compressed_twirl antisymMatrixProduct Y hPY hYP _

end AntisymmetricVerification
