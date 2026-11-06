import Antisymmetric.RevisionAntisymmetricChannel
import Antisymmetric.RevisionSlaterLadderCoordinates
import Preliminaries.RevisionKrausVectorization
import BellOutput.RevisionBellChannel

/-! The actual Bell output of the antisymmetric channel is the vectorized
partial-trace Gram operator. The normalization factors are proved from the
channel definition, rather than assumed in a spectral model. -/

open Matrix Finset PreliminariesMatrix RevisionBell ProjectionChannels
open scoped BigOperators
noncomputable section
namespace AntisymmetricVerification

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

lemma entrywiseConjugate_add (X Y : Matrix A A ℂ) :
    entrywiseConjugate (X+Y) = entrywiseConjugate X + entrywiseConjugate Y := by
  ext i j
  simp [entrywiseConjugate]

lemma entrywiseConjugate_smul (c : ℂ) (X : Matrix A A ℂ) :
    entrywiseConjugate (c • X) = star c • entrywiseConjugate X := by
  ext i j
  simp [entrywiseConjugate, Matrix.smul_apply, smul_eq_mul]

lemma entrywiseConjugate_one : entrywiseConjugate (1 : Matrix A A ℂ) = 1 := by
  ext i j
  simp [entrywiseConjugate, Matrix.one_apply]

def conjugateLinearMap (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun := conjugateMap Φ
  map_add' X Y := by
    simp only [conjugateMap, entrywiseConjugate_add, map_add]
  map_smul' c X := by
    simp only [conjugateMap, entrywiseConjugate_smul, map_smul, star_star]
    rfl

lemma tensorMap_add_input (Φ Ψ : Matrix A A ℂ → Matrix B B ℂ)
    (X Y : Matrix (A×A) (A×A) ℂ) :
    tensorMap Φ Ψ (X+Y) = tensorMap Φ Ψ X + tensorMap Φ Ψ Y := by
  ext i j
  simp [tensorMap, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma tensorMap_smul_input (Φ Ψ : Matrix A A ℂ → Matrix B B ℂ)
    (c : ℂ) (X : Matrix (A×A) (A×A) ℂ) :
    tensorMap Φ Ψ (c • X) = c • tensorMap Φ Ψ X := by
  ext i j
  simp only [tensorMap, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma tensor_conjugate_one (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    tensorMap Φ (conjugateMap Φ) 1 =
      Matrix.kronecker (Φ 1) (entrywiseConjugate (Φ 1)) := by
  have h := tensorMap_kronecker Φ (conjugateLinearMap Φ) 1 1
  rw [show Matrix.kronecker (1 : Matrix A A ℂ) 1 = 1 from Matrix.one_kronecker_one] at h
  simpa only [conjugateLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    conjugateMap, entrywiseConjugate_one] using h

lemma tensor_conjugate_bell_supermatrix (Φ : Matrix A A ℂ → Matrix B B ℂ) :
    tensorMap Φ (conjugateMap Φ) (bellState A) =
      (1 / (Fintype.card A : ℂ)) •
        krausSupermatrix (fun ab : A × A => Φ (matrixUnit ab.1 ab.2)) := by
  ext ⟨i,p⟩ ⟨j,q⟩
  rw [tensor_conjugate_bell_entry]
  simp only [BellLimitVerification.bellEntry, choiInput, Matrix.smul_apply,
    smul_eq_mul, krausSupermatrix, Fintype.sum_prod_type]

lemma matrixUnit_conjTranspose (a b : A) :
    (matrixUnit a b).conjTranspose = matrixUnit b a := by
  ext i j
  simp [Matrix.conjTranspose_apply, matrixUnit, and_comm]

lemma kronecker_conjTranspose_matrix (X : Matrix A A ℂ) (Y : Matrix B B ℂ) :
    (Matrix.kronecker X Y).conjTranspose =
      Matrix.kronecker X.conjTranspose Y.conjTranspose := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]

lemma compressed_leg_twirl (U : Matrix (A × B) C ℂ) (Y : Matrix C C ℂ) :
    (∑ a : A, ∑ b : A,
      (U.conjTranspose * Matrix.kronecker (matrixUnit a b) (1 : Matrix B B ℂ) * U) * Y *
      (U.conjTranspose * Matrix.kronecker (matrixUnit b a) (1 : Matrix B B ℂ) * U)) =
      U.conjTranspose * Matrix.kronecker (1 : Matrix A A ℂ)
        (traceA (U * Y * U.conjTranspose)) * U := by
  rw [← matrixUnit_twirl]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

variable {k r : ℕ}

lemma slater_up_down_raw
    (Y : Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ) :
    slaterUp k r (slaterDown k r Y) =
      slaterProduct.conjTranspose * Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
        (traceA (slaterProduct * Y * slaterProduct.conjTranspose)) * slaterProduct := by
  let Z := slaterProduct * Y * (slaterProduct (k:=k) (r:=r)).conjTranspose
  have hPZ : antisymMatrixProduct * Z = Z := by
    dsimp [Z]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, slaterProduct_projection_left]
  have hZP : Z * antisymMatrixProduct = Z := by
    dsimp [Z]
    rw [Matrix.mul_assoc, slaterProduct_projection_right]
  have hs := antisym_partialTrace_support Z hPZ hZP
  have he : slaterIsometry * (slaterIsometry.conjTranspose * traceA Z * slaterIsometry) *
      slaterIsometry.conjTranspose = traceA Z := by
    calc
      _ = antisymMatrix * traceA Z * antisymMatrix := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, slaterIsometry_range_projection]
        rw [Matrix.mul_assoc, slaterIsometry_range_projection]
      _ = _ := hs
  unfold slaterUp slaterDown upCoordinates downCoordinates
  rw [he]

lemma antisymmetricChannel_unit_adjoint (a b : Fin k) :
    (antisymmetricChannel (r:=r) (matrixUnit a b)).conjTranspose =
      antisymmetricChannel (r:=r) (matrixUnit b a) := by
  simp only [antisymmetricChannel_product_formula, Matrix.conjTranspose_smul,
    star_div₀, star_natCast, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, kronecker_conjTranspose_matrix,
    Matrix.conjTranspose_one, matrixUnit_conjTranspose, Matrix.mul_assoc]

lemma antisymmetricChannel_unit_gram
    (Y : Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ) :
    (∑ a : Fin k, ∑ b : Fin k,
      antisymmetricChannel (r:=r) (matrixUnit a b) * Y *
        antisymmetricChannel (r:=r) (matrixUnit b a)) =
      (((k:ℂ)/(Nat.choose k (r+1):ℂ))^2) • slaterUp k r (slaterDown k r Y) := by
  simp only [antisymmetricChannel_product_formula, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← pow_two, ← Finset.smul_sum]
  rw [compressed_leg_twirl, slater_up_down_raw]

/-- Actual Bell output as an operator on vectorized Slater matrices. -/
theorem antisymmetricChannel_bell_mulVec
    (Y : Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ) :
    (tensorMap (antisymmetricChannel (k:=k) (r:=r))
      (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) (bellState (Fin k))).mulVec
        (matrixVec Y) =
      ((1/(k:ℂ)) * ((k:ℂ)/(Nat.choose k (r+1):ℂ))^2) •
        matrixVec (slaterUp k r (slaterDown k r Y)) := by
  rw [tensor_conjugate_bell_supermatrix, Matrix.smul_mulVec_assoc, krausSupermatrix_mulVec]
  simp only [Fintype.card_fin, Fintype.sum_prod_type, antisymmetricChannel_unit_adjoint,
    antisymmetricChannel_unit_gram]
  rw [← smul_smul]
  rfl

/-- The Bell matrix equals `k / D²` times the partial-trace Gram matrix,
where `D = choose k (r+1)`. This is the normalization used in B.2. -/
theorem antisymmetricChannel_bell_gram (hk : 0 < k) :
    tensorMap (antisymmetricChannel (k:=k) (r:=r))
      (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) (bellState (Fin k)) =
      ((k:ℂ)/(Nat.choose k (r+1):ℂ)^2) •
        ((slaterReductionMatrix k r).conjTranspose * slaterReductionMatrix k r) := by
  have hc : (1/(k:ℂ))*((k:ℂ)/(Nat.choose k (r+1):ℂ))^2 =
      (k:ℂ)/(Nat.choose k (r+1):ℂ)^2 := by
    have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    by_cases hn : (Nat.choose k (r+1):ℂ) = 0
    · simp [hn]
    · field_simp [hk0, hn]
      ring
  have he (Y : Matrix (SubsetIndex k (r+1)) (SubsetIndex k (r+1)) ℂ) :
      (tensorMap (antisymmetricChannel (k:=k) (r:=r))
        (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) (bellState (Fin k))).mulVec
          (matrixVec Y) =
        (((k:ℂ)/(Nat.choose k (r+1):ℂ)^2) •
          ((slaterReductionMatrix k r).conjTranspose * slaterReductionMatrix k r)).mulVec
          (matrixVec Y) := by
    rw [antisymmetricChannel_bell_mulVec, hc, Matrix.smul_mulVec_assoc,
      ← Matrix.mulVec_mulVec, slaterReductionMatrix_mulVec,
      slaterReductionMatrix_adj_mulVec]
  apply Matrix.ext_of_mulVec_single
  intro p
  simpa only [matrixVec] using he (fun i j => (Pi.single p (1:ℂ) : _ → ℂ) (i,j))

lemma antisymmetricChannel_one :
    antisymmetricChannel (k:=k) (r:=r) 1 =
      ((k:ℂ)/(Nat.choose k (r+1):ℂ)) • 1 := by
  rw [antisymmetricChannel_product_formula]
  rw [show Matrix.kronecker (1 : Matrix (Fin k) (Fin k) ℂ)
      (1 : Matrix (TensorIndex k r) (TensorIndex k r) ℂ) = 1 from Matrix.one_kronecker_one,
    Matrix.mul_one, slaterProduct_isometry]

lemma antisymmetricChannel_maximallyMixed (hk : 0 < k) :
    antisymmetricChannel (k:=k) (r:=r) ((1/(k:ℂ)) • 1) =
      (1/(Nat.choose k (r+1):ℂ)) • 1 := by
  rw [map_smul, antisymmetricChannel_one, smul_smul]
  congr 1
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp [hk0]

/-- The maximally mixed part remains maximally mixed after postprocessing. -/
lemma antisymmetricChannel_tensor_one :
    tensorMap (antisymmetricChannel (k:=k) (r:=r))
      (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) 1 =
      (((k:ℂ)/(Nat.choose k (r+1):ℂ))^2) • 1 := by
  rw [tensor_conjugate_one, antisymmetricChannel_one, entrywiseConjugate_smul,
    entrywiseConjugate_one]
  simp only [star_div₀, star_natCast, Matrix.kronecker, Matrix.smul_kronecker, Matrix.kronecker_smul,
    smul_smul, ← pow_two]
  congr 1
  exact Matrix.one_kronecker_one

/-- Exact isotropic postprocessing formula, before evaluating Gram eigenvalues. -/
theorem antisymmetricChannel_isotropic_gram (hk : 0 < k) (q : ℝ) :
    tensorMap (antisymmetricChannel (k:=k) (r:=r))
      (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) (isotropic (Fin k) q) =
      ((q:ℂ) * (k:ℂ)/(Nat.choose k (r+1):ℂ)^2) •
        ((slaterReductionMatrix k r).conjTranspose * slaterReductionMatrix k r) +
      (((1-q:ℝ):ℂ)/(Nat.choose k (r+1):ℂ)^2) • 1 := by
  rw [isotropic, tensorMap_add_input, tensorMap_smul_input, tensorMap_smul_input,
    antisymmetricChannel_bell_gram hk, antisymmetricChannel_tensor_one, smul_smul, smul_smul]
  simp only [Fintype.card_fin]
  congr 1
  · congr 1
    ring
  · congr 1
    push_cast
    have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp [hk0]

end AntisymmetricVerification
