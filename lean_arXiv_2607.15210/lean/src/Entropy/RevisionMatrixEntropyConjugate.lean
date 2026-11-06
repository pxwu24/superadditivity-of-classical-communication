import Entropy.RevisionMatrixEntropy
import Preliminaries.PreliminariesChoi

open Matrix PreliminariesMatrix ProjectionChannels RevisionOutput Set
open scoped BigOperators ComplexOrder Topology
noncomputable section
namespace RevisionMatrixEntropy
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma entrywiseConjugate_mul (M N : Matrix A A ℂ) :
    entrywiseConjugate (M*N)=entrywiseConjugate M*entrywiseConjugate N := by
  ext i j
  simp [entrywiseConjugate,Matrix.mul_apply,map_sum,map_mul]

lemma entrywiseConjugate_star (M : Matrix A A ℂ) :
    entrywiseConjugate (star M)=star (entrywiseConjugate M) := by
  ext i j
  simp [entrywiseConjugate,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]

@[simp] lemma entrywiseConjugate_one : entrywiseConjugate (1:Matrix A A ℂ)=1 := by
  ext i j
  simp [entrywiseConjugate,Matrix.one_apply]

@[simp] lemma entrywiseConjugate_involutive (M : Matrix A B ℂ) :
    entrywiseConjugate (entrywiseConjugate M)=M := by
  ext i j
  simp [entrywiseConjugate]

def conjugateUnitary (U : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup A ℂ :=
  ⟨entrywiseConjugate (U:Matrix A A ℂ), by
    constructor
    · rw [←entrywiseConjugate_star,←entrywiseConjugate_mul,U.prop.1]
      exact entrywiseConjugate_one
    · rw [←entrywiseConjugate_star,←entrywiseConjugate_mul,U.prop.2]
      exact entrywiseConjugate_one⟩

lemma entrywiseConjugate_unitaryDiagonal (U : Matrix.unitaryGroup A ℂ) (v : A→ℝ) :
    entrywiseConjugate (unitaryDiagonal U v) = unitaryDiagonal (conjugateUnitary U) v := by
  change entrywiseConjugate ((U:Matrix A A ℂ)*diagonal (fun i=>(v i:ℂ))*star (U:Matrix A A ℂ)) = _
  rw [entrywiseConjugate_mul,entrywiseConjugate_mul,entrywiseConjugate_star]
  have hd : entrywiseConjugate (diagonal (fun i=>(v i:ℂ))) = diagonal (fun i=>(v i:ℂ)) := by
    ext i j
    simp only [entrywiseConjugate,diagonal_apply]
    split_ifs <;> simp
  rw [hd]
  rfl

lemma matrixRenyiEntropy_eq_eigenvalues (p : ℝ) (hp : 0<p)
    (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    matrixRenyiEntropy p M = AppendixB.renyi p Finset.univ (fun _ : A=>1) hM.eigenvalues := by
  have heq : M=unitaryDiagonal hM.eigenvectorUnitary hM.eigenvalues := hM.spectral_theorem
  conv_lhs => rw [heq]
  exact matrixRenyiEntropy_unitaryDiagonal p hp _ _

/-- Entrywise complex conjugation preserves the entropy of every Hermitian matrix. -/
theorem matrixRenyiEntropy_entrywiseConjugate (p : ℝ) (hp : 0<p)
    (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    matrixRenyiEntropy p (entrywiseConjugate M)=matrixRenyiEntropy p M := by
  have heq : M=unitaryDiagonal hM.eigenvectorUnitary hM.eigenvalues := hM.spectral_theorem
  rw [heq,entrywiseConjugate_unitaryDiagonal,
    matrixRenyiEntropy_unitaryDiagonal p hp,matrixRenyiEntropy_unitaryDiagonal p hp]

lemma unitaryDiagonal_mul (U V : Matrix.unitaryGroup A ℂ) (v : A→ℝ) :
    unitaryDiagonal (U*V) v=(U:Matrix A A ℂ)*unitaryDiagonal V v*star (U:Matrix A A ℂ) := by
  change ((U:Matrix A A ℂ)*(V:Matrix A A ℂ))*diagonal (fun i=>(v i:ℂ))*
    star ((U:Matrix A A ℂ)*(V:Matrix A A ℂ)) = _
  simp only [StarMul.star_mul,unitaryDiagonal,unitaryConjugateDiagonalHom,
    StarAlgHom.coe_mk,AlgHom.coe_mk,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,mul_assoc]

/-- Unitary conjugation preserves matrix Rényi entropy. -/
theorem matrixRenyiEntropy_unitaryConjugate (p : ℝ) (hp : 0<p)
    (U : Matrix.unitaryGroup A ℂ) (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    matrixRenyiEntropy p ((U:Matrix A A ℂ)*M*star (U:Matrix A A ℂ))=matrixRenyiEntropy p M := by
  have heq : M=unitaryDiagonal hM.eigenvectorUnitary hM.eigenvalues := hM.spectral_theorem
  rw [heq,←unitaryDiagonal_mul,matrixRenyiEntropy_unitaryDiagonal p hp,
    matrixRenyiEntropy_unitaryDiagonal p hp]

variable [Nonempty A]

lemma entrywiseConjugate_density {ρ : Matrix A A ℂ} (hρ : ρ∈densityMatrices A) :
    entrywiseConjugate ρ∈densityMatrices A := by
  obtain ⟨⟨U,v⟩,heq⟩ := diagonalizationMap_surjective (⟨ρ,hρ⟩ : densityMatrices A)
  have h : unitaryDiagonal U v=ρ := congrArg Subtype.val heq
  rw [←h,entrywiseConjugate_unitaryDiagonal]
  exact unitaryDiagonal_density _ _

lemma entrywiseConjugate_image_density : entrywiseConjugate '' densityMatrices A=densityMatrices A := by
  ext ρ
  constructor
  · rintro ⟨σ,hσ,rfl⟩
    exact entrywiseConjugate_density hσ
  · intro hρ
    exact ⟨entrywiseConjugate ρ,entrywiseConjugate_density hρ,entrywiseConjugate_involutive ρ⟩

/-- Minimum output entropy of an actual matrix map. -/
def minimumOutputEntropy (p : ℝ) (Φ : Matrix A A ℂ→Matrix B B ℂ) : ℝ :=
  sInf (matrixRenyiEntropy p '' (Φ '' densityMatrices A))

lemma entropy_image_conjugateMap (p : ℝ) (hp : 0<p)
    (Φ : Matrix A A ℂ→Matrix B B ℂ)
    (hΦ : ∀ρ∈densityMatrices A, (Φ ρ).IsHermitian) :
    matrixRenyiEntropy p '' (conjugateMap Φ '' densityMatrices A)=
      matrixRenyiEntropy p '' (Φ '' densityMatrices A) := by
  ext y
  constructor
  · rintro ⟨σ,⟨ρ,hρ,rfl⟩,rfl⟩
    refine ⟨Φ (entrywiseConjugate ρ),⟨entrywiseConjugate ρ,entrywiseConjugate_density hρ,rfl⟩,?_⟩
    exact (matrixRenyiEntropy_entrywiseConjugate p hp _ (hΦ _ (entrywiseConjugate_density hρ))).symm
  · rintro ⟨σ,⟨ρ,hρ,rfl⟩,rfl⟩
    refine ⟨conjugateMap Φ (entrywiseConjugate ρ),
      ⟨entrywiseConjugate ρ,entrywiseConjugate_density hρ,rfl⟩,?_⟩
    unfold conjugateMap
    rw [entrywiseConjugate_involutive]
    exact matrixRenyiEntropy_entrywiseConjugate p hp _ (hΦ _ hρ)

theorem minimumOutputEntropy_conjugateMap (p : ℝ) (hp : 0<p)
    (Φ : Matrix A A ℂ→Matrix B B ℂ)
    (hΦ : ∀ρ∈densityMatrices A, (Φ ρ).IsHermitian) :
    minimumOutputEntropy p (conjugateMap Φ)=minimumOutputEntropy p Φ := by
  unfold minimumOutputEntropy
  rw [entropy_image_conjugateMap p hp Φ hΦ]

end RevisionMatrixEntropy
