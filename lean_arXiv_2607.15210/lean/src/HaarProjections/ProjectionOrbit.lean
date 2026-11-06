import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith

open Matrix

namespace ProjectionOrbit
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The spectral values of a Hermitian idempotent are zero or one. -/
theorem eigenvalues_zero_or_one {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hp : P * P = P) (i : E) :
    hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
  have hv : (⇑(hP.eigenvectorBasis i) : E → ℂ) ≠ 0 := by
    intro hz
    apply hP.eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun hz j
  have he := hP.mulVec_eigenvectorBasis i
  have hvec : (hP.eigenvalues i * hP.eigenvalues i) •
      (⇑(hP.eigenvectorBasis i) : E → ℂ) =
      hP.eigenvalues i • (⇑(hP.eigenvectorBasis i) : E → ℂ) := by
    calc
      _ = P *ᵥ (P *ᵥ ⇑(hP.eigenvectorBasis i)) := by rw [he, Matrix.mulVec_smul, he, smul_smul]
      _ = _ := by rw [Matrix.mulVec_mulVec, hp, he]
  have hs := smul_left_injective ℝ hv hvec
  have hf : hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- Equal-rank projections have matching eigenvalues after a permutation. -/
theorem exists_matching_eigenvalue_permutation {P Q : Matrix E E ℂ}
    (hP : P.IsHermitian) (hp : P * P = P)
    (hQ : Q.IsHermitian) (hq : Q * Q = Q) (hr : P.rank = Q.rank) :
    ∃ e : E ≃ E, ∀ i, hQ.eigenvalues (e i) = hP.eigenvalues i := by
  classical
  have hc : Fintype.card {i // hP.eigenvalues i ≠ 0} =
      Fintype.card {i // hQ.eigenvalues i ≠ 0} := by
    rw [← hP.rank_eq_card_non_zero_eigs, ← hQ.rank_eq_card_non_zero_eigs, hr]
  let es : {i // hP.eigenvalues i ≠ 0} ≃ {i // hQ.eigenvalues i ≠ 0} :=
    Fintype.equivOfCardEq hc
  refine ⟨es.extendSubtype, ?_⟩
  intro i
  by_cases hi : hP.eigenvalues i ≠ 0
  · have hqi := es.extendSubtype_mem i hi
    rw [(eigenvalues_zero_or_one hP hp i).resolve_left hi,
      (eigenvalues_zero_or_one hQ hq _).resolve_left hqi]
  · have hqi := es.extendSubtype_not_mem i hi
    simp only [not_not] at hi hqi
    rw [hi, hqi]


/-- Permuting the columns of a unitary matrix preserves unitarity. -/
def permuteColumns (U : Matrix.unitaryGroup E ℂ) (e : E ≃ E) :
    Matrix.unitaryGroup E ℂ :=
  ⟨(U : Matrix E E ℂ).submatrix id e, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change ((U : Matrix E E ℂ).submatrix id e).conjTranspose *
      (U : Matrix E E ℂ).submatrix id e = 1
    rw [Matrix.conjTranspose_submatrix]
    have hmul : (U : Matrix E E ℂ).conjTranspose.submatrix e id *
        (U : Matrix E E ℂ).submatrix id e =
        ((U : Matrix E E ℂ).conjTranspose * (U : Matrix E E ℂ)).submatrix e e := by
      simpa only [Equiv.coe_refl] using
        Matrix.submatrix_mul_equiv (U : Matrix E E ℂ).conjTranspose
          (U : Matrix E E ℂ) e (Equiv.refl E) e
    rw [hmul]
    change ((star (U : Matrix E E ℂ)) * (U : Matrix E E ℂ)).submatrix e e = 1
    rw [unitary.coe_star_mul_self, Matrix.submatrix_one_equiv]⟩

theorem permuteColumns_diagonalization (U : Matrix.unitaryGroup E ℂ) (e : E ≃ E)
    (Q : Matrix E E ℂ) :
    (star (permuteColumns U e : Matrix E E ℂ)) * Q * (permuteColumns U e : Matrix E E ℂ) =
      ((star (U : Matrix E E ℂ)) * Q * (U : Matrix E E ℂ)).submatrix e e := by
  change ((U : Matrix E E ℂ).submatrix id e).conjTranspose * Q *
    (U : Matrix E E ℂ).submatrix id e = _
  rw [Matrix.conjTranspose_submatrix]
  have hfirst : (U : Matrix E E ℂ).conjTranspose.submatrix e id * Q =
      ((U : Matrix E E ℂ).conjTranspose * Q).submatrix e id := by
    simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
      Matrix.submatrix_mul_equiv (U : Matrix E E ℂ).conjTranspose Q e (Equiv.refl E) id
  rw [hfirst]
  simpa only [Equiv.coe_refl] using
    Matrix.submatrix_mul_equiv ((U : Matrix E E ℂ).conjTranspose * Q)
      (U : Matrix E E ℂ) e (Equiv.refl E) e

/-- Every two finite complex Hermitian projections of the same rank are
unitarily conjugate. This includes rank zero and the full-rank projection. -/
theorem exists_unitary_conjugate (P Q : Matrix E E ℂ)
    (hP : P.IsHermitian) (hp : P * P = P)
    (hQ : Q.IsHermitian) (hq : Q * Q = Q) (hr : P.rank = Q.rank) :
    ∃ U : Matrix.unitaryGroup E ℂ,
      P = (U : Matrix E E ℂ) * Q * (U : Matrix E E ℂ).conjTranspose := by
  classical
  obtain ⟨e, he⟩ := exists_matching_eigenvalue_permutation hP hp hQ hq hr
  let V := permuteColumns hQ.eigenvectorUnitary e
  have hdiag : (star (V : Matrix E E ℂ)) * Q * (V : Matrix E E ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues) := by
    rw [permuteColumns_diagonalization, hQ.star_mul_self_mul_eq_diagonal,
      Matrix.submatrix_diagonal_equiv]
    ext i j
    simp [Matrix.diagonal, Function.comp_apply, he]
  refine ⟨hP.eigenvectorUnitary * star V, ?_⟩
  change P = ((hP.eigenvectorUnitary : Matrix E E ℂ) * star (V : Matrix E E ℂ)) * Q *
    star ((hP.eigenvectorUnitary : Matrix E E ℂ) * star (V : Matrix E E ℂ))
  rw [Matrix.star_mul, star_star]
  calc
    P = (hP.eigenvectorUnitary : Matrix E E ℂ) *
        Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues) *
        star (hP.eigenvectorUnitary : Matrix E E ℂ) := hP.spectral_theorem
    _ = _ := by rw [← hdiag]; simp only [Matrix.mul_assoc]

end
end ProjectionOrbit

