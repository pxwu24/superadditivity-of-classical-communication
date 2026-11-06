import Antisymmetric.RevisionAntisymmetricBasis
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-! Change of one-particle eigenbasis on the actual finite tensor space. -/
noncomputable section
open Finset Equiv
namespace AntisymmetricVerification
variable {k r : ℕ}

/-- The actual tensor power matrix of a one-particle matrix. -/
def tensorMatrix (U : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (TensorIndex k r) (TensorIndex k r) ℂ :=
  fun x y => ∏ j, U (x j) (y j)

lemma tensorMatrix_mul (U V : Matrix (Fin k) (Fin k) ℂ) :
    tensorMatrix (r := r) (U * V) = tensorMatrix U * tensorMatrix V := by
  ext x y
  simp only [tensorMatrix, Matrix.mul_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

lemma tensorMatrix_one : tensorMatrix (r := r) (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext x y
  classical
  by_cases h : x = y
  · subst y
    simp [tensorMatrix]
  · have he : ∃ j, x j ≠ y j := Function.ne_iff.mp h
    obtain ⟨j, hj⟩ := he
    rw [Matrix.one_apply, if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

lemma tensorMatrix_pureTensor (U : Matrix (Fin k) (Fin k) ℂ)
    (v : Fin r → Fin k → ℂ) :
    (tensorMatrix U).mulVec (pureTensor v) = pureTensor (fun j => U.mulVec (v j)) := by
  ext x
  simp only [Matrix.mulVec, dotProduct, tensorMatrix, pureTensor,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (j : Fin r) (a : Fin k) => U (x j) a * v j a)).symm

lemma mulVec_fintype_sum {ι : Type*} [Fintype ι]
    (M : Matrix (TensorIndex k r) (TensorIndex k r) ℂ)
    (f : ι → TensorVector k r) : M.mulVec (∑ i, f i) = ∑ i, M.mulVec (f i) := by
  exact map_sum M.mulVecLin f univ

lemma slater_expansion_vector (v : Fin r → Fin k → ℂ) :
    slater v = ∑ σ : Perm (Fin r), signC σ • pureTensor (v ∘ σ) := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, slater_expansion]

lemma tensorMatrix_slater (U : Matrix (Fin k) (Fin k) ℂ)
    (v : Fin r → Fin k → ℂ) :
    (tensorMatrix U).mulVec (slater v) = slater (fun j => U.mulVec (v j)) := by
  simp only [slater_expansion_vector, mulVec_fintype_sum, Matrix.mulVec_smul,
    tensorMatrix_pureTensor, Function.comp_def]

lemma standardVector_eq_single (a : Fin k) : standardVector a = Pi.single a 1 := by
  ext b
  simp [standardVector, Pi.single_apply, eq_comm]

lemma tensorMatrix_standardSlater (U : Matrix (Fin k) (Fin k) ℂ)
    (I : SubsetIndex k r) :
    (tensorMatrix U).mulVec (standardSlater I) =
      slater (fun j b => U b (subsetEnum I j)) := by
  rw [standardSlater, tensorMatrix_slater]
  simp only [standardVector_eq_single, Matrix.mulVec_single_one]
  rfl

lemma alternating_sum_smul {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → TensorVector k r) (hf : ∀ i, alternating (f i)) :
    alternating (∑ i, c i • f i) := by
  intro σ
  ext x
  simp only [permute, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro i hi
  have h := congrFun (hf i σ) x
  simp only [permute, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  ring

lemma alternating_expansion_vector {f : TensorVector k r} (hf : alternating f) :
    f = ∑ I : SubsetIndex k r, f (subsetEnum I) • standardSlater I := by
  classical
  calc
    f = (fun x => ∑ I : SubsetIndex k r, f (subsetEnum I) * standardSlater I x) :=
      alternating_slater_expansion hf
    _ = _ := by
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma tensorMatrix_preserves_alternating (U : Matrix (Fin k) (Fin k) ℂ)
    {f : TensorVector k r} (hf : alternating f) :
    alternating ((tensorMatrix U).mulVec f) := by
  rw [alternating_expansion_vector hf]
  simp only [mulVec_fintype_sum, Matrix.mulVec_smul, tensorMatrix_standardSlater]
  exact alternating_sum_smul _ _ (fun _ => slater_alternating _)

/-- Slater vectors obtained by any invertible change of one-body basis remain
 a complete basis of the alternating tensor space. -/
theorem transformedSlater_expansion (U V : Matrix (Fin k) (Fin k) ℂ)
    (hUV : U * V = 1) {f : TensorVector k r} (hf : alternating f) :
    f = ∑ I : SubsetIndex k r,
      ((tensorMatrix V).mulVec f) (subsetEnum I) •
        slater (fun j b => U b (subsetEnum I j)) := by
  have h := alternating_expansion_vector (tensorMatrix_preserves_alternating V hf)
  have hh := congrArg (Matrix.mulVec (tensorMatrix U)) h
  rw [Matrix.mulVec_mulVec, ← tensorMatrix_mul, hUV, tensorMatrix_one, Matrix.one_mulVec] at hh
  simpa only [mulVec_fintype_sum, Matrix.mulVec_smul, tensorMatrix_standardSlater] using hh

lemma tensorMatrix_mulVec_injective (U V : Matrix (Fin k) (Fin k) ℂ)
    (hVU : V * U = 1) : Function.Injective (Matrix.mulVec (tensorMatrix (r := r) U)) := by
  intro f g h
  have hh := congrArg (Matrix.mulVec (tensorMatrix V)) h
  simpa only [Matrix.mulVec_mulVec, ← tensorMatrix_mul, hVU, tensorMatrix_one,
    Matrix.one_mulVec] using hh

/-- The transformed Slater family has no linear dependencies. -/
theorem transformedSlater_linearIndependent (U V : Matrix (Fin k) (Fin k) ℂ)
    (hVU : V * U = 1) :
    LinearIndependent ℂ (fun I : SubsetIndex k r =>
      slater (fun j b => U b (subsetEnum I j))) := by
  classical
  have hinj := tensorMatrix_mulVec_injective (r := r) U V hVU
  have hlin := standardSlater_linearIndependent (k := k) (r := r)
  have h := hlin.map' (tensorMatrix U).mulVecLin (LinearMap.ker_eq_bot.mpr hinj)
  simpa only [Function.comp_def, Matrix.mulVecLin_apply, tensorMatrix_standardSlater] using h

end AntisymmetricVerification
