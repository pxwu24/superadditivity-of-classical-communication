import Antisymmetric.RevisionAntisymmetricProjection

/-! Orthonormality of the normalized Slater vectors, proved through the actual
 orthogonal projection matrix. -/
noncomputable section
open Finset Equiv
namespace AntisymmetricVerification
variable {k r : ℕ}

lemma pureTensor_standard (e x : TensorIndex k r) :
    pureTensor (fun j => standardVector (e j)) x = if e = x then 1 else 0 := by
  classical
  by_cases h : e = x
  · subst e
    simp [pureTensor, standardVector]
  · rw [if_neg h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (mem_univ j)
    simp [standardVector, hj]

lemma antisymMatrix_enum_apply (I : SubsetIndex k r) (x : TensorIndex k r) :
    antisymMatrix (subsetEnum I) x = (r.factorial : ℂ)⁻¹ * standardSlater I x := by
  simp only [antisymMatrix, standardSlater, slater_expansion]
  congr 1
  apply sum_congr rfl
  intro σ hσ
  rw [show ((fun j => standardVector (subsetEnum I j)) ∘ σ) =
    (fun j => standardVector ((subsetEnum I ∘ σ) j)) by rfl]
  rw [pureTensor_standard]

lemma antisymMatrix_flip (x y : TensorIndex k r) :
    antisymMatrix x y = star (antisymMatrix y x) := by
  exact (congrFun (congrFun antisymMatrix_isHermitian x) y).symm

/-- The unnormalized Slater family has Gram matrix `r! I`. -/
theorem standardSlater_gram (I J : SubsetIndex k r) :
    (∑ x : TensorIndex k r, star (standardSlater I x) * standardSlater J x) =
      (r.factorial : ℂ) * if I = J then 1 else 0 := by
  classical
  have h := congrFun (congrFun (antisymMatrix_idempotent (k := k) (r := r))
    (subsetEnum J)) (subsetEnum I)
  rw [Matrix.mul_apply] at h
  simp_rw [antisymMatrix_enum_apply, antisymMatrix_flip (y := subsetEnum I),
    antisymMatrix_enum_apply, star_mul, star_inv₀, star_natCast] at h
  have hrewrite : (∑ x : TensorIndex k r,
      ((r.factorial : ℂ)⁻¹ * standardSlater J x) *
        (star (standardSlater I x) * (r.factorial : ℂ)⁻¹)) =
      ((r.factorial : ℂ)⁻¹ * (r.factorial : ℂ)⁻¹) *
        ∑ x : TensorIndex k r, star (standardSlater I x) * standardSlater J x := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x hx
    ring
  rw [hrewrite, standardSlater_evaluation] at h
  have hf0 : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  by_cases hIJ : I = J
  · subst J
    simp only [ite_true] at h ⊢
    field_simp [hf0] at h
    simpa only [mul_one] using h
  · simp only [if_neg hIJ, if_neg (Ne.symm hIJ), mul_zero] at h ⊢
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (inv_ne_zero hf0) (inv_ne_zero hf0))

/-- Columns are the normalized standard Slater vectors in the full tensor
 coordinate space. -/
def slaterIsometry : Matrix (TensorIndex k r) (SubsetIndex k r) ℂ :=
  fun x I => ((Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹) * standardSlater I x

/-- Equation (59) really gives an orthonormal family; the normalization is
 checked rather than taken as an assumption. -/
theorem slaterIsometry_isometry :
    (slaterIsometry (k := k) (r := r)).conjTranspose *
      (slaterIsometry (k := k) (r := r)) = 1 := by
  classical
  have hs : 0 < Real.sqrt (r.factorial : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hs0 : (Real.sqrt (r.factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsq : (Real.sqrt (r.factorial : ℝ) : ℂ) * (Real.sqrt (r.factorial : ℝ) : ℂ) =
      (r.factorial : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (by positivity)
  ext I J
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, slaterIsometry, star_mul, star_inv₀, Complex.star_def,
    Complex.conj_ofReal]
  have hh : (∑ x : TensorIndex k r,
      (star (standardSlater I x) * (Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹) *
        ((Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹ * standardSlater J x)) =
      ((Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹ * (Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹) *
        ∑ x : TensorIndex k r, star (standardSlater I x) * standardSlater J x := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x hx
    ring
  change (∑ x : TensorIndex k r,
    (star (standardSlater I x) * (Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹) *
      ((Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹ * standardSlater J x)) = _
  rw [hh, standardSlater_gram]
  by_cases hIJ : I = J
  · simp only [if_pos hIJ, mul_one]
    rw [← hsq]
    field_simp
  · simp [hIJ]

end AntisymmetricVerification
