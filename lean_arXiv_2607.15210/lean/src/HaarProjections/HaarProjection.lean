import Preliminaries.PreliminariesMatrix
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Gaussian whitening: deterministic part of the Haar-projection argument

The statements in this file establish the exact linear-algebraic reduction from
an injective matrix `G` to the orthogonal projection onto its column space.  They
are separate from the distributional assertion identifying this projection's
law with Haar measure on the Grassmannian.
-/

open scoped BigOperators ComplexOrder
open Matrix
open PreliminariesMatrix

namespace HaarProjection

noncomputable section
variable {A B D E : Type*} [Fintype A] [Fintype B] [Fintype D] [Fintype E]

/-- The projection obtained by whitening the Gram matrix of `G`. -/
def whitenedProjection [DecidableEq D] (G : Matrix E D ℂ) : Matrix E E ℂ :=
  G * (G.conjTranspose * G)⁻¹ * G.conjTranspose

/-- Full column rank is equivalent to injectivity of the matrix action. -/
theorem injective_of_full_column_rank (G : Matrix E D ℂ)
    (hG : G.rank = Fintype.card D) : Function.Injective G.mulVec := by
  have hd := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
  rw [← Matrix.rank, hG, Module.finrank_pi] at hd
  have hk : Module.finrank ℂ (LinearMap.ker G.mulVecLin) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The Gram matrix of an injective complex matrix is strictly positive. -/
theorem gram_posDef [DecidableEq E] (G : Matrix E D ℂ)
    (hG : Function.Injective G.mulVec) : (G.conjTranspose * G).PosDef := by
  simpa only [Matrix.mul_one] using
    (Matrix.PosDef.one : (1 : Matrix E E ℂ).PosDef).conjTranspose_mul_mul_same hG

/-- Whitening gives a positive semidefinite matrix. -/
theorem whitenedProjection_posSemidef [DecidableEq E] [DecidableEq D]
    (G : Matrix E D ℂ) (hG : Function.Injective G.mulVec) :
    (whitenedProjection G).PosSemidef :=
  (gram_posDef G hG).inv.posSemidef.mul_mul_conjTranspose_same G

/-- Whitening is the identity on the original column space. -/
theorem whitenedProjection_mul [DecidableEq E] [DecidableEq D]
    (G : Matrix E D ℂ) (hG : Function.Injective G.mulVec) :
    whitenedProjection G * G = G := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (gram_posDef G hG).isUnit
  simp only [whitenedProjection, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

/-- The whitened matrix is an orthogonal projection. -/
theorem whitenedProjection_idempotent [DecidableEq E] [DecidableEq D]
    (G : Matrix E D ℂ) (hG : Function.Injective G.mulVec) :
    whitenedProjection G * whitenedProjection G = whitenedProjection G := by
  conv_lhs => rhs; unfold whitenedProjection
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, whitenedProjection_mul G hG]
  rfl

/-- Whitening preserves the rank of the original column space. -/
theorem whitenedProjection_rank [DecidableEq E] [DecidableEq D]
    (G : Matrix E D ℂ) (hG : Function.Injective G.mulVec) :
    (whitenedProjection G).rank = G.rank := by
  exact posDef_congruence_rank G _ (gram_posDef G hG).inv

/-- The identity tensor a positive definite matrix is positive definite. -/
theorem one_kronecker_posDef [DecidableEq B] [DecidableEq D]
    (M : Matrix D D ℂ) (hM : M.PosDef) :
    (Matrix.kronecker (1 : Matrix B B ℂ) M).PosDef := by
  constructor
  · apply Matrix.IsHermitian.ext
    rintro ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      simpa [Matrix.kronecker, Matrix.kroneckerMap_apply] using hM.isHermitian.apply a b
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, hij, Ne.symm hij]
  · intro x hx
    have he : star x ⬝ᵥ (Matrix.kronecker (1 : Matrix B B ℂ) M) *ᵥ x =
        ∑ i : B, star (fun a : D => x (i, a)) ⬝ᵥ M *ᵥ (fun a : D => x (i, a)) := by
      simp [dotProduct, Matrix.mulVec, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Fintype.sum_prod_type]
    rw [he]
    obtain ⟨⟨i, a⟩, hi⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun j _ => hM.posSemidef.2 _) ?_
    refine ⟨i, Finset.mem_univ _, hM.2 _ ?_⟩
    intro hz
    apply hi
    exact congrFun hz a

/-- Whitening does not change the support rank of the input partial trace. -/
theorem whitenedProjection_partialTrace_rank [DecidableEq A] [DecidableEq B]
    [DecidableEq D] (G : Matrix (A × B) D ℂ)
    (hG : Function.Injective G.mulVec) :
    (traceB (whitenedProjection G)).rank = (flatten G).rank := by
  rw [whitenedProjection, reduced_weighted_gram]
  exact posDef_congruence_rank (flatten G) _
    (one_kronecker_posDef _ (gram_posDef G hG).inv)

/-- For a flattened matrix of full row rank, the reduced projection is strictly positive. -/
theorem whitenedProjection_partialTrace_posDef [DecidableEq A] [DecidableEq B]
    [DecidableEq D] (G : Matrix (A × B) D ℂ)
    (hG : Function.Injective G.mulVec)
    (hflat : (flatten G).rank = Fintype.card A) :
    (traceB (whitenedProjection G)).PosDef := by
  rw [whitenedProjection, reduced_weighted_gram]
  have hi : Function.Injective (flatten G).conjTranspose.mulVec :=
    injective_of_full_column_rank _ (by rwa [Matrix.rank_conjTranspose])
  simpa only [Matrix.conjTranspose_conjTranspose] using
    (one_kronecker_posDef (B := B) _ (gram_posDef G hG).inv).conjTranspose_mul_mul_same hi

/-- The exact dimension criterion, once the flattened matrix has maximal rank. -/
theorem whitenedProjection_partialTrace_posDef_iff [DecidableEq A] [DecidableEq B]
    [DecidableEq D] (G : Matrix (A × B) D ℂ)
    (hG : Function.Injective G.mulVec)
    (hflat : (flatten G).rank = min (Fintype.card A) (Fintype.card B * Fintype.card D)) :
    (traceB (whitenedProjection G)).PosDef ↔
      Fintype.card A ≤ Fintype.card B * Fintype.card D := by
  constructor
  · intro hp
    have hr := Matrix.rank_of_isUnit _ hp.isUnit
    rw [whitenedProjection_partialTrace_rank G hG, hflat] at hr
    omega
  · intro hn
    apply whitenedProjection_partialTrace_posDef G hG
    rwa [min_eq_left hn] at hflat

/-- Combining the two almost-sure Gaussian rank statements is a purely
measure-theoretic intersection step; no assertion about the law of `G` is assumed. -/
theorem ae_whitenedProjection_partialTrace_rank
    [DecidableEq A] [DecidableEq B] [DecidableEq D]
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (G : Ω → Matrix (A × B) D ℂ)
    (hcol : ∀ᵐ ω ∂μ, (G ω).rank = Fintype.card D)
    (hflat : ∀ᵐ ω ∂μ, (flatten (G ω)).rank =
      min (Fintype.card A) (Fintype.card B * Fintype.card D)) :
    ∀ᵐ ω ∂μ, (traceB (whitenedProjection (G ω))).rank =
      min (Fintype.card A) (Fintype.card B * Fintype.card D) := by
  filter_upwards [hcol, hflat] with ω hω hflatω
  rw [whitenedProjection_partialTrace_rank _ (injective_of_full_column_rank _ hω), hflatω]

/-- The full-local-support criterion on the same probability-one event. -/
theorem ae_whitenedProjection_partialTrace_posDef_iff
    [DecidableEq A] [DecidableEq B] [DecidableEq D]
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (G : Ω → Matrix (A × B) D ℂ)
    (hcol : ∀ᵐ ω ∂μ, (G ω).rank = Fintype.card D)
    (hflat : ∀ᵐ ω ∂μ, (flatten (G ω)).rank =
      min (Fintype.card A) (Fintype.card B * Fintype.card D)) :
    ∀ᵐ ω ∂μ, (traceB (whitenedProjection (G ω))).PosDef ↔
      Fintype.card A ≤ Fintype.card B * Fintype.card D := by
  filter_upwards [hcol, hflat] with ω hω hflatω
  exact whitenedProjection_partialTrace_posDef_iff _
    (injective_of_full_column_rank _ hω) hflatω

/-- Whitening is equivariant under left multiplication by a unitary matrix. -/
theorem whitenedProjection_unitary_equivariant [DecidableEq E] [DecidableEq D]
    (U : Matrix.unitaryGroup E ℂ) (G : Matrix E D ℂ) :
    whitenedProjection ((U : Matrix E E ℂ) * G) =
      (U : Matrix E E ℂ) * whitenedProjection G * (U : Matrix E E ℂ).conjTranspose := by
  have hU : (U : Matrix E E ℂ).conjTranspose * U = 1 := U.prop.1
  have hg : ((U : Matrix E E ℂ) * G).conjTranspose * ((U : Matrix E E ℂ) * G) =
      G.conjTranspose * G := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix E E ℂ).conjTranspose,
      hU, Matrix.one_mul]
  unfold whitenedProjection
  rw [hg]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A positive semidefinite matrix is strictly positive exactly when it has full rank. -/
theorem posDef_iff_full_rank [DecidableEq A] (M : Matrix A A ℂ) (hM : M.PosSemidef) :
    M.PosDef ↔ M.rank = Fintype.card A := by
  constructor
  · intro h
    exact Matrix.rank_of_isUnit M h.isUnit
  · intro hr
    have hrs : hM.sqrt.rank = Fintype.card A := by
      apply Nat.le_antisymm (Matrix.rank_le_card_width _)
      have hh := Matrix.rank_mul_le_left hM.sqrt hM.sqrt
      rwa [hM.sqrt_mul_self, hr] at hh
    have hp := gram_posDef hM.sqrt (injective_of_full_column_rank hM.sqrt hrs)
    rwa [hM.posSemidef_sqrt.isHermitian.eq, hM.sqrt_mul_self] at hp

/-- Partial trace preserves positive semidefiniteness. -/
theorem traceB_posSemidef [DecidableEq A] [DecidableEq B]
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef) :
    (traceB R).PosSemidef := by
  have he : traceB R = flatten hR.sqrt * (flatten hR.sqrt).conjTranspose := by
    calc
      traceB R = traceB (hR.sqrt * hR.sqrt.conjTranspose) := by
        rw [hR.posSemidef_sqrt.isHermitian.eq, hR.sqrt_mul_self]
      _ = _ := reduced_gram _
  rw [he]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Every Hermitian idempotent is positive semidefinite. -/
theorem projection_posSemidef (P : Matrix A A ℂ) (hP : P.IsHermitian)
    (hidem : P * P = P) : P.PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose P
  rwa [hP.eq, hidem] at h

/-- Unitary conjugation preserves the rank of every matrix. -/
theorem unitary_conjugation_rank [DecidableEq A]
    (U : Matrix.unitaryGroup A ℂ) (P : Matrix A A ℂ) :
    ((U : Matrix A A ℂ) * P * (U : Matrix A A ℂ).conjTranspose).rank = P.rank := by
  have hu := Matrix.UnitaryGroup.det_isUnit U
  have hu' : IsUnit (U : Matrix A A ℂ).conjTranspose.det := by
    simpa only [← Matrix.star_eq_conjTranspose, ← Matrix.UnitaryGroup.inv_val] using
      Matrix.UnitaryGroup.det_isUnit U⁻¹
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]

end
end HaarProjection

