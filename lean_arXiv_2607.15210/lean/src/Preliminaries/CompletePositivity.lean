import Preliminaries.PreliminariesChoi

/-!
# Choi's theorem from positivity of genuine matrix amplifications

`CompletelyPositive` means positivity after tensoring with the identity on
every finite-dimensional ancillary space. It is not defined using the Choi
matrix. The proof constructs Kraus operators from a positive Choi square root.
-/

open scoped BigOperators ComplexOrder
open Matrix PreliminariesMatrix ProjectionChannels Classical

noncomputable section

namespace ProjectionChannelsCP

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

/-- Apply the map to every input block, keeping the ancillary indices. -/
def amplify (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (Y : Matrix (C × A) (C × A) ℂ) : Matrix (C × B) (C × B) ℂ :=
  fun ci dj => Φ (fun a b => Y (ci.1, a) (dj.1, b)) ci.2 dj.2

/-- Complete positivity, defined by positivity of all finite amplifications. -/
def CompletelyPositive (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C]
    (Y : Matrix (C × A) (C × A) ℂ),
    Y.PosSemidef → (amplify Φ Y).PosSemidef

/-- Choi inversion as an actual complex linear map. -/
def choiChannel (J : Matrix (A × B) (A × B) ℂ) :
    Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun := channel J
  map_add' X Y := by
    ext i j
    simp [channel, mul_add, Finset.sum_add_distrib]
  map_smul' z X := by
    ext i j
    simp [channel, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

/-- The unnormalized Bell vector as a one-column matrix. -/
def bellColumn [DecidableEq A] : Matrix (A × A) Unit ℂ :=
  fun p _ => if p.1 = p.2 then 1 else 0

theorem bell_block [DecidableEq A] (a b : A) :
    (fun r s => (bellColumn (A := A) * (bellColumn (A := A)).conjTranspose)
      (a, r) (b, s)) = matrixUnit a b := by
  ext r s
  by_cases hr : r = a <;> by_cases hs : s = b <;>
    simp_all [bellColumn, Matrix.mul_apply, Matrix.conjTranspose_apply,
      matrixUnit, hr, hs, eq_comm]

/-- Applying the input map to half of the unnormalized Bell matrix gives its Choi matrix. -/
theorem amplify_bell [DecidableEq A]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    amplify Φ (bellColumn (A := A) * (bellColumn (A := A)).conjTranspose) =
      choiInput Φ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [amplify, bell_block, choiInput]

/-- Complete positivity implies positivity of the Choi matrix. -/
theorem choi_posSemidef_of_completelyPositive [DecidableEq A]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (hΦ : CompletelyPositive Φ) :
    (choiInput Φ).PosSemidef := by
  have h := hΦ A
    (bellColumn (A := A) * (bellColumn (A := A)).conjTranspose)
    (Matrix.posSemidef_self_mul_conjTranspose _)
  simpa only [amplify_bell] using h

/-- Reshape a column of a Choi factor into a Kraus operator. -/
def krausOperator (S : Matrix (A × B) D ℂ) (r : D) : Matrix B A ℂ :=
  fun i a => S (a, i) r

/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_sum {E : Type} [Fintype E]
    (M : E → Matrix C C ℂ) (hM : ∀ e, (M e).PosSemidef) :
    (∑ e, M e).PosSemidef := by
  classical
  exact Finset.sum_induction M (fun N => N.PosSemidef)
    (fun _ _ hN hP => hN.add hP) Matrix.PosSemidef.zero (fun e _ => hM e)

/-- Expanding a Choi Gram factor gives the Kraus representation. -/
theorem channel_gram_kraus (S : Matrix (A × B) D ℂ) (X : Matrix A A ℂ) :
    channel (S * S.conjTranspose) X =
      ∑ r : D, krausOperator S r * X * (krausOperator S r).conjTranspose := by
  ext i j
  simp only [channel, Matrix.mul_apply, Matrix.conjTranspose_apply, krausOperator,
    Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- A Kraus term amplifies to a congruence by `I ⊗ K`. -/
theorem amplified_kraus_term [DecidableEq C]
    (K : Matrix B A ℂ) (Y : Matrix (C × A) (C × A) ℂ) :
    (fun (ci dj : C × B) => (K * Matrix.of (fun a b => Y (ci.1, a) (dj.1, b)) * K.conjTranspose)
      ci.2 dj.2) =
      Matrix.kronecker (1 : Matrix C C ℂ) K * Y *
        (Matrix.kronecker (1 : Matrix C C ℂ) K).conjTranspose := by
  ext ⟨c, i⟩ ⟨d, j⟩
  simp [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, apply_ite]

/-- Every finite Kraus representation is completely positive by congruence positivity. -/
theorem completelyPositive_of_kraus
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (K : D → Matrix B A ℂ)
    (hK : ∀ X, Φ X = ∑ r : D, K r * X * (K r).conjTranspose) :
    CompletelyPositive Φ := by
  intro C _ _ Y hY
  have hamp : amplify Φ Y =
      ∑ r : D, Matrix.kronecker (1 : Matrix C C ℂ) (K r) * Y *
        (Matrix.kronecker (1 : Matrix C C ℂ) (K r)).conjTranspose := by
    ext ⟨c, i⟩ ⟨d, j⟩
    simp only [amplify, hK, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro r hr
    exact congrArg (fun M => M (c, i) (d, j)) (amplified_kraus_term (K r) Y)
  rw [hamp]
  exact posSemidef_sum _ (fun r => hY.mul_mul_conjTranspose_same _)

/-- A positive semidefinite Choi matrix yields a completely positive map. -/
theorem completelyPositive_of_choi_posSemidef [DecidableEq A] [DecidableEq B]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (hJ : (choiInput Φ).PosSemidef) :
    CompletelyPositive Φ := by
  let S := hJ.sqrt
  have hS : S * S.conjTranspose = choiInput Φ := by
    rw [hJ.posSemidef_sqrt.isHermitian.eq]
    exact hJ.sqrt_mul_self
  apply completelyPositive_of_kraus Φ (krausOperator S)
  intro X
  rw [← channel_gram_kraus, hS]
  exact (choi_reconstructs_linearMap Φ X).symm

/-- Choi's theorem for actual complex linear maps and all finite amplifications. -/
theorem completelyPositive_iff_choi_posSemidef [DecidableEq A] [DecidableEq B]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    CompletelyPositive Φ ↔ (choiInput Φ).PosSemidef :=
  ⟨choi_posSemidef_of_completelyPositive Φ, completelyPositive_of_choi_posSemidef Φ⟩

/-- Trace preservation on every matrix, not merely positive inputs. -/
def TracePreserving (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) : Prop :=
  ∀ X, Matrix.trace (Φ X) = Matrix.trace X

theorem tracePreserving_iff_choi_partialTrace [DecidableEq A]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    TracePreserving Φ ↔ traceB (choiInput Φ) = 1 := by
  constructor
  · intro h
    ext a b
    have hab := h (matrixUnit a b)
    simpa [traceB, choiInput, Matrix.trace, Matrix.diag,
      matrixUnit, Matrix.one_apply, ite_and] using hab
  · intro h X
    rw [← choi_reconstructs_linearMap Φ X]
    exact channel_trace_preserving _ h X

/-- The standard Choi criterion for a completely positive, trace preserving channel. -/
theorem quantumChannel_iff_choi [DecidableEq A] [DecidableEq B]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    (CompletelyPositive Φ ∧ TracePreserving Φ) ↔
      ((choiInput Φ).PosSemidef ∧ traceB (choiInput Φ) = 1) := by
  rw [completelyPositive_iff_choi_posSemidef, tracePreserving_iff_choi_partialTrace]

theorem choiInput_choiChannel [DecidableEq A]
    (J : Matrix (A × B) (A × B) ℂ) : choiInput (choiChannel J) = J := by
  ext ⟨a, i⟩ ⟨b, j⟩
  exact choi_recovery J a b i j

/-- The actual inverse-square-root normalization used in the manuscript. -/
def generalizedChoi [DecidableEq A] [DecidableEq B]
    (R : Matrix (A × B) (A × B) ℂ) (hRA : (traceB R).PosDef) :
    Matrix (A × B) (A × B) ℂ :=
  let H := hRA.posSemidef.sqrt⁻¹
  Matrix.kronecker H (1 : Matrix B B ℂ) * R *
    Matrix.kronecker H (1 : Matrix B B ℂ)

/-- A positive generalized Choi operator with positive definite marginal gives
a genuine completely positive, trace preserving map. -/
theorem generalizedChoi_is_quantumChannel [DecidableEq A] [DecidableEq B]
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef)
    (hRA : (traceB R).PosDef) :
    CompletelyPositive (choiChannel (generalizedChoi R hRA)) ∧
      TracePreserving (choiChannel (generalizedChoi R hRA)) := by
  rw [quantumChannel_iff_choi, choiInput_choiChannel]
  exact inverse_sqrt_normalized_choi R hR hRA

/-- Multiplication by a nonnegative real scalar preserves matrix positivity. -/
theorem posSemidef_real_smul (M : Matrix A A ℂ) (hM : M.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c) : ((c : ℂ) • M).PosSemidef := by
  constructor
  · change ((c : ℂ) • M).conjTranspose = (c : ℂ) • M
    simp [Matrix.conjTranspose_smul, hM.isHermitian.eq]
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (Complex.zero_le_real.mpr hc) (hM.2 x)

/-- A strictly positive real scaling preserves positive definiteness. -/
theorem posDef_real_smul (M : Matrix A A ℂ) (hM : M.PosDef)
    (c : ℝ) (hc : 0 < c) : ((c : ℂ) • M).PosDef := by
  constructor
  · change ((c : ℂ) • M).conjTranspose = (c : ℂ) • M
    simp [Matrix.conjTranspose_smul, hM.isHermitian.eq]
  · intro x hx
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_pos (Complex.zero_lt_real.mpr hc) (hM.2 x hx)

theorem traceB_smul (R : Matrix (A × B) (A × B) ℂ) (c : ℂ) :
    traceB (c • R) = c • traceB R := by
  ext a b
  simp [traceB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The positive square root scales by the square root of a nonnegative scalar. -/
theorem positive_sqrt_real_smul [DecidableEq A]
    (M : Matrix A A ℂ) (hM : M.PosSemidef) (c : ℝ) (hc : 0 ≤ c) :
    (posSemidef_real_smul M hM c hc).sqrt = (Real.sqrt c : ℂ) • hM.sqrt := by
  symm
  apply (posSemidef_real_smul hM.sqrt hM.posSemidef_sqrt
    (Real.sqrt c) (Real.sqrt_nonneg c)).eq_sqrt_of_sq_eq
  rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hM.sqrt_mul_self]
  simp only [← Complex.ofReal_mul, Real.mul_self_sqrt hc]

/-- The rescaled operator has a strictly positive input marginal. -/
theorem scaled_marginal_posDef [DecidableEq A]
    (R : Matrix (A × B) (A × B) ℂ) (hRA : (traceB R).PosDef)
    (c : ℝ) (hc : 0 < c) : (traceB ((c : ℂ) • R)).PosDef := by
  rw [traceB_smul]
  exact posDef_real_smul (traceB R) hRA c hc

/-- Positive rescaling cancels exactly in the generalized Choi normalization. -/
theorem generalizedChoi_positive_rescaling [DecidableEq A] [DecidableEq B]
    (R : Matrix (A × B) (A × B) ℂ) (hRA : (traceB R).PosDef)
    (c : ℝ) (hc : 0 < c) :
    generalizedChoi ((c : ℂ) • R) (scaled_marginal_posDef R hRA c hc) =
      generalizedChoi R hRA := by
  let S := hRA.posSemidef.sqrt
  have hSsq : S * S = traceB R := hRA.posSemidef.sqrt_mul_self
  have hdet : IsUnit S.det := by
    have h : IsUnit (S.det * S.det) := by
      rw [← Matrix.det_mul, hSsq]
      exact (Matrix.isUnit_iff_isUnit_det _).mp hRA.isUnit
    exact (IsUnit.mul_iff.mp h).1
  have hsqrt : (scaled_marginal_posDef R hRA c hc).posSemidef.sqrt =
      (Real.sqrt c : ℂ) • S := by
    symm
    apply (posSemidef_real_smul S hRA.posSemidef.posSemidef_sqrt
      (Real.sqrt c) (Real.sqrt_nonneg c)).eq_sqrt_of_sq_eq
    rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hSsq, traceB_smul]
    simp only [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  have hr : (Real.sqrt c : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  have hinv : ((Real.sqrt c : ℂ) • S)⁻¹ =
      (Real.sqrt c : ℂ)⁻¹ • S⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      Matrix.nonsing_inv_mul S hdet, inv_mul_cancel₀ hr, one_smul]
  dsimp only [generalizedChoi]
  rw [hsqrt, hinv]
  simp only [Matrix.kronecker, Matrix.smul_kronecker]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hscalar : (Real.sqrt c : ℂ)⁻¹ * (c : ℂ) * (Real.sqrt c : ℂ)⁻¹ = 1 := by
    have hs : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = (c : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hc.le
    rw [← hs]
    field_simp
  rw [← mul_assoc, hscalar, one_smul]

end ProjectionChannelsCP

