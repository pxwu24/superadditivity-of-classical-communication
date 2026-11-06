import HaarProjections.GaussianMatrixLaw
import HaarProjections.HaarProjection
import StrongConvergence.StrongConvergenceCompressionBounds

/-!
# Stability of Gaussian whitening on lower-frame sets

All statements here concern the actual rectangular matrix and its whitened
orthogonal projection. The lower-frame hypothesis is deterministic; no
probability estimate or strong-convergence statement is assumed.
-/

open Matrix HaarProjection ProjectionChannels GaussianRank
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section

namespace StrongConvergence

variable {E D F : Type*} [Fintype E] [Fintype D] [Fintype F]
  [DecidableEq E] [DecidableEq D] [DecidableEq F]

/-- A positive lower bound for the smallest singular value, expressed
directly on Euclidean vectors. -/
def LowerFrame (s : ℝ) (G : Matrix E D ℂ) : Prop :=
  ∀ v : EuclideanSpace ℂ D, s * ‖v‖ ≤ ‖Matrix.toEuclideanLin G v‖

omit [DecidableEq E] in
lemma LowerFrame.mono {s r : ℝ} {G : Matrix E D ℂ}
    (h : LowerFrame s G) (hrs : r ≤ s) : LowerFrame r G :=
  fun v => (mul_le_mul_of_nonneg_right hrs (norm_nonneg v)).trans (h v)

omit [Fintype E] [DecidableEq E] in
lemma continuous_toEuclideanLin_apply (v : EuclideanSpace ℂ D) :
    Continuous (fun G : Matrix E D ℂ => Matrix.toEuclideanLin G v) := by
  change Continuous (fun G : Matrix E D ℂ =>
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : E => ℂ)).symm (G *ᵥ v))
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : E => ℂ)).symm.continuous.comp
    (continuous_id.matrix_mulVec continuous_const)

omit [DecidableEq E] in
theorem isClosed_lowerFrame (s : ℝ) : IsClosed {G : Matrix E D ℂ | LowerFrame s G} := by
  simp only [LowerFrame, Set.setOf_forall]
  apply isClosed_iInter
  intro v
  exact isClosed_le continuous_const (continuous_toEuclideanLin_apply v).norm

omit [Fintype E] [DecidableEq E] in
lemma toEuclideanLin_mul_apply (A : Matrix E D ℂ) (B : Matrix D F ℂ)
    (v : EuclideanSpace ℂ F) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  ext i
  exact congrFun (Matrix.mulVec_mulVec v A B).symm i

omit [DecidableEq E] in
lemma matrix_opNorm_le_of_bound (A : Matrix E D ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ v : EuclideanSpace ℂ D, ‖Matrix.toEuclideanLin A v‖ ≤ C * ‖v‖) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hC h

omit [DecidableEq E] in
lemma toEuclideanLin_norm_le (A : Matrix E D ℂ) (v : EuclideanSpace ℂ D) :
    ‖Matrix.toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ :=
  Matrix.l2_opNorm_mulVec A v

omit [DecidableEq E] in
lemma LowerFrame.injective {s : ℝ} (hs : 0 < s) {G : Matrix E D ℂ}
    (hG : LowerFrame s G) : Function.Injective G.mulVec := by
  change Function.Injective (G.mulVecLin : (D → ℂ) → (E → ℂ))
  apply (LinearMap.ker_eq_bot).mp
  apply (LinearMap.ker_eq_bot').mpr
  intro v hv
  have h := hG ((WithLp.equiv 2 (D → ℂ)).symm v)
  have hz : Matrix.toEuclideanLin G ((WithLp.equiv 2 (D → ℂ)).symm v) = 0 := by
    ext i
    exact congrFun hv i
  rw [hz, norm_zero] at h
  have hvnorm : ‖(WithLp.equiv 2 (D → ℂ)).symm v‖ = 0 := by
    nlinarith [norm_nonneg ((WithLp.equiv 2 (D → ℂ)).symm v)]
  have hvzero := norm_eq_zero.mp hvnorm
  exact congrArg (WithLp.equiv 2 (D → ℂ)) hvzero

/-- Every orthogonal projection is a contraction, including zero-dimensional
index types. -/
lemma hermitian_idempotent_norm_le_one (P : Matrix E E ℂ)
    (hP : P.IsHermitian) (hId : P * P = P) : ‖P‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hP.eq, hId] at h
  nlinarith [norm_nonneg P]

lemma hermitian_idempotent_complement_norm_le_one (P : Matrix E E ℂ)
    (hP : P.IsHermitian) (hId : P * P = P) : ‖1 - P‖ ≤ 1 := by
  apply hermitian_idempotent_norm_le_one _ (Matrix.isHermitian_one.sub hP)
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hId]
  abel

lemma whitenedProjection_norm_le_one (G : Matrix E D ℂ)
    (hG : Function.Injective G.mulVec) : ‖whitenedProjection G‖ ≤ 1 :=
  hermitian_idempotent_norm_le_one _ (whitenedProjection_posSemidef G hG).isHermitian
    (whitenedProjection_idempotent G hG)

lemma whitenedProjection_complement_norm_le_one (G : Matrix E D ℂ)
    (hG : Function.Injective G.mulVec) : ‖1 - whitenedProjection G‖ ≤ 1 :=
  hermitian_idempotent_complement_norm_le_one _
    (whitenedProjection_posSemidef G hG).isHermitian (whitenedProjection_idempotent G hG)

omit [DecidableEq E] in
/-- The repository's nonsingular inverse convention makes whitening zero
when the rectangular matrix does not have full column rank. -/
theorem whitenedProjection_eq_zero_of_not_injective (G : Matrix E D ℂ)
    (hG : ¬ Function.Injective G.mulVec) : whitenedProjection G = 0 := by
  have hdet : ¬ IsUnit (G.conjTranspose * G).det := by
    intro h
    have hi := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr h)
    apply hG
    intro x y hxy
    apply hi
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  rw [whitenedProjection,
    Matrix.nonsing_inv_apply_not_isUnit (A := G.conjTranspose * G) hdet, Matrix.mul_zero,
    Matrix.zero_mul]

theorem whitenedProjection_isHermitian_all (G : Matrix E D ℂ) :
    (whitenedProjection G).IsHermitian := by
  by_cases hi : Function.Injective G.mulVec
  · exact (whitenedProjection_posSemidef G hi).isHermitian
  · rw [whitenedProjection_eq_zero_of_not_injective G hi]
    exact Matrix.isHermitian_zero

theorem whitenedProjection_idempotent_all (G : Matrix E D ℂ) :
    whitenedProjection G * whitenedProjection G = whitenedProjection G := by
  by_cases hi : Function.Injective G.mulVec
  · exact whitenedProjection_idempotent G hi
  · simp only [whitenedProjection_eq_zero_of_not_injective G hi, Matrix.zero_mul]

theorem whitenedProjection_norm_le_one_all (G : Matrix E D ℂ) :
    ‖whitenedProjection G‖ ≤ 1 :=
  hermitian_idempotent_norm_le_one _ (whitenedProjection_isHermitian_all G)
    (whitenedProjection_idempotent_all G)

/-- The left pseudoinverse used in the definition of Gaussian whitening. -/
def whiteningInverse (G : Matrix E D ℂ) : Matrix D E ℂ :=
  (G.conjTranspose * G)⁻¹ * G.conjTranspose

omit [DecidableEq E] in
lemma mul_whiteningInverse (G : Matrix E D ℂ) :
    G * whiteningInverse G = whitenedProjection G := by
  simp only [whiteningInverse, whitenedProjection, Matrix.mul_assoc]

/-- A lower frame bound controls the operator norm of the left pseudoinverse. -/
theorem whiteningInverse_norm_le {s : ℝ} (hs : 0 < s) {G : Matrix E D ℂ}
    (hG : LowerFrame s G) : ‖whiteningInverse G‖ ≤ s⁻¹ := by
  have hi := hG.injective hs
  apply matrix_opNorm_le_of_bound _ _ (inv_nonneg.mpr hs.le)
  intro v
  have h := hG (Matrix.toEuclideanLin (whiteningInverse G) v)
  rw [← toEuclideanLin_mul_apply, mul_whiteningInverse] at h
  have hPv : ‖Matrix.toEuclideanLin (whitenedProjection G) v‖ ≤ ‖v‖ :=
    (toEuclideanLin_norm_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg v) (whitenedProjection_norm_le_one G hi))
  have hh : s * ‖Matrix.toEuclideanLin (whiteningInverse G) v‖ ≤ ‖v‖ := h.trans hPv
  calc
    ‖Matrix.toEuclideanLin (whiteningInverse G) v‖ ≤ ‖v‖ / s := by
      apply (le_div_iff₀ hs).mpr
      simpa only [mul_comm] using hh
    _ = s⁻¹ * ‖v‖ := by rw [div_eq_mul_inv, mul_comm]

lemma one_sub_whitenedProjection_mul (G : Matrix E D ℂ)
    (hG : Function.Injective G.mulVec) : (1 - whitenedProjection G) * G = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, whitenedProjection_mul G hG, sub_self]

/-- The cross-projection error factors through the rectangular matrix error. -/
theorem whitening_cross_error (G H : Matrix E D ℂ)
    (hH : Function.Injective H.mulVec) :
    (1 - whitenedProjection H) * whitenedProjection G =
      (1 - whitenedProjection H) * (G-H) * whiteningInverse G := by
  symm
  rw [Matrix.mul_sub, one_sub_whitenedProjection_mul H hH, sub_zero,
    Matrix.mul_assoc, mul_whiteningInverse]

lemma hermitian_projection_difference (P Q : Matrix E E ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    P-Q = (1-Q)*P - ((1-P)*Q).conjTranspose := by
  rw [Matrix.conjTranspose_mul, hQ.eq, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hP.eq]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  abel

theorem whitening_cross_error_norm_le {s : ℝ} (hs : 0 < s)
    {G H : Matrix E D ℂ} (hG : LowerFrame s G)
    (hH : Function.Injective H.mulVec) :
    ‖(1 - whitenedProjection H) * whitenedProjection G‖ ≤ ‖G-H‖ * s⁻¹ := by
  rw [whitening_cross_error G H hH]
  have hprod : ‖(1 - whitenedProjection H) * (G-H)‖ ≤ ‖G-H‖ :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (whitenedProjection_complement_norm_le_one H hH))
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul hprod (whiteningInverse_norm_le hs hG) (norm_nonneg _) (norm_nonneg _))

/-- Whitening is Lipschitz whenever both smallest singular values stay
positive. The constants are independent of both matrix dimensions. -/
theorem norm_whitenedProjection_sub_le {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    {G H : Matrix E D ℂ} (hG : LowerFrame s G) (hH : LowerFrame s' H) :
    ‖whitenedProjection G - whitenedProjection H‖ ≤ ‖G-H‖ * (s⁻¹+s'⁻¹) := by
  have hiG := hG.injective hs
  have hiH := hH.injective hs'
  rw [hermitian_projection_difference _ _
    (whitenedProjection_posSemidef G hiG).isHermitian
    (whitenedProjection_posSemidef H hiH).isHermitian]
  calc
    _ ≤ ‖(1 - whitenedProjection H) * whitenedProjection G‖ +
        ‖((1 - whitenedProjection G) * whitenedProjection H).conjTranspose‖ := norm_sub_le _ _
    _ = ‖(1 - whitenedProjection H) * whitenedProjection G‖ +
        ‖(1 - whitenedProjection G) * whitenedProjection H‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
    _ ≤ ‖G-H‖ * s⁻¹ + ‖H-G‖ * s'⁻¹ :=
      add_le_add (whitening_cross_error_norm_le hs hG hiH)
        (whitening_cross_error_norm_le hs' hH hiG)
    _ = ‖G-H‖ * (s⁻¹+s'⁻¹) := by rw [norm_sub_rev H G]; ring

theorem norm_whitenedProjection_sub_le_common {s : ℝ} (hs : 0 < s)
    {G H : Matrix E D ℂ} (hG : LowerFrame s G) (hH : LowerFrame s H) :
    ‖whitenedProjection G - whitenedProjection H‖ ≤ (2/s) * ‖G-H‖ := by
  convert norm_whitenedProjection_sub_le hs hs hG hH using 1
  ring

theorem norm_whitenedProjection_sub_le_min {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    {G H : Matrix E D ℂ} (hG : LowerFrame s G) (hH : LowerFrame s' H) :
    ‖whitenedProjection G - whitenedProjection H‖ ≤ (2 / min s s') * ‖G-H‖ :=
  norm_whitenedProjection_sub_le_common (lt_min hs hs')
    (hG.mono (min_le_left _ _)) (hH.mono (min_le_right _ _))

omit [DecidableEq E] in
/-- The Euclidean Gaussian coordinate norm controls the matrix operator
norm. This is the operator/Hilbert--Schmidt comparison without changing the
matrix norm instance. -/
theorem matrixCoordinates_opNorm_le (x : EuclideanSpace ℂ (E × D)) :
    ‖matrixCoordinates E D x‖ ≤ ‖x‖ := by
  apply matrix_opNorm_le_of_bound _ _ (norm_nonneg _)
  intro v
  have hrow (i : E) :
      ‖∑ j : D, x (i,j) * v j‖ ^ 2 ≤
        (∑ j : D, ‖x (i,j)‖ ^ 2) * (∑ j : D, ‖v j‖ ^ 2) := by
    have hn : ‖∑ j : D, x (i,j) * v j‖ ≤ ∑ j : D, ‖x (i,j)‖ * ‖v j‖ := by
      simpa only [norm_mul] using norm_sum_le (s := Finset.univ) (fun j : D => x (i,j)*v j)
    have hn0 : 0 ≤ ∑ j : D, ‖x (i,j)‖ * ‖v j‖ := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) hn0).mpr hn |>.trans
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : D => ‖x (i,j)‖) (fun j : D => ‖v j‖)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset E)) => hrow i)
  have heq : ‖Matrix.toEuclideanLin (matrixCoordinates E D x) v‖ ^ 2 ≤
      (‖x‖ * ‖v‖)^2 := by
    simpa only [PiLp.norm_sq_eq_of_L2, Matrix.toEuclideanLin_apply,
      Matrix.mulVec, dotProduct, matrixCoordinates_apply, WithLp.equiv_symm_pi_apply,
      WithLp.equiv_pi_apply, Fintype.sum_prod_type, ← Finset.sum_mul, mul_pow] using hsum
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp heq

omit [DecidableEq E] in
theorem matrixCoordinates_opNorm_sub_le (x y : EuclideanSpace ℂ (E × D)) :
    ‖matrixCoordinates E D x - matrixCoordinates E D y‖ ≤ ‖x-y‖ := by
  simpa only [map_sub] using matrixCoordinates_opNorm_le (x-y)

/-- The actual whitening map is Lipschitz on a fixed lower-frame set in
the Euclidean Gaussian coordinates. -/
theorem whitening_lipschitzOn {s : ℝ} (hs : 0 < s) :
    LipschitzOnWith ⟨2/s, by positivity⟩
      (fun x : EuclideanSpace ℂ (E × D) => whitenedProjection (matrixCoordinates E D x))
      {x | LowerFrame s (matrixCoordinates E D x)} := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  simp only [dist_eq_norm, NNReal.coe_mk]
  exact (norm_whitenedProjection_sub_le_common hs hx hy).trans
    (mul_le_mul_of_nonneg_left (matrixCoordinates_opNorm_sub_le x y) (by positivity))

omit [Fintype D] in
lemma rowRestriction_mul_conjTranspose (f : D → E) (hf : Function.Injective f) :
    (1 : Matrix E E ℂ).submatrix f id *
      ((1 : Matrix E E ℂ).submatrix f id).conjTranspose = 1 := by
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : Matrix E E ℂ).submatrix f (Equiv.refl E) *
    (1 : Matrix E E ℂ).submatrix id f = 1
  rw [Matrix.one_submatrix_mul]
  simpa only [Equiv.refl_symm, Equiv.refl_apply, Function.id_comp,
    Matrix.submatrix_submatrix, Function.comp_id] using Matrix.submatrix_one f hf (α := ℂ)

lemma rowRestriction_norm_le_one (f : D → E) (hf : Function.Injective f) :
    ‖(1 : Matrix E E ℂ).submatrix f id‖ ≤ 1 := by
  let R := (1 : Matrix E E ℂ).submatrix f id
  have h := Matrix.l2_opNorm_conjTranspose_mul_self R.conjTranspose
  rw [Matrix.conjTranspose_conjTranspose, rowRestriction_mul_conjTranspose f hf,
    Matrix.l2_opNorm_conjTranspose] at h
  have h1 := hermitian_idempotent_norm_le_one (1 : Matrix D D ℂ)
    Matrix.isHermitian_one (by simp)
  nlinarith [norm_nonneg R]

/-- Compression to any coordinate subspace is contractive in operator norm. -/
theorem principal_submatrix_opNorm_le (M : Matrix E E ℂ)
    (f : D → E) (hf : Function.Injective f) : ‖M.submatrix f f‖ ≤ ‖M‖ := by
  let R := (1 : Matrix E E ℂ).submatrix f id
  have hrepr : R * M * R.conjTranspose = M.submatrix f f := by
    dsimp [R]
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    change (1 : Matrix E E ℂ).submatrix f (Equiv.refl E) * M *
      (1 : Matrix E E ℂ).submatrix (Equiv.refl E) f = _
    rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one]
    rfl
  rw [← hrepr]
  have hR : ‖R‖ ≤ 1 := rowRestriction_norm_le_one f hf
  calc
    _ ≤ ‖R*M‖ * ‖R.conjTranspose‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖R‖ * ‖M‖) * ‖R.conjTranspose‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖M‖) * 1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = ‖M‖ := by ring

theorem diagonalBlock_opNorm_le (M : Matrix (E × D) (E × D) ℂ) (i : D) :
    ‖diagonalBlock M i‖ ≤ ‖M‖ :=
  principal_submatrix_opNorm_le M (fun e => (e,i)) (fun _ _ h => (Prod.mk.inj h).1)

/-- Weighted diagonal block compression has operator Lipschitz constant
equal to the sum of absolute coefficients. No positivity is needed. -/
theorem blockCompression_opNorm_le (M : Matrix (E × D) (E × D) ℂ) (a : D → ℝ) :
    ‖blockCompression (diagonalBlock M) a‖ ≤ (∑ i, |a i|) * ‖M‖ := by
  rw [blockCompression, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (diagonalBlock_opNorm_le M i) (abs_nonneg _)

omit [Fintype E] [DecidableEq E] [DecidableEq D] in
lemma blockCompression_sub (P Q : Matrix (E × D) (E × D) ℂ) (a : D → ℝ) :
    blockCompression (diagonalBlock (P-Q)) a =
      blockCompression (diagonalBlock P) a - blockCompression (diagonalBlock Q) a := by
  simp only [blockCompression, diagonalBlock, Matrix.submatrix_sub, Pi.sub_apply, smul_sub,
    Finset.sum_sub_distrib]

theorem blockCompression_opNorm_sub_le (P Q : Matrix (E × D) (E × D) ℂ)
    (a : D → ℝ) :
    ‖blockCompression (diagonalBlock P) a - blockCompression (diagonalBlock Q) a‖ ≤
      (∑ i, |a i|) * ‖P-Q‖ := by
  rw [← blockCompression_sub]
  exact blockCompression_opNorm_le _ _

/-- Every affine norm test of the block compression is Lipschitz with the
same dimension-independent coefficient norm. -/
theorem affineCompressionNorm_lipschitz (P Q : Matrix (E × D) (E × D) ℂ)
    (a : D → ℝ) (c : ℝ) :
    |‖(c : ℂ) • (1 : Matrix E E ℂ) + blockCompression (diagonalBlock P) a‖ -
      ‖(c : ℂ) • (1 : Matrix E E ℂ) + blockCompression (diagonalBlock Q) a‖| ≤
      (∑ i, |a i|) * ‖P-Q‖ := by
  apply (abs_norm_sub_norm_le _ _).trans
  have heq : (c : ℂ) • (1 : Matrix E E ℂ) + blockCompression (diagonalBlock P) a -
      ((c : ℂ) • (1 : Matrix E E ℂ) + blockCompression (diagonalBlock Q) a) =
      blockCompression (diagonalBlock P) a - blockCompression (diagonalBlock Q) a := by abel
  rw [heq]
  exact blockCompression_opNorm_sub_le _ _ _

/-- The same coefficient constant controls the largest eigenvalue for
orthogonal projection inputs. A common positive shift reduces this to the
already verified affine-norm estimate. -/
theorem largestCompression_lipschitz [Nonempty E]
    (P Q : Matrix (E × D) (E × D) ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPId : P*P = P) (hQId : Q*Q = Q) (a : D → ℝ) :
    |largestEigenvalue (blockCompression_isHermitian (diagonalBlock P)
        (fun i => hP.submatrix (fun e => (e,i))) a) -
      largestEigenvalue (blockCompression_isHermitian (diagonalBlock Q)
        (fun i => hQ.submatrix (fun e => (e,i))) a)| ≤
      (∑ i, |a i|) * ‖P-Q‖ := by
  have hCP := blockCompression_isHermitian (diagonalBlock P)
    (fun i => hP.submatrix (fun e => (e,i))) a
  have hCQ := blockCompression_isHermitian (diagonalBlock Q)
    (fun i => hQ.submatrix (fun e => (e,i))) a
  have hp := norm_shift_eq_largest hCP (∑ i, |a i|)
    (blockCompression_positive_shift (diagonalBlock P)
      (fun i => (projection_diagonalBlock_contraction P hP hPId i).1)
      (fun i => (projection_diagonalBlock_contraction P hP hPId i).2) a _ le_rfl)
  have hq := norm_shift_eq_largest hCQ (∑ i, |a i|)
    (blockCompression_positive_shift (diagonalBlock Q)
      (fun i => (projection_diagonalBlock_contraction Q hQ hQId i).1)
      (fun i => (projection_diagonalBlock_contraction Q hQ hQId i).2) a _ le_rfl)
  have h := affineCompressionNorm_lipschitz P Q a (∑ i, |a i|)
  rw [hp, hq] at h
  simpa only [add_sub_add_left_eq_sub] using h

lemma abs_eigenvalue_le_opNorm [Nonempty E] (M : Matrix E E ℂ)
    (hM : M.IsHermitian) (i : E) : |hM.eigenvalues i| ≤ ‖M‖ := by
  have he : Matrix.toEuclideanLin M (hM.eigenvectorBasis i) =
      hM.eigenvalues i • hM.eigenvectorBasis i := by
    ext j
    exact congrFun (hM.mulVec_eigenvectorBasis i) j
  have h := toEuclideanLin_norm_le M (hM.eigenvectorBasis i)
  rw [he, norm_smul, hM.eigenvectorBasis.orthonormal.1 i, mul_one, mul_one,
    Real.norm_eq_abs] at h
  exact h

/-- The normalized real trace of a Hermitian matrix is contractive. -/
theorem abs_normalized_real_trace_le [Nonempty E] (M : Matrix E E ℂ)
    (hM : M.IsHermitian) : |(Matrix.trace M).re / (Fintype.card E : ℝ)| ≤ ‖M‖ := by
  have htr : |(Matrix.trace M).re| ≤ (Fintype.card E : ℝ) * ‖M‖ := by
    have he := trace_pow_re M hM 1
    simp only [pow_one] at he
    rw [he]
    calc
      _ ≤ ∑ i : E, |hM.eigenvalues i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : E, ‖M‖ := Finset.sum_le_sum (fun i _ => abs_eigenvalue_le_opNorm M hM i)
      _ = _ := by simp
  have hc : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  rw [abs_div, abs_of_pos hc]
  exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using htr)

/-- A noncommutative telescoping estimate for positive integer powers. -/
theorem norm_pow_succ_sub_le (A B : Matrix E E ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ K) (n : ℕ) :
    ‖A^(n+1) - B^(n+1)‖ ≤ ((n+1 : ℕ) : ℝ) * K^n * ‖A-B‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : A^(n+1+1) - B^(n+1+1) =
        A * (A^(n+1) - B^(n+1)) + (A-B) * B^(n+1) := by
      rw [pow_succ' A (n+1), pow_succ' B (n+1)]
      noncomm_ring
    have hBp : ‖B^(n+1)‖ ≤ K^(n+1) :=
      (norm_pow_le' B (Nat.succ_pos _)).trans (pow_le_pow_left₀ (norm_nonneg _) hB _)
    rw [show n.succ+1 = n+1+1 by omega, heq]
    calc
      _ ≤ ‖A * (A^(n+1)-B^(n+1))‖ + ‖(A-B) * B^(n+1)‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖A^(n+1)-B^(n+1)‖ + ‖A-B‖ * ‖B^(n+1)‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ K * (((n+1 : ℕ) : ℝ) * K^n * ‖A-B‖) + ‖A-B‖ * K^(n+1) := by
        gcongr
      _ = ((n+1+1 : ℕ) : ℝ) * K^(n+1) * ‖A-B‖ := by
        push_cast
        rw [pow_succ]
        ring

/-- Fixed positive normalized moments are Lipschitz on an operator-norm
ball, with a constant independent of the matrix dimension. -/
theorem normalized_moment_sub_le [Nonempty E]
    (A B : Matrix E E ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (K : ℝ) (hK : 0 ≤ K) (hAK : ‖A‖ ≤ K) (hBK : ‖B‖ ≤ K) (n : ℕ) :
    |(Matrix.trace (A^(n+1))).re / (Fintype.card E : ℝ) -
      (Matrix.trace (B^(n+1))).re / (Fintype.card E : ℝ)| ≤
      ((n+1 : ℕ) : ℝ) * K^n * ‖A-B‖ := by
  have h := abs_normalized_real_trace_le (A^(n+1)-B^(n+1)) ((hA.pow _).sub (hB.pow _))
  rw [Matrix.trace_sub, Complex.sub_re, sub_div] at h
  exact h.trans (norm_pow_succ_sub_le A B K hK hAK hBK n)

/-- The positive `(n+1)`-st normalized compression moment has Lipschitz
constant `(n+1) (∑ |aᵢ|)^(n+1)` on orthogonal projections. -/
theorem compressionMoment_lipschitz [Nonempty E]
    (P Q : Matrix (E × D) (E × D) ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPId : P*P = P) (hQId : Q*Q = Q) (a : D → ℝ) (n : ℕ) :
    |(Matrix.trace ((blockCompression (diagonalBlock P) a)^(n+1))).re /
        (Fintype.card E : ℝ) -
      (Matrix.trace ((blockCompression (diagonalBlock Q) a)^(n+1))).re /
        (Fintype.card E : ℝ)| ≤
      ((n+1 : ℕ) : ℝ) * (∑ i, |a i|)^(n+1) * ‖P-Q‖ := by
  have h := normalized_moment_sub_le _ _
    (blockCompression_isHermitian _ (fun i => hP.submatrix (fun e => (e,i))) a)
    (blockCompression_isHermitian _ (fun i => hQ.submatrix (fun e => (e,i))) a)
    (∑ i, |a i|) (Finset.sum_nonneg (fun i _ => abs_nonneg (a i)))
    (projection_compression_norm_le P hP hPId a)
    (projection_compression_norm_le Q hQ hQId a) n
  apply h.trans
  calc
    _ ≤ ((n+1 : ℕ) : ℝ) * (∑ i, |a i|)^n * ((∑ i, |a i|) * ‖P-Q‖) :=
      mul_le_mul_of_nonneg_left (blockCompression_opNorm_sub_le P Q a) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end StrongConvergence

#print axioms StrongConvergence.whiteningInverse_norm_le
#print axioms StrongConvergence.whitening_cross_error
#print axioms StrongConvergence.norm_whitenedProjection_sub_le
#print axioms StrongConvergence.norm_whitenedProjection_sub_le_common
#print axioms StrongConvergence.matrixCoordinates_opNorm_le
#print axioms StrongConvergence.whitening_lipschitzOn
#print axioms StrongConvergence.principal_submatrix_opNorm_le
#print axioms StrongConvergence.blockCompression_opNorm_sub_le
#print axioms StrongConvergence.affineCompressionNorm_lipschitz
#print axioms StrongConvergence.largestCompression_lipschitz
#print axioms StrongConvergence.normalized_moment_sub_le
#print axioms StrongConvergence.compressionMoment_lipschitz
#print axioms StrongConvergence.whitenedProjection_isHermitian_all
#print axioms StrongConvergence.whitenedProjection_idempotent_all
