import StrongConvergence.StrongConvergencePermutationNeumann
import StrongConvergence.StrongConvergenceGenusRadius
import Mathlib.Algebra.Polynomial.Div

/-! Exact polynomial realizations of the finite Haar Neumann moment expansion. -/
open Matrix MeasureTheory Polynomial
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

/-- Real polynomial evaluation followed by the canonical complex embedding. -/
def complexPolynomialEval (x : ℝ) : ℝ[X] →+* ℂ :=
  Complex.ofRealHom.comp (Polynomial.evalRingHom x)

@[simp] lemma complexPolynomialEval_apply (x : ℝ) (p : ℝ[X]) :
    complexPolynomialEval x p = Complex.ofReal (p.eval x) := rfl

lemma polynomialGramError_evalMatrix_inv {m N : ℕ} (hN : 0 < N) :
    (complexPolynomialEval ((N : ℝ)⁻¹)).mapMatrix (polynomialGramError m) =
      ((N : ℂ) ^ m)⁻¹ • permutationGram (Fin N) m - 1 := by
  ext σ τ
  exact polynomialGramError_eval_inv N hN σ τ

lemma partialInverse_evalMatrix_inv {m N : ℕ} (hN : 0 < N) (L : ℕ) :
    (complexPolynomialEval ((N : ℝ)⁻¹)).mapMatrix
      (NeumannPolynomial.partialInverse (polynomialGramError m) L) =
      ∑ l ∈ Finset.range (L + 1),
        (1 - ((N : ℂ) ^ m)⁻¹ • permutationGram (Fin N) m) ^ l := by
  simp only [NeumannPolynomial.partialInverse, map_sum, map_pow, map_neg,
    polynomialGramError_evalMatrix_inv hN, neg_sub]

lemma rankContractionPolynomial_eval_inv {m N : ℕ} (hN : 0 < N)
    (d : ℕ) (τ : Equiv.Perm (Fin m)) :
    complexPolynomialEval ((N : ℝ)⁻¹) (rankContractionPolynomial ((d : ℝ) / N) τ) =
      normalizedProjectionContractions N m d τ := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [complexPolynomialEval_apply, rankContractionPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_inv,
    normalizedProjectionContractions, cycleCount_symm, permutationLength]
  rw [div_pow, inv_pow]
  have hp : (N : ℂ) ^ (m - cycleCount τ) * (N : ℂ) ^ cycleCount τ = (N : ℂ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel (cycleCount_le _)]
  field_simp [hNC]
  rw [← hp]
  ring_nf
  simp

/-- The normalized finite inverse-Gram coefficient is exactly the evaluation
of the polynomial coefficient vector at inverse dimension and rank density. -/
theorem polynomialProjectionCoefficients_eval_inv {m N : ℕ} (hN : 0 < N)
    (d L : ℕ) (σ : Equiv.Perm (Fin m)) :
    complexPolynomialEval ((N : ℝ)⁻¹)
      (polynomialProjectionCoefficients m ((d : ℝ) / N) L σ) =
      neumannProjectionMomentCoefficients (Fin N) m d (L + 1) σ := by
  have hA := partialInverse_evalMatrix_inv (m := m) hN L
  unfold polynomialProjectionCoefficients neumannProjectionMomentCoefficients
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro τ _
  rw [rankContractionPolynomial_eval_inv hN]
  congr 1
  exact congrFun (congrFun hA σ) τ

/-- The real weighted permutation contraction, retaining arbitrary signs of `a`. -/
def realWeightedCycleMoment {K : Type*} [Fintype K] [DecidableEq K] {m : ℕ}
    (a : K → ℝ) (σ : Equiv.Perm (Fin m)) : ℝ :=
  (weightedCycleMoment a σ).re

lemma weightedCycleMoment_real {K : Type*} [Fintype K] [DecidableEq K] {m : ℕ}
    (a : K → ℝ) (σ : Equiv.Perm (Fin m)) :
    Complex.ofReal (realWeightedCycleMoment a σ) = weightedCycleMoment a σ := by
  unfold realWeightedCycleMoment weightedCycleMoment
  simp only [Complex.re_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp [← Complex.ofReal_prod]

/-- Uniform coefficient bound for signed weights, with `K = ∑ᵢ |aᵢ|`. -/
theorem weightedCycleMoment_norm_le {K : Type*} [Fintype K] [DecidableEq K] {m : ℕ}
    (a : K → ℝ) (σ : Equiv.Perm (Fin m)) :
    ‖weightedCycleMoment a σ‖ ≤ (∑ i, |a i|) ^ m := by
  classical
  unfold weightedCycleMoment
  calc
    _ ≤ ∑ b : Fin m → K, ‖(∏ l, (a (b l) : ℂ)) *
          (if b = (fun l => b (σ l)) then 1 else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin m → K, ∏ l, |a (b l)| := by
      apply Finset.sum_le_sum
      intro b _
      split_ifs
      · simp [norm_prod, Complex.norm_real, Real.norm_eq_abs]
      · simp only [mul_zero, norm_zero]
        positivity
    _ = _ := by
      simpa using (Fintype.prod_sum (fun (_ : Fin m) (i : K) => |a i|)).symm

lemma realWeightedCycleMoment_abs_le {K : Type*} [Fintype K] [DecidableEq K] {m : ℕ}
    (a : K → ℝ) (σ : Equiv.Perm (Fin m)) :
    |realWeightedCycleMoment a σ| ≤ (∑ i, |a i|) ^ m := by
  have h := weightedCycleMoment_norm_le a σ
  rw [← weightedCycleMoment_real a σ, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The output-dimension contribution after normalized trace division. -/
def genusWeight {m k : ℕ} (a : Fin k → ℝ) (σ : Equiv.Perm (Fin m)) : ℝ :=
  ((k : ℝ)⁻¹) ^ (cycleCount (finRotate m * σ) - 1) * realWeightedCycleMoment a σ

lemma genusWeight_abs_le {m k : ℕ} (hk : 0 < k)
    (a : Fin k → ℝ) (σ : Equiv.Perm (Fin m)) :
    |genusWeight a σ| ≤ (∑ i, |a i|) ^ m := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hi0 : 0 ≤ (k : ℝ)⁻¹ := by positivity
  have hi1 : (k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk1
  rw [genusWeight, abs_mul, abs_of_nonneg (pow_nonneg hi0 _)]
  calc
    _ ≤ 1 * |realWeightedCycleMoment a σ| :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hi0 hi1) (abs_nonneg _)
    _ ≤ _ := by simpa using realWeightedCycleMoment_abs_le a σ

/-- Numerator of the finite normalized moment polynomial. -/
def genusMomentNumerator (k m : ℕ) (a : Fin k → ℝ) (s : ℝ) (L : ℕ) : ℝ[X] :=
  ∑ σ : Equiv.Perm (Fin m), Polynomial.C (genusWeight a σ) *
    (Polynomial.X ^ permutationLength (finRotate m * σ) *
      polynomialProjectionCoefficients m s L σ)

lemma genusMomentNumerator_coeff_eq_zero {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (L n : ℕ) (hn : n < m - 1) :
    (genusMomentNumerator k m a s L).coeff n = 0 := by
  rw [genusMomentNumerator, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro σ _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs with hshift
  · rw [polynomialProjectionCoefficients_coeff_eq_zero]
    · simp
    · have h := permutationLength_add_finRotate_mul_ge hm σ
      omega
  · simp

lemma X_pow_dvd_genusMomentNumerator {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (L : ℕ) :
    Polynomial.X ^ (m - 1) ∣ genusMomentNumerator k m a s L := by
  apply Polynomial.X_pow_dvd_iff.mpr
  exact fun n hn => genusMomentNumerator_coeff_eq_zero hm a s L n hn

/-- The normalized finite moment is an honest polynomial in inverse dimension. -/
def genusMomentPolynomial (k m : ℕ) (a : Fin k → ℝ) (s : ℝ) (L : ℕ) : ℝ[X] :=
  genusMomentNumerator k m a s L /ₘ Polynomial.X ^ (m - 1)

lemma genusMomentPolynomial_factor {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (L : ℕ) :
    Polynomial.X ^ (m - 1) * genusMomentPolynomial k m a s L =
      genusMomentNumerator k m a s L := by
  obtain ⟨q, hq⟩ := X_pow_dvd_genusMomentNumerator hm a s L
  rw [genusMomentPolynomial, hq, Polynomial.mul_divByMonic_cancel_left q
    (Polynomial.monic_X_pow _)]

lemma genusMomentPolynomial_coeff {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (L n : ℕ) :
    (genusMomentPolynomial k m a s L).coeff n =
      (genusMomentNumerator k m a s L).coeff (n + (m - 1)) := by
  rw [← genusMomentPolynomial_factor hm a s L, Polynomial.coeff_X_pow_mul]

lemma genusMomentNumerator_coeff_eq_zero_of_parity {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (L n : ℕ) (hn : n % 2 ≠ (m - 1) % 2) :
    (genusMomentNumerator k m a s L).coeff n = 0 := by
  rw [genusMomentNumerator, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro σ _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs with hshift
  · rw [polynomialProjectionCoefficients_coeff_eq_zero_of_parity]
    · simp
    · have hpar := permutationLength_mul_mod_two (finRotate m * σ) σ.symm
      simp [mul_assoc, permutationLength_finRotate hm] at hpar
      omega
  · simp

/-- The normalized finite moment polynomial is even in inverse dimension. -/
theorem genusMomentPolynomial_odd_coeff {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (L n : ℕ) (hn : n % 2 = 1) :
    (genusMomentPolynomial k m a s L).coeff n = 0 := by
  rw [genusMomentPolynomial_coeff hm]
  apply genusMomentNumerator_coeff_eq_zero_of_parity hm
  omega

/-- A coefficient of degree `n` stabilizes once `n+m-1` Neumann terms
have been retained. -/
theorem genusMomentPolynomial_coeff_stable {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (n L : ℕ) (hL : n + (m - 1) ≤ L) :
    (genusMomentPolynomial k m a s L).coeff n =
      (genusMomentPolynomial k m a s (n + (m - 1))).coeff n := by
  rw [genusMomentPolynomial_coeff hm, genusMomentPolynomial_coeff hm]
  simp only [genusMomentNumerator, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs with hshift
  · rw [polynomialProjectionCoefficients_coeff_stable s
        (n + (m - 1) - permutationLength (finRotate m * σ)) L (by omega),
      polynomialProjectionCoefficients_coeff_stable s
        (n + (m - 1) - permutationLength (finRotate m * σ)) (n + (m - 1)) (by omega)]
  · rfl

/-- The constant term is a sum over geodesic permutations only. This identifies
the exact algebraic leading coefficient, before its free-cumulant interpretation. -/
theorem genusMomentPolynomial_constantTerm {k m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (s : ℝ) (L : ℕ) :
    (genusMomentPolynomial k m a s L).coeff 0 =
      ∑ σ : Equiv.Perm (Fin m),
        if permutationLength σ + permutationLength (finRotate m * σ) = m - 1 then
          genusWeight a σ * (polynomialProjectionCoefficients m s L σ).coeff
            (permutationLength σ) else 0 := by
  rw [genusMomentPolynomial_coeff hm]
  simp only [zero_add, genusMomentNumerator, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  apply Finset.sum_congr rfl
  intro σ _
  have hshift := permutationLength_le_pred hm (finRotate m * σ)
  rw [if_pos hshift]
  split_ifs with hgeo
  · have heq : m - 1 - permutationLength (finRotate m * σ) = permutationLength σ := by omega
    rw [heq]
  · have hge := permutationLength_add_finRotate_mul_ge hm σ
    have hlt : m - 1 - permutationLength (finRotate m * σ) < permutationLength σ := by omega
    rw [polynomialProjectionCoefficients_coeff_eq_zero s L σ _ hlt, mul_zero]

/-- Explicit error of the normalized projection-moment coefficient at any
finite Neumann order, proved from the actual inverse Gram matrix. -/
theorem projectionMomentCoefficients_neumann_error_quadratic
    {E : Type*} [Fintype E] [DecidableEq E] {r d : ℕ}
    (e : Fin r ↪ E) (hr : 0 < r) (hd : d ≤ Fintype.card E)
    (hN : 2 * r ^ 2 ≤ Fintype.card E) (q : ℕ) (σ : Equiv.Perm (Fin r)) :
    ‖projectionMomentCoefficients E r d σ -
      neumannProjectionMomentCoefficients E r d q σ‖ ≤
      2 * ((2 * (r : ℝ) ^ 2) / (3 * Fintype.card E)) ^ q := by
  have hE : 0 < Fintype.card E := lt_of_lt_of_le (by positivity) hN
  exact (projectionMomentCoefficients_sub_neumann_norm_le E r d q hE hd σ).trans
    (scaled_inverse_permutationGram_neumann_row_bound_quadratic e hr hN q σ)

lemma pow_div_self_eq_pred {x : ℝ} (hx : x ≠ 0) {c : ℕ} (hc : 1 ≤ c) :
    x ^ c / x = x ^ (c - 1) := by
  have hp : x ^ c = x ^ (c - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel hc]
  rw [hp, mul_div_cancel_right₀ _ hx]

/-- The scalar normalization needed when passing from ambient dimension
`U*K` to normalized trace on the input factor `U`. -/
lemma inverse_dimension_moment_scale (U K : ℂ) (hU : U ≠ 0) (hK : K ≠ 0)
    {r c : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r) :
    ((U * K)⁻¹) ^ (r - 1) * (U ^ c / U) =
      (K⁻¹) ^ (c - 1) * ((U * K)⁻¹) ^ (r - c) := by
  have hr : r - 1 = (c - 1) + (r - c) := by omega
  have hup : U ^ c = U ^ (c - 1) * U := by
    rw [← pow_succ, Nat.sub_add_cancel hc]
  rw [hup, mul_div_cancel_right₀ _ hU, hr, pow_add, _root_.mul_inv_rev, mul_pow]
  field_simp
  ring

end ProjectionChannels.TensorHaar
namespace ProjectionChannels.Canonical
open TensorHaar

/-- Exact realization of the normalized finite Haar-Neumann moment by an
even polynomial evaluated at inverse ambient dimension and actual rank density. -/
theorem genusMomentPolynomial_eval_eq_neumann {k : ℕ} (hk : 0 < k)
    (t : ℝ) (n m L : ℕ) (a : Fin k → ℝ) :
    complexPolynomialEval (((n + 1) * k : ℕ) : ℝ)⁻¹
      (genusMomentPolynomial k (m + 1) a
        ((rankSequence k t n : ℝ) / (((n + 1) * k : ℕ) : ℝ)) L) =
      neumannCompressionTraceMoment k t m (L + 1) a n / ((n + 1 : ℕ) : ℂ) := by
  let N : ℕ := (n + 1) * k
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos n) hk
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have huC : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hcard : Fintype.card (Index k n) = N := by
    simp only [Index, Fintype.card_prod, Fintype.card_fin, N]
  have hfac := congrArg (complexPolynomialEval ((N : ℝ)⁻¹))
    (genusMomentPolynomial_factor (Nat.succ_pos m) a
      ((rankSequence k t n : ℝ) / N) L)
  simp only [map_mul, map_pow, complexPolynomialEval_apply, Polynomial.eval_X,
    Complex.ofReal_inv, Complex.ofReal_natCast, Nat.succ_sub_one] at hfac
  apply (mul_left_cancel₀ (pow_ne_zero m (inv_ne_zero hNc)))
  simp only [complexPolynomialEval_apply]
  change (N : ℂ)⁻¹ ^ m * _ = (N : ℂ)⁻¹ ^ m * _
  rw [hfac]
  unfold genusMomentNumerator neumannCompressionTraceMoment
  simp only [Polynomial.eval_finset_sum, Complex.ofReal_sum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_natCast,
    Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hcoeff := polynomialProjectionCoefficients_eval_inv hN (rankSequence k t n) L σ
  simp only [complexPolynomialEval_apply] at hcoeff
  rw [hcoeff, neumannProjectionMomentCoefficients_eq_fin (Index k n), hcard]
  have hscale := inverse_dimension_moment_scale ((n + 1 : ℕ) : ℂ) (k : ℂ)
    huC hkC (cycleCount_pos (Nat.succ_pos m) (finRotate (m + 1) * σ))
    (cycleCount_le (finRotate (m + 1) * σ))
  have hNcprod : ((n + 1 : ℕ) : ℂ) * (k : ℂ) = (N : ℂ) := by
    simp [N]
  rw [hNcprod] at hscale
  simp only [Nat.add_sub_cancel] at hscale
  simp only [genusWeight, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv, Complex.ofReal_natCast, weightedCycleMoment_real,
    permutationLength]
  convert congrArg (fun z : ℂ => z *
    neumannProjectionMomentCoefficients (Fin N) (m + 1) (rankSequence k t n) (L + 1) σ *
      weightedCycleMoment a σ) hscale.symm using 1 <;> ring

/-- The actual expected normalized trace moment of the canonical ensemble. -/
def expectedNormalizedMoment (k : ℕ) (t : ℝ) (n m : ℕ) (a : Fin k → ℝ) : ℂ :=
  (∫ ω, Matrix.trace
    ((blockCompression (diagonalBlock (projection k t ω n)) a) ^ (m + 1))
      ∂probability k) / ((n + 1 : ℕ) : ℂ)

/-- Quantitative finite error for the actual Haar expectation, not an assumed
moment bound. This is the Neumann part of the degree-truncation remainder. -/
theorem expectedNormalizedMoment_neumann_error
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n m L : ℕ) (hmn : m ≤ n) (a : Fin k → ℝ)
    (hN : 2 * (m + 1) ^ 2 ≤ (n + 1) * k) :
    ‖expectedNormalizedMoment k t n m a -
      complexPolynomialEval ((((n + 1) * k : ℕ) : ℝ)⁻¹)
        (genusMomentPolynomial k (m + 1) a
          ((rankSequence k t n : ℝ) / (((n + 1) * k : ℕ) : ℝ)) L)‖ ≤
      ((m + 1).factorial : ℝ) * ((((n + 1) * k : ℕ) : ℝ) ^ m) *
        (∑ i, |a i|) ^ (m + 1) *
        (2 * ((2 * ((m + 1 : ℕ) : ℝ) ^ 2) /
          (3 * (((n + 1) * k : ℕ) : ℝ))) ^ (L + 1)) := by
  let N : ℕ := (n + 1) * k
  let K : ℝ := ∑ i, |a i|
  let B : ℝ := 2 * ((2 * ((m + 1 : ℕ) : ℝ) ^ 2) / (3 * (N : ℝ))) ^ (L + 1)
  let D (σ : Equiv.Perm (Fin (m + 1))) :=
    projectionMomentCoefficients (Index k n) (m + 1) (rankSequence k t n) σ -
      neumannProjectionMomentCoefficients (Index k n) (m + 1) (rankSequence k t n) (L + 1) σ
  have hNpos : 0 < N := Nat.mul_pos (Nat.succ_pos n) hk
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcard : Fintype.card (Index k n) = N := by
    simp only [Index, Fintype.card_prod, Fintype.card_fin, N]
  let e : Fin (m + 1) ↪ Index k n :=
    { toFun := fun i => (Fin.castLE (Nat.succ_le_succ hmn) i, ⟨0, hk⟩)
      inj' := by
        intro i j h
        apply Fin.ext
        exact congrArg (fun z : Index k n => z.1.val) h }
  have hD (σ : Equiv.Perm (Fin (m + 1))) : ‖D σ‖ ≤ B := by
    simpa only [D, B, hcard] using
      projectionMomentCoefficients_neumann_error_quadratic e (Nat.succ_pos m)
        (rankSequence_le ht0 ht1 n) (by simpa only [hcard] using hN) (L + 1) σ
  have huR : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have huN : ((n + 1 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (show n + 1 ≤ N by dsimp [N]; nlinarith)
  have hterm (σ : Equiv.Perm (Fin (m + 1))) :
      ‖D σ * ((n + 1 : ℕ) : ℂ) ^ cycleCount (finRotate (m + 1) * σ) *
          weightedCycleMoment a σ / ((n + 1 : ℕ) : ℂ)‖ ≤ (N : ℝ) ^ m * K ^ (m + 1) * B := by
    have hc1 := cycleCount_pos (Nat.succ_pos m) (finRotate (m + 1) * σ)
    have hcm := cycleCount_le (finRotate (m + 1) * σ)
    have hpow : ((n + 1 : ℕ) : ℝ) ^ (cycleCount (finRotate (m + 1) * σ) - 1) ≤
        (N : ℝ) ^ m := by
      exact (pow_le_pow_left₀ huR.le huN _).trans
        (pow_le_pow_right₀ hN1 (by omega))
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    calc
      _ = ‖D σ‖ *
          (((n + 1 : ℕ) : ℝ) ^ cycleCount (finRotate (m + 1) * σ) /
            ((n + 1 : ℕ) : ℝ)) * ‖weightedCycleMoment a σ‖ := by ring
      _ = ‖D σ‖ *
          (((n + 1 : ℕ) : ℝ) ^ (cycleCount (finRotate (m + 1) * σ) - 1)) *
            ‖weightedCycleMoment a σ‖ := by rw [pow_div_self_eq_pred huR.ne' hc1]
      _ ≤ B * ((N : ℝ) ^ m) * K ^ (m + 1) :=
        mul_le_mul (mul_le_mul (hD σ) hpow (by positivity) hB)
          (weightedCycleMoment_norm_le a σ) (by positivity) (by positivity)
      _ = _ := by ring
  rw [genusMomentPolynomial_eval_eq_neumann hk]
  unfold expectedNormalizedMoment
  rw [integral_compression_trace_cycles hk ht0 ht1 n m hmn a,
    neumannCompressionTraceMoment, ← sub_div, ← Finset.sum_sub_distrib, Finset.sum_div]
  have hsum :
      (∑ σ : Equiv.Perm (Fin (m + 1)),
        (projectionMomentCoefficients (Index k n) (m + 1) (rankSequence k t n) σ *
          ((n + 1 : ℕ) : ℂ) ^ cycleCount (finRotate (m + 1) * σ) * weightedCycleMoment a σ -
        neumannProjectionMomentCoefficients (Index k n) (m + 1) (rankSequence k t n) (L + 1) σ *
          ((n + 1 : ℕ) : ℂ) ^ cycleCount (finRotate (m + 1) * σ) * weightedCycleMoment a σ) /
            ((n + 1 : ℕ) : ℂ)) =
      ∑ σ : Equiv.Perm (Fin (m + 1)), D σ *
        ((n + 1 : ℕ) : ℂ) ^ cycleCount (finRotate (m + 1) * σ) *
          weightedCycleMoment a σ / ((n + 1 : ℕ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [D]
    ring
  rw [hsum]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin (m + 1)), ‖D σ *
        ((n + 1 : ℕ) : ℂ) ^ cycleCount (finRotate (m + 1) * σ) *
          weightedCycleMoment a σ / ((n + 1 : ℕ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin (m + 1)), (N : ℝ) ^ m * K ^ (m + 1) * B :=
      Finset.sum_le_sum fun σ _ => hterm σ
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]
      dsimp [N, K, B]
      ring

end ProjectionChannels.Canonical
namespace ProjectionChannels.TensorHaar
#print axioms ProjectionChannels.Canonical.expectedNormalizedMoment_neumann_error
#print axioms ProjectionChannels.Canonical.genusMomentPolynomial_eval_eq_neumann
#print axioms polynomialProjectionCoefficients_eval_inv
#print axioms weightedCycleMoment_norm_le
#print axioms genusMomentPolynomial_factor
#print axioms genusMomentPolynomial_odd_coeff
#print axioms genusMomentPolynomial_coeff_stable
#print axioms genusMomentPolynomial_constantTerm
end ProjectionChannels.TensorHaar
