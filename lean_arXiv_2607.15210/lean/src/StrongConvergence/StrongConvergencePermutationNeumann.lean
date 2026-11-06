import StrongConvergence.StrongConvergenceGenusParity
import StrongConvergence.StrongConvergenceGenusNeumann

/-!
# The polynomial normalized Haar Gram matrix

Specialization of the polynomial-matrix filtration to absolute permutation
length. These are finite identities for all moment orders and all powers.
-/
open scoped BigOperators
open Polynomial Matrix
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {m : ℕ}

/-- Length of the relative permutation from `σ` to `τ`. -/
def permutationDistance (σ τ : Equiv.Perm (Fin m)) : ℕ :=
  permutationLength (τ * σ.symm)

@[simp] lemma permutationDistance_self (σ : Equiv.Perm (Fin m)) :
    permutationDistance σ σ = 0 := by
  simp [permutationDistance]

lemma permutationDistance_pos {σ τ : Equiv.Perm (Fin m)} (hστ : σ ≠ τ) :
    0 < permutationDistance σ τ := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hmul := (permutationLength_eq_zero_iff _).mp hzero
  have h := congrArg (fun ρ => ρ * σ) hmul
  have hτσ : τ = σ := by simpa [mul_assoc] using h
  exact hστ hτσ.symm

lemma permutationDistance_triangle (σ ρ τ : Equiv.Perm (Fin m)) :
    permutationDistance σ τ ≤ permutationDistance σ ρ + permutationDistance ρ τ := by
  simpa [permutationDistance, permutation_symm_eq_inv, mul_assoc, Nat.add_comm] using
    permutationLength_mul_le (τ * ρ.symm) (ρ * σ.symm)

/-- Polynomial off-diagonal error of the normalized Haar permutation Gram matrix. -/
def polynomialGramError (m : ℕ) :
    Matrix (Equiv.Perm (Fin m)) (Equiv.Perm (Fin m)) ℝ[X] :=
  NeumannPolynomial.monomialMatrix permutationDistance

/-- Evaluating at the reciprocal ambient dimension gives exactly the
normalized Haar Gram error, entry by entry (not merely a bound on its norm). -/
theorem polynomialGramError_eval_inv (N : ℕ) (hN : 0 < N)
    (σ τ : Equiv.Perm (Fin m)) :
    Complex.ofReal (Polynomial.eval ((N : ℝ)⁻¹) (polynomialGramError m σ τ)) =
      ((((N : ℂ) ^ m)⁻¹ • permutationGram (Fin N) m - 1) σ τ) := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  by_cases hστ : σ = τ
  · subst τ
    simp [polynomialGramError, NeumannPolynomial.monomialMatrix,
      permutationGram_cycles, Matrix.smul_apply, smul_eq_mul, hNC]
  · simp only [polynomialGramError, NeumannPolynomial.monomialMatrix, if_neg hστ,
      Polynomial.eval_pow, Polynomial.eval_X, Complex.ofReal_pow, Complex.ofReal_inv,
      Complex.ofReal_natCast, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      permutationGram_cycles, Fintype.card_fin, Matrix.one_apply_ne hστ, sub_zero,
      permutationDistance, permutationLength]
    rw [inv_pow]
    have hp : (N : ℂ) ^ (m - cycleCount (τ * σ.symm)) *
        (N : ℂ) ^ cycleCount (τ * σ.symm) = (N : ℂ) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (cycleCount_le _)]
    field_simp
    simpa [mul_comm] using hp.symm

/-- Every coefficient is nonnegative. No bound on the order or exponent is needed. -/
theorem polynomialGramError_pow_coeff_nonneg (l : ℕ)
    (σ τ : Equiv.Perm (Fin m)) (n : ℕ) :
    0 ≤ ((polynomialGramError m ^ l) σ τ).coeff n :=
  NeumannPolynomial.coeffNonnegative_pow
    (NeumannPolynomial.monomialMatrix_coeff_nonneg permutationDistance) l σ τ n

/-- A term in the `l`th power has degree at least both `l` and the
length of the relative permutation. -/
theorem polynomialGramError_pow_coeff_eq_zero (l : ℕ)
    (σ τ : Equiv.Perm (Fin m)) (n : ℕ)
    (hn : n < l ∨ n < permutationLength (τ * σ.symm)) :
    ((polynomialGramError m ^ l) σ τ).coeff n = 0 := by
  exact (NeumannPolynomial.monomialMatrix_pow_coefficients permutationDistance
    permutationDistance_self (fun _ _ h => permutationDistance_pos h)
    permutationDistance_triangle l σ τ n).2 hn

lemma polynomialGramError_natDegree_le (hm : 0 < m)
    (σ τ : Equiv.Perm (Fin m)) :
    (polynomialGramError m σ τ).natDegree ≤ m - 1 := by
  unfold polynomialGramError NeumannPolynomial.monomialMatrix
  split_ifs
  · simp
  · rw [Polynomial.natDegree_X_pow]
    exact permutationLength_le_pred hm _

/-- Relative permutation parity fixes the parity of every coefficient. -/
theorem polynomialGramError_pow_coeff_eq_zero_of_parity (l : ℕ)
    (σ τ : Equiv.Perm (Fin m)) (n : ℕ)
    (hn : n % 2 ≠ permutationLength (τ * σ.symm) % 2) :
    ((polynomialGramError m ^ l) σ τ).coeff n = 0 := by
  exact NeumannPolynomial.pow_coeff_eq_zero_of_parity permutationDistance
    permutationDistance_self permutationDistance_parity _
    (NeumannPolynomial.monomialMatrix_coeff_eq_zero_of_parity permutationDistance)
    l σ τ n hn

/-- The sharp degree upper bound used by the finite expansion. -/
theorem polynomialGramError_pow_natDegree_le (hm : 0 < m) (l : ℕ)
    (σ τ : Equiv.Perm (Fin m)) :
    ((polynomialGramError m ^ l) σ τ).natDegree ≤ l * (m - 1) := by
  exact NeumannPolynomial.pow_natDegree_le _ (m - 1)
    (polynomialGramError_natDegree_le hm) l σ τ

/-- The polynomial Neumann coefficients stabilize at each fixed degree. -/
theorem polynomialGramError_neumann_coeff_stable
    (n L : ℕ) (hL : n ≤ L) (σ τ : Equiv.Perm (Fin m)) :
    (NeumannPolynomial.partialInverse (polynomialGramError m) L σ τ).coeff n =
      (NeumannPolynomial.partialInverse (polynomialGramError m) n σ τ).coeff n := by
  exact NeumannPolynomial.partialInverse_coeff_stable _
    (NeumannPolynomial.monomialMatrix_coeff_zero permutationDistance
      (fun _ _ h => permutationDistance_pos h)) n L hL σ τ

/-- The polynomial rank contraction in the normalized Gram system. -/
def rankContractionPolynomial (s : ℝ) (τ : Equiv.Perm (Fin m)) : ℝ[X] :=
  Polynomial.C (s ^ cycleCount τ) * Polynomial.X ^ permutationLength τ

lemma rankContractionPolynomial_coeff (s : ℝ) (τ : Equiv.Perm (Fin m)) (n : ℕ) :
    (rankContractionPolynomial s τ).coeff n =
      if n = permutationLength τ then s ^ cycleCount τ else 0 := by
  rw [rankContractionPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs <;> simp

/-- Polynomial approximation to the normalized projection-moment coefficients. -/
def polynomialProjectionCoefficients (m : ℕ) (s : ℝ) (L : ℕ) :
    Equiv.Perm (Fin m) → ℝ[X] :=
  NeumannPolynomial.partialInverse (polynomialGramError m) L *ᵥ
    rankContractionPolynomial s

/-- The inverse Gram solution starts at the absolute length of its permutation. -/
theorem polynomialProjectionCoefficients_coeff_eq_zero (s : ℝ) (L : ℕ)
    (σ : Equiv.Perm (Fin m)) (n : ℕ) (hn : n < permutationLength σ) :
    (polynomialProjectionCoefficients m s L σ).coeff n = 0 := by
  apply NeumannPolynomial.mulVec_coeff_eq_zero_of_lt permutationDistance
    permutationLength permutationLength ?_ _ _ ?_ ?_ σ n hn
  · intro σ τ
    simpa [permutationDistance, Nat.add_comm] using permutationLength_le_add_distance σ τ
  · intro σ τ n hn
    exact NeumannPolynomial.partialInverse_coeff_eq_zero_of_lt_distance permutationDistance
      permutationDistance_self permutationDistance_triangle _
      (NeumannPolynomial.monomialMatrix_coeff_eq_zero_of_lt permutationDistance) L σ τ n hn
  · intro τ n hn
    simp [rankContractionPolynomial_coeff, hn.ne]

/-- Only coefficients of the same parity as the permutation length can occur. -/
theorem polynomialProjectionCoefficients_coeff_eq_zero_of_parity (s : ℝ) (L : ℕ)
    (σ : Equiv.Perm (Fin m)) (n : ℕ) (hn : n % 2 ≠ permutationLength σ % 2) :
    (polynomialProjectionCoefficients m s L σ).coeff n = 0 := by
  apply NeumannPolynomial.mulVec_coeff_eq_zero_of_parity permutationDistance
    permutationLength permutationLength ?_ _ _ ?_ ?_ σ n hn
  · intro σ τ
    have h := permutationLength_mul_mod_two (σ * τ.symm) τ
    simpa [permutationDistance, mul_assoc, permutationLength_mul_symm_comm σ τ] using h
  · intro σ τ n hn
    exact NeumannPolynomial.partialInverse_coeff_eq_zero_of_parity permutationDistance
      permutationDistance_self permutationDistance_parity _
      (NeumannPolynomial.monomialMatrix_coeff_eq_zero_of_parity permutationDistance) L σ τ n hn
  · intro τ n hn
    have hne : n ≠ permutationLength τ := by
      intro h
      exact hn (congrArg (fun x => x % 2) h)
    simp [rankContractionPolynomial_coeff, hne]

/-- Coefficients of degree `n` become independent of truncation for `L ≥ n`. -/
theorem polynomialProjectionCoefficients_coeff_stable (s : ℝ)
    (n L : ℕ) (hL : n ≤ L) (σ : Equiv.Perm (Fin m)) :
    (polynomialProjectionCoefficients m s L σ).coeff n =
      (polynomialProjectionCoefficients m s n σ).coeff n := by
  exact NeumannPolynomial.partialInverse_mulVec_coeff_stable _
    (NeumannPolynomial.monomialMatrix_coeff_zero permutationDistance
      (fun _ _ h => permutationDistance_pos h)) _ n L hL σ

/-- A single numerator summand before removing the universal factor
`X^(m-1)` in the normalized moment expansion. -/
def genusNumerator (σ τ : Equiv.Perm (Fin m)) (l : ℕ) : ℝ[X] :=
  Polynomial.X ^ (permutationLength τ + permutationLength (finRotate m * σ)) *
    ((polynomialGramError m ^ l) σ τ)

/-- There are no negative powers after division by `X^(m-1)`, and
terms of walk length greater than the requested degree do not contribute. -/
theorem genusNumerator_coeff_eq_zero (hm : 0 < m)
    (σ τ : Equiv.Perm (Fin m)) (l n : ℕ)
    (hn : n < l ∨ n < m - 1) : (genusNumerator σ τ l).coeff n = 0 := by
  rw [genusNumerator, Polynomial.coeff_X_pow_mul']
  split_ifs with hshift
  · apply polynomialGramError_pow_coeff_eq_zero
    rcases hn with hn | hn
    · left; omega
    · right
      have h := permutationLength_genus_nonneg hm σ τ
      omega
  · rfl

/-- The shifted Haar numerator has the same coefficient parity as `m-1`.
After removal of `X^(m-1)`, only even powers remain. -/
theorem genusNumerator_coeff_eq_zero_of_parity (hm : 0 < m)
    (σ τ : Equiv.Perm (Fin m)) (l n : ℕ)
    (hn : n % 2 ≠ (m - 1) % 2) : (genusNumerator σ τ l).coeff n = 0 := by
  rw [genusNumerator, Polynomial.coeff_X_pow_mul']
  split_ifs with hshift
  · apply polynomialGramError_pow_coeff_eq_zero_of_parity
    have h₁ := permutationLength_mul_mod_two (τ * σ.symm) σ
    have h₂ := permutationLength_mul_mod_two (finRotate m * σ) σ.symm
    simp [mul_assoc, permutationLength_finRotate hm] at h₁ h₂
    omega
  · rfl

#print axioms polynomialProjectionCoefficients_coeff_eq_zero_of_parity
#print axioms polynomialProjectionCoefficients_coeff_stable
#print axioms genusNumerator_coeff_eq_zero
#print axioms genusNumerator_coeff_eq_zero_of_parity
#print axioms polynomialGramError_eval_inv
#print axioms polynomialGramError_pow_coeff_eq_zero
#print axioms polynomialGramError_pow_natDegree_le
#print axioms polynomialGramError_neumann_coeff_stable
end ProjectionChannels.TensorHaar
