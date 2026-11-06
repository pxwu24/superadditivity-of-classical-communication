import StrongConvergence.StrongConvergenceGenusExpansion

/-! Coefficient majorants and degree truncation for finite Haar moment polynomials. -/
open Polynomial Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

lemma negative_polynomial_matrix_pow {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ[X]) (l : ℕ) :
    (-A) ^ l = (-1 : ℝ[X]) ^ l • A ^ l := by
  rw [← neg_one_smul ℝ[X] A, smul_pow]

/-- Expanding the finite inverse series exposes its coefficientwise positive
path polynomials and puts all signs in scalar coefficients. -/
theorem genusMomentNumerator_expansion {k m : ℕ}
    (a : Fin k → ℝ) (s : ℝ) (L : ℕ) :
    genusMomentNumerator k m a s L =
      ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
        ∑ l ∈ Finset.range (L + 1),
          Polynomial.C ((-1 : ℝ) ^ l * genusWeight a σ * s ^ cycleCount τ) *
            genusNumerator σ τ l := by
  simp only [genusMomentNumerator, polynomialProjectionCoefficients,
    NeumannPolynomial.partialInverse, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    negative_polynomial_matrix_pow, Matrix.smul_apply, smul_eq_mul,
    rankContractionPolynomial, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro l _
  simp only [genusNumerator, map_mul, map_pow, map_neg, map_one, pow_add]
  ring

lemma genusNumerator_coeff_nonneg {m : ℕ} (σ τ : Equiv.Perm (Fin m)) (l n : ℕ) :
    0 ≤ (genusNumerator σ τ l).coeff n := by
  rw [genusNumerator, Polynomial.coeff_X_pow_mul']
  split_ifs
  · exact polynomialGramError_pow_coeff_nonneg _ _ _ _
  · rfl

/-- The unsigned sum of all numerator paths. -/
def genusMajorantNumerator (m L : ℕ) : ℝ[X] :=
  ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
    ∑ l ∈ Finset.range (L + 1), genusNumerator σ τ l

lemma genusMajorantNumerator_coeff_nonneg (m L n : ℕ) :
    0 ≤ (genusMajorantNumerator m L).coeff n := by
  simp only [genusMajorantNumerator, Polynomial.finset_sum_coeff]
  exact Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ =>
    Finset.sum_nonneg fun l _ => genusNumerator_coeff_nonneg σ τ l n

lemma genusMajorantNumerator_coeff_eq_zero {m : ℕ} (hm : 0 < m)
    (L n : ℕ) (hn : n < m - 1) : (genusMajorantNumerator m L).coeff n = 0 := by
  simp only [genusMajorantNumerator, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro σ _
  apply Finset.sum_eq_zero
  intro τ _
  apply Finset.sum_eq_zero
  intro l _
  exact genusNumerator_coeff_eq_zero hm σ τ l n (Or.inr hn)

/-- Normalized coefficientwise positive majorant. -/
def genusMajorantPolynomial (m L : ℕ) : ℝ[X] :=
  genusMajorantNumerator m L /ₘ Polynomial.X ^ (m - 1)

lemma genusMajorantPolynomial_factor {m : ℕ} (hm : 0 < m) (L : ℕ) :
    Polynomial.X ^ (m - 1) * genusMajorantPolynomial m L = genusMajorantNumerator m L := by
  have hdiv : Polynomial.X ^ (m - 1) ∣ genusMajorantNumerator m L := by
    apply Polynomial.X_pow_dvd_iff.mpr
    exact fun n hn => genusMajorantNumerator_coeff_eq_zero hm L n hn
  obtain ⟨q, hq⟩ := hdiv
  rw [genusMajorantPolynomial, hq, Polynomial.mul_divByMonic_cancel_left q
    (Polynomial.monic_X_pow _)]

lemma genusMajorantPolynomial_coeff {m : ℕ} (hm : 0 < m) (L n : ℕ) :
    (genusMajorantPolynomial m L).coeff n =
      (genusMajorantNumerator m L).coeff (n + (m - 1)) := by
  rw [← genusMajorantPolynomial_factor hm L, Polynomial.coeff_X_pow_mul]

lemma genusMajorantPolynomial_coeff_nonneg {m : ℕ} (hm : 0 < m) (L n : ℕ) :
    0 ≤ (genusMajorantPolynomial m L).coeff n := by
  rw [genusMajorantPolynomial_coeff hm]
  exact genusMajorantNumerator_coeff_nonneg _ _ _

/-- Signed coefficients are dominated by the unsigned path expansion. -/
theorem genusMomentNumerator_coeff_abs_le {k m : ℕ} (hk : 0 < k)
    (a : Fin k → ℝ) {s : ℝ} (hs : |s| ≤ 1) (L n : ℕ) :
    |(genusMomentNumerator k m a s L).coeff n| ≤
      (∑ i, |a i|) ^ m * (genusMajorantNumerator m L).coeff n := by
  rw [genusMomentNumerator_expansion]
  simp only [genusMajorantNumerator, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro σ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro τ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [abs_mul, abs_of_nonneg (genusNumerator_coeff_nonneg σ τ l n)]
  apply mul_le_mul_of_nonneg_right _ (genusNumerator_coeff_nonneg σ τ l n)
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  calc
    |genusWeight a σ| * |s| ^ cycleCount τ ≤ (∑ i, |a i|) ^ m * 1 :=
      mul_le_mul (genusWeight_abs_le hk a σ) (pow_le_one₀ (abs_nonneg _) hs)
        (by positivity) (by positivity)
    _ = _ := mul_one _

/-- Uniform majorization for the normalized finite moment polynomial. -/
theorem genusMomentPolynomial_coeff_abs_le {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (a : Fin k → ℝ) {s : ℝ} (hs : |s| ≤ 1) (L n : ℕ) :
    |(genusMomentPolynomial k m a s L).coeff n| ≤
      (∑ i, |a i|) ^ m * (genusMajorantPolynomial m L).coeff n := by
  rw [genusMomentPolynomial_coeff hm, genusMajorantPolynomial_coeff hm]
  exact genusMomentNumerator_coeff_abs_le hk a hs L _

lemma polynomial_eval_nonneg_of_coeff (p : ℝ[X]) (hp : ∀ i, 0 ≤ p.coeff i)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ p.eval x := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (pow_nonneg hx i)

lemma polynomialGramError_pow_eval {m : ℕ} (x : ℝ) (l : ℕ)
    (σ τ : Equiv.Perm (Fin m)) :
    Polynomial.eval x ((polynomialGramError m ^ l) σ τ) =
      ((polynomialGramError m).map (Polynomial.eval x) ^ l) σ τ := by
  exact congrFun (congrFun (map_pow (Polynomial.evalRingHom x).mapMatrix
    (polynomialGramError m) l) σ) τ

lemma matrix_pow_row_sum {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (ε : ℝ) (hrow : ∀ i, ∑ j, A i j = ε) (l : ℕ) :
    ∀ i, ∑ j, (A ^ l) i j = ε ^ l := by
  induction l with
  | zero => intro i; simp [Matrix.one_apply]
  | succ l ih =>
    intro i
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hrow]
    rw [← Finset.sum_mul, ih]

lemma polynomialGramError_eval_row_sum {m N : ℕ} (hN : 0 < N)
    (σ : Equiv.Perm (Fin m)) :
    (∑ τ, Polynomial.eval ((N : ℝ)⁻¹) (polynomialGramError m σ τ)) =
      genusRowError m ((N : ℝ)⁻¹) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ = ∑ τ, ‖((((N : ℂ) ^ m)⁻¹ • permutationGram (Fin N) m - 1) σ τ)‖ := by
      apply Finset.sum_congr rfl
      intro τ _
      rw [← polynomialGramError_eval_inv N hN σ τ, Complex.norm_real, Real.norm_eq_abs]
      symm
      apply abs_of_nonneg
      exact polynomial_eval_nonneg_of_coeff _
        (NeumannPolynomial.monomialMatrix_coeff_nonneg permutationDistance σ τ) (by positivity)
    _ = _ := by
      simpa [genusRowError, div_eq_mul_inv] using
        normalized_permutationGram_sub_one_row_product (E := Fin N) (by simpa using hN) σ

lemma genusRadius_le_one {m : ℕ} (hm : 0 < m) : genusRadius m ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold genusRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith

lemma genusRadius_eq_inv_nat (m : ℕ) :
    genusRadius m = (((2 * m ^ 2 : ℕ) : ℝ))⁻¹ := by
  simp [genusRadius, one_div]

lemma polynomialGramError_eval_radius_row_sum {m : ℕ} (hm : 0 < m)
    (σ : Equiv.Perm (Fin m)) :
    (∑ τ, Polynomial.eval (genusRadius m) (polynomialGramError m σ τ)) =
      genusRowError m (genusRadius m) := by
  rw [genusRadius_eq_inv_nat]
  exact polynomialGramError_eval_row_sum (by positivity) σ

lemma finite_geometric_sum_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (L : ℕ) :
    (∑ l ∈ Finset.range (L + 1), ε ^ l) ≤ 1 / (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hε0 (L + 1)]

/-- The unsigned numerator has a uniform radius bound obtained from the exact
Haar Gram row sums, rather than counting paths factorially at every step. -/
theorem genusMajorantNumerator_eval_radius_le {m : ℕ} (hm : 0 < m) (L : ℕ) :
    (genusMajorantNumerator m L).eval (genusRadius m) ≤
      (m.factorial : ℝ) / (1 - genusRowError m (genusRadius m)) := by
  let y := genusRadius m
  let ε := genusRowError m y
  have hy0 : 0 ≤ y := (genusRadius_pos hm).le
  have hy1 : y ≤ 1 := genusRadius_le_one hm
  have hε0 : 0 ≤ ε := genusRowError_nonneg m hy0
  have hε1 : ε < 1 := lt_trans (genusRowError_radius_lt_third hm) (by norm_num)
  have hrow : ∀ σ, ∑ τ, ((polynomialGramError m).map (Polynomial.eval y)) σ τ = ε := by
    intro σ
    exact polynomialGramError_eval_radius_row_sum hm σ
  have hrowpow (l : ℕ) (σ : Equiv.Perm (Fin m)) :
      (∑ τ, Polynomial.eval y ((polynomialGramError m ^ l) σ τ)) = ε ^ l := by
    simp_rw [polynomialGramError_pow_eval]
    exact matrix_pow_row_sum _ ε hrow l σ
  simp only [genusMajorantNumerator, Polynomial.eval_finset_sum,
    genusNumerator, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
        ∑ l ∈ Finset.range (L + 1), Polynomial.eval y ((polynomialGramError m ^ l) σ τ) := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.sum_le_sum
      intro τ _
      apply Finset.sum_le_sum
      intro l _
      apply mul_le_of_le_one_left
      · exact polynomial_eval_nonneg_of_coeff _
          (polynomialGramError_pow_coeff_nonneg l σ τ) hy0
      · exact pow_le_one₀ hy0 hy1
    _ = ∑ σ : Equiv.Perm (Fin m), ∑ l ∈ Finset.range (L + 1), ε ^ l := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.sum_comm]
      simp_rw [hrowpow]
    _ = (m.factorial : ℝ) * ∑ l ∈ Finset.range (L + 1), ε ^ l := by
      simp [Fintype.card_perm, nsmul_eq_mul]
    _ ≤ (m.factorial : ℝ) * (1 / (1 - ε)) :=
      mul_le_mul_of_nonneg_left (finite_geometric_sum_le hε0 hε1 L) (by positivity)
    _ = _ := by ring

/-- Radius bound on the normalized unsigned polynomial. -/
theorem genusMajorantPolynomial_eval_radius_le {m : ℕ} (hm : 0 < m) (L : ℕ) :
    (genusMajorantPolynomial m L).eval (genusRadius m) ≤
      (m.factorial : ℝ) / ((genusRadius m) ^ (m - 1) *
        (1 - genusRowError m (genusRadius m))) := by
  have hy := genusRadius_pos hm
  have he := genusRowError_radius_lt_third hm
  have hden : 0 < 1 - genusRowError m (genusRadius m) := by linarith
  have hfac := congrArg (Polynomial.eval (genusRadius m)) (genusMajorantPolynomial_factor hm L)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hfac
  apply (le_div_iff₀ (mul_pos (pow_pos hy _) hden)).mpr
  calc
    _ = ((genusRadius m) ^ (m - 1) *
          (genusMajorantPolynomial m L).eval (genusRadius m)) *
        (1 - genusRowError m (genusRadius m)) := by ring
    _ = (genusMajorantNumerator m L).eval (genusRadius m) *
        (1 - genusRowError m (genusRadius m)) := by rw [hfac]
    _ ≤ _ := (le_div_iff₀ hden).mp (genusMajorantNumerator_eval_radius_le hm L)

#print axioms genusMajorantPolynomial_eval_radius_le
#print axioms genusMomentNumerator_expansion
#print axioms genusMomentPolynomial_coeff_abs_le
end ProjectionChannels.TensorHaar
