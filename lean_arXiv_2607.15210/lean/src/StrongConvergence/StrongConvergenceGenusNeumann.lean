import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Polynomial Neumann matrices

Universal coefficient estimates for powers of a matrix of polynomials.
These estimates isolate the algebra behind the finite Haar-moment expansion:
nonnegative coefficients are preserved, every step adds a power of `X`,
and a triangle inequality for entry lengths prevents low-degree terms.
-/
open scoped BigOperators
open Matrix Polynomial
noncomputable section
namespace ProjectionChannels.NeumannPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every coefficient of every matrix entry is nonnegative. -/
def CoeffNonnegative (A : Matrix ι ι ℝ[X]) : Prop :=
  ∀ i j n, 0 ≤ (A i j).coeff n

/-- Entrywise coefficient nonnegativity is preserved by matrix products. -/
lemma coeffNonnegative_mul {A B : Matrix ι ι ℝ[X]}
    (hA : CoeffNonnegative A) (hB : CoeffNonnegative B) :
    CoeffNonnegative (A * B) := by
  intro i j n
  simp only [Matrix.mul_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_mul]
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (hA i u p.1) (hB u j p.2)

/-- Powers of a coefficientwise nonnegative polynomial matrix remain nonnegative. -/
theorem coeffNonnegative_pow {A : Matrix ι ι ℝ[X]}
    (hA : CoeffNonnegative A) (l : ℕ) : CoeffNonnegative (A ^ l) := by
  induction l with
  | zero =>
      intro i j n
      simp only [pow_zero, Matrix.one_apply]
      split_ifs
      · rw [Polynomial.coeff_one]
        split_ifs <;> norm_num
      · simp
  | succ l ih =>
      rw [pow_succ]
      exact coeffNonnegative_mul ih hA

/-- If every entry has zero constant coefficient, a walk of length `l`
has no coefficients below degree `l`. -/
theorem pow_coeff_eq_zero_of_lt_steps (A : Matrix ι ι ℝ[X])
    (hA : ∀ i j, (A i j).coeff 0 = 0) (l : ℕ) :
    ∀ i j n, n < l → ((A ^ l) i j).coeff n = 0 := by
  induction l with
  | zero => intro i j n hn; omega
  | succ l ih =>
      intro i j n hn
      simp only [pow_succ, Matrix.mul_apply, Polynomial.finset_sum_coeff]
      apply Finset.sum_eq_zero
      intro u _
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      have hp' := Finset.mem_antidiagonal.mp hp
      by_cases hpl : p.1 < l
      · rw [ih i u p.1 hpl, zero_mul]
      · have hpz : p.2 = 0 := by omega
        rw [hpz, hA u j, mul_zero]

/-- A length lower bound survives matrix multiplication along a triangle
inequality. This is the algebraic source of the genus filtration. -/
theorem pow_coeff_eq_zero_of_lt_distance
    (d : ι → ι → ℕ) (hdiag : ∀ i, d i i = 0)
    (htri : ∀ i u j, d i j ≤ d i u + d u j)
    (A : Matrix ι ι ℝ[X])
    (hA : ∀ i j n, n < d i j → (A i j).coeff n = 0) (l : ℕ) :
    ∀ i j n, n < d i j → ((A ^ l) i j).coeff n = 0 := by
  induction l with
  | zero =>
      intro i j n hn
      simp only [pow_zero, Matrix.one_apply]
      split_ifs with hij
      · subst j
        rw [hdiag] at hn
        omega
      · simp
  | succ l ih =>
      intro i j n hn
      simp only [pow_succ, Matrix.mul_apply, Polynomial.finset_sum_coeff]
      apply Finset.sum_eq_zero
      intro u _
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      have hp' := Finset.mem_antidiagonal.mp hp
      by_cases hpi : p.1 < d i u
      · rw [ih i u p.1 hpi, zero_mul]
      · have hpj : p.2 < d u j := by have := htri i u j; omega
        rw [hA u j p.2 hpj, mul_zero]

/-- The off-diagonal monomial matrix used in the normalized Haar Gram matrix. -/
def monomialMatrix (d : ι → ι → ℕ) : Matrix ι ι ℝ[X] :=
  fun i j => if i = j then 0 else Polynomial.X ^ d i j

lemma monomialMatrix_coeff_nonneg (d : ι → ι → ℕ) :
    CoeffNonnegative (monomialMatrix d) := by
  intro i j n
  unfold monomialMatrix
  split_ifs
  · simp
  · rw [Polynomial.coeff_X_pow]
    split_ifs <;> positivity

lemma monomialMatrix_coeff_zero (d : ι → ι → ℕ)
    (hpos : ∀ i j, i ≠ j → 0 < d i j) :
    ∀ i j, (monomialMatrix d i j).coeff 0 = 0 := by
  intro i j
  unfold monomialMatrix
  split_ifs with hij
  · simp
  · simp [Polynomial.coeff_X_pow, (hpos i j hij).ne]

lemma monomialMatrix_coeff_eq_zero_of_lt (d : ι → ι → ℕ) :
    ∀ i j n, n < d i j → (monomialMatrix d i j).coeff n = 0 := by
  intro i j n hn
  unfold monomialMatrix
  split_ifs
  · simp
  · simp [Polynomial.coeff_X_pow, Nat.ne_of_lt hn, (Nat.ne_of_lt hn).symm]

/-- Simultaneous coefficient nonnegativity and lower-degree estimates for
all powers, without any restriction on the matrix size or walk length. -/
theorem monomialMatrix_pow_coefficients
    (d : ι → ι → ℕ) (hdiag : ∀ i, d i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < d i j)
    (htri : ∀ i u j, d i j ≤ d i u + d u j)
    (l : ℕ) (i j : ι) (n : ℕ) :
    0 ≤ ((monomialMatrix d ^ l) i j).coeff n ∧
      (n < l ∨ n < d i j → ((monomialMatrix d ^ l) i j).coeff n = 0) := by
  constructor
  · exact coeffNonnegative_pow (monomialMatrix_coeff_nonneg d) l i j n
  · rintro (hn | hn)
    · exact pow_coeff_eq_zero_of_lt_steps _ (monomialMatrix_coeff_zero d hpos) l i j n hn
    · exact pow_coeff_eq_zero_of_lt_distance d hdiag htri _
        (monomialMatrix_coeff_eq_zero_of_lt d) l i j n hn

/-- A uniform degree bound on matrix entries grows linearly with the power. -/
theorem pow_natDegree_le (A : Matrix ι ι ℝ[X]) (D : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ D) (l : ℕ) :
    ∀ i j, ((A ^ l) i j).natDegree ≤ l * D := by
  induction l with
  | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply, zero_mul]
      split_ifs <;> simp
  | succ l ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro u _
      exact (Polynomial.natDegree_mul_le).trans (by
        simpa only [Nat.succ_mul] using add_le_add (ih i u) (hA u j))

/-- An additive parity label on paths determines the parity of every
nonzero coefficient of every matrix power. -/
theorem pow_coeff_eq_zero_of_parity
    (d : ι → ι → ℕ) (hdiag : ∀ i, d i i = 0)
    (hpar : ∀ i u j, (d i u + d u j) % 2 = d i j % 2)
    (A : Matrix ι ι ℝ[X])
    (hA : ∀ i j n, n % 2 ≠ d i j % 2 → (A i j).coeff n = 0) (l : ℕ) :
    ∀ i j n, n % 2 ≠ d i j % 2 → ((A ^ l) i j).coeff n = 0 := by
  induction l with
  | zero =>
      intro i j n hn
      simp only [pow_zero, Matrix.one_apply]
      split_ifs with hij
      · subst j
        have hn0 : n ≠ 0 := by intro hn0; subst n; simp [hdiag] at hn
        simp [Polynomial.coeff_one, hn0]
      · simp
  | succ l ih =>
      intro i j n hn
      simp only [pow_succ, Matrix.mul_apply, Polynomial.finset_sum_coeff]
      apply Finset.sum_eq_zero
      intro u _
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      have hp' := Finset.mem_antidiagonal.mp hp
      by_cases hpi : p.1 % 2 ≠ d i u % 2
      · rw [ih i u p.1 hpi, zero_mul]
      · have hpj : p.2 % 2 ≠ d u j % 2 := by
          have := hpar i u j
          omega
        rw [hA u j p.2 hpj, mul_zero]

lemma monomialMatrix_coeff_eq_zero_of_parity (d : ι → ι → ℕ) :
    ∀ i j n, n % 2 ≠ d i j % 2 → (monomialMatrix d i j).coeff n = 0 := by
  intro i j n hn
  have hne : n ≠ d i j := by intro h; exact hn (congrArg (fun x => x % 2) h)
  unfold monomialMatrix
  split_ifs <;> simp [Polynomial.coeff_X_pow, hne]

/-- The finite Neumann series through the indicated power. -/
def partialInverse (A : Matrix ι ι ℝ[X]) (L : ℕ) : Matrix ι ι ℝ[X] :=
  ∑ l ∈ Finset.range (L + 1), (-A) ^ l

/-- Coefficients through degree `n` cannot change after `n` Neumann terms. -/
theorem partialInverse_coeff_stable (A : Matrix ι ι ℝ[X])
    (hA : ∀ i j, (A i j).coeff 0 = 0)
    (n L : ℕ) (hL : n ≤ L) (i j : ι) :
    (partialInverse A L i j).coeff n = (partialInverse A n i j).coeff n := by
  have hneg : ∀ i j, ((-A) i j).coeff 0 = 0 := by
    intro i j
    simp [hA]
  simp only [partialInverse, Matrix.sum_apply, Polynomial.finset_sum_coeff]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hL 1))
  intro l _ hl
  exact pow_coeff_eq_zero_of_lt_steps (-A) hneg l i j n (by
    simp only [Finset.mem_range] at hl
    omega)

/-- A filtered matrix times a filtered polynomial vector has no coefficient
below the corresponding output filtration. -/
theorem mulVec_coeff_eq_zero_of_lt
    (d : ι → ι → ℕ) (e f : ι → ℕ)
    (hbound : ∀ i j, f i ≤ d i j + e j)
    (A : Matrix ι ι ℝ[X]) (v : ι → ℝ[X])
    (hA : ∀ i j n, n < d i j → (A i j).coeff n = 0)
    (hv : ∀ j n, n < e j → (v j).coeff n = 0)
    (i : ι) (n : ℕ) (hn : n < f i) :
    ((A *ᵥ v) i).coeff n = 0 := by
  simp only [Matrix.mulVec, dotProduct, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  by_cases hpi : p.1 < d i j
  · rw [hA i j p.1 hpi, zero_mul]
  · have hpj : p.2 < e j := by have := hbound i j; omega
    rw [hv j p.2 hpj, mul_zero]

/-- Relative-distance filtration for the finite inverse series. -/
theorem partialInverse_coeff_eq_zero_of_lt_distance
    (d : ι → ι → ℕ) (hdiag : ∀ i, d i i = 0)
    (htri : ∀ i u j, d i j ≤ d i u + d u j)
    (A : Matrix ι ι ℝ[X])
    (hA : ∀ i j n, n < d i j → (A i j).coeff n = 0)
    (L : ℕ) (i j : ι) (n : ℕ) (hn : n < d i j) :
    (partialInverse A L i j).coeff n = 0 := by
  have hneg : ∀ i j n, n < d i j → ((-A) i j).coeff n = 0 := by
    intro i j n hn
    simp [hA i j n hn]
  simp only [partialInverse, Matrix.sum_apply, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro l _
  exact pow_coeff_eq_zero_of_lt_distance d hdiag htri (-A) hneg l i j n hn

/-- Parity filtration for the finite inverse series. -/
theorem partialInverse_coeff_eq_zero_of_parity
    (d : ι → ι → ℕ) (hdiag : ∀ i, d i i = 0)
    (hpar : ∀ i u j, (d i u + d u j) % 2 = d i j % 2)
    (A : Matrix ι ι ℝ[X])
    (hA : ∀ i j n, n % 2 ≠ d i j % 2 → (A i j).coeff n = 0)
    (L : ℕ) (i j : ι) (n : ℕ) (hn : n % 2 ≠ d i j % 2) :
    (partialInverse A L i j).coeff n = 0 := by
  have hneg : ∀ i j n, n % 2 ≠ d i j % 2 → ((-A) i j).coeff n = 0 := by
    intro i j n hn
    simp [hA i j n hn]
  simp only [partialInverse, Matrix.sum_apply, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro l _
  exact pow_coeff_eq_zero_of_parity d hdiag hpar (-A) hneg l i j n hn

/-- Parity support also passes from a matrix and vector to their product. -/
theorem mulVec_coeff_eq_zero_of_parity
    (d : ι → ι → ℕ) (e f : ι → ℕ)
    (hbound : ∀ i j, (d i j + e j) % 2 = f i % 2)
    (A : Matrix ι ι ℝ[X]) (v : ι → ℝ[X])
    (hA : ∀ i j n, n % 2 ≠ d i j % 2 → (A i j).coeff n = 0)
    (hv : ∀ j n, n % 2 ≠ e j % 2 → (v j).coeff n = 0)
    (i : ι) (n : ℕ) (hn : n % 2 ≠ f i % 2) :
    ((A *ᵥ v) i).coeff n = 0 := by
  simp only [Matrix.mulVec, dotProduct, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  by_cases hpi : p.1 % 2 ≠ d i j % 2
  · rw [hA i j p.1 hpi, zero_mul]
  · have hpj : p.2 % 2 ≠ e j % 2 := by have := hbound i j; omega
    rw [hv j p.2 hpj, mul_zero]

/-- Stabilization also holds after multiplying by an arbitrary polynomial
vector; no convergence or infinite-series rearrangement is involved. -/
theorem partialInverse_mulVec_coeff_stable (A : Matrix ι ι ℝ[X])
    (hA : ∀ i j, (A i j).coeff 0 = 0) (v : ι → ℝ[X])
    (n L : ℕ) (hL : n ≤ L) (i : ι) :
    ((partialInverse A L *ᵥ v) i).coeff n =
      ((partialInverse A n *ᵥ v) i).coeff n := by
  simp only [Matrix.mulVec, dotProduct, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  have hpn : p.1 ≤ n := by omega
  rw [partialInverse_coeff_stable A hA p.1 L (hpn.trans hL),
    partialInverse_coeff_stable A hA p.1 n hpn]

#print axioms partialInverse_mulVec_coeff_stable
#print axioms partialInverse_coeff_stable
#print axioms pow_coeff_eq_zero_of_parity
#print axioms monomialMatrix_pow_coefficients
end ProjectionChannels.NeumannPolynomial
