import Entropy.Defs

/-! Exact coefficient and negative-root arithmetic for the final draft's Bell
limit. Analytic Cauchy-transform identities are not assumptions hidden in these
theorems: the assertions below are the displayed rational identities only. -/

noncomputable section
namespace BellLimitVerification

def denominator (k t : ℝ) := k ^ 4 * t - 2 * k ^ 2 * t + 1
def mixing (k t : ℝ) := k ^ 2 * (1 - t) / denominator k t
def hessianC1 (k t : ℝ) := -k * (1 - t) / denominator k t
def hessianC0 (k t : ℝ) := (-1 - k * hessianC1 k t) / k ^ 2
def bellAlpha (k t : ℝ) :=
  (k ^ 4 - (1 + t) * k ^ 2 + 1) / (k ^ 2 * denominator k t)
def bellBeta (k t : ℝ) :=
  (k ^ 2 - 1) * (k ^ 2 * t - 1) / (k ^ 2 * denominator k t)

lemma denominator_identity (k t : ℝ) :
    denominator k t = (k ^ 2 - 1) ^ 2 * t + 1 - t := by
  unfold denominator
  ring

lemma denominator_pos {k t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < denominator k t := by
  rw [denominator_identity]
  have := mul_nonneg (sq_nonneg (k ^ 2 - 1)) ht.le
  linarith

lemma mixing_mem_unit_interval {k t : ℝ}
    (hk : 1 < k) (ht : 0 < t) (ht1 : t < 1) (hkt : 1 < k ^ 2 * t) :
    0 < mixing k t ∧ mixing k t < 1 := by
  have hden := denominator_pos (k := k) ht ht1
  have hk2 : 1 < k ^ 2 := by nlinarith
  unfold mixing
  constructor
  · exact div_pos (mul_pos (by positivity) (by linarith)) hden
  · rw [div_lt_one hden]
    have hp := mul_pos (sub_pos.mpr hk2) (sub_pos.mpr hkt)
    unfold denominator
    nlinarith only [hp]

lemma hessian_bell_coefficients {k t : ℝ} (hk : k ≠ 0)
    (hden : denominator k t ≠ 0) :
    -hessianC0 k t = bellBeta k t ∧
    -hessianC1 k t = mixing k t / k ∧
    -hessianC0 k t - k * hessianC1 k t = bellAlpha k t := by
  unfold hessianC0 hessianC1 bellBeta mixing bellAlpha
  have hd : denominator k t = k ^ 4 * t - 2 * k ^ 2 * t + 1 := rfl
  constructor
  · field_simp
    rw [hd]
    ring
  constructor
  · field_simp
    <;> ring
  · field_simp
    rw [hd]
    ring

lemma bell_spectrum_identities {k t : ℝ} (hk : k ≠ 0)
    (hden : denominator k t ≠ 0) :
    bellBeta k t = (1 - mixing k t) / k ^ 2 ∧
    bellAlpha k t = bellBeta k t + mixing k t ∧
    bellAlpha k t + (k ^ 2 - 1) * bellBeta k t = 1 := by
  unfold bellBeta bellAlpha mixing
  have hd : denominator k t = k ^ 4 * t - 2 * k ^ 2 * t + 1 := rfl
  constructor
  · field_simp
    rw [hd]
    ring
  constructor
  · field_simp
    ring
  · field_simp
    rw [hd]
    ring

lemma bell_spectrum_positive {k t : ℝ}
    (hk : 1 < k) (ht : 0 < t) (ht1 : t < 1) (hkt : 1 < k ^ 2 * t) :
    0 < bellBeta k t ∧ bellBeta k t < bellAlpha k t := by
  have hk0 : k ≠ 0 := ne_of_gt (lt_trans zero_lt_one hk)
  have hd := denominator_pos (k := k) ht ht1
  have hm := mixing_mem_unit_interval hk ht ht1 hkt
  have hi := bell_spectrum_identities hk0 hd.ne'
  constructor
  · rw [hi.1]
    exact div_pos (by linarith) (sq_pos_of_ne_zero hk0)
  · rw [hi.2.1]
    linarith

/-- The candidate negative inverse-Cauchy root satisfies the Bernoulli quadratic.
Here `q = k²`, `g = -1/q`, and `y = w/k`. This proves the arithmetic substitution,
not the analytic identification of `g` with the Bernoulli branch. -/
lemma negative_root_arithmetic {q t : ℝ} (hq : 1 < q) (hqt : 1 < q * t) :
    let y := -(q - 1) / (q * (q * t - 1))
    let g := -1 / q
    y < 0 ∧ g ^ 2 + (1 - y) * g - t * y = 0 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hden : 0 < q * (q * t - 1) := mul_pos hq0 (sub_pos.mpr hqt)
  dsimp
  constructor
  · exact div_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hq)) hden
  · field_simp
    <;> ring

/-- Substituting `g=-1/k²` into the Bernoulli derivative quotient gives the
Hessian coefficient in the paper. -/
lemma bernoulli_derivative_substitution {k t : ℝ} (hk : k ≠ 0)
    (hden : denominator k t ≠ 0) :
    -k * (((-1 / k ^ 2) ^ 2 * (1 - t)) /
      ((-1 / k ^ 2) ^ 2 + 2 * t * (-1 / k ^ 2) + t)) = hessianC1 k t := by
  have hq : (-1 / k ^ 2) ^ 2 + 2 * t * (-1 / k ^ 2) + t =
      denominator k t / k ^ 4 := by
    unfold denominator
    field_simp
    <;> ring
  rw [hq]
  unfold hessianC1
  field_simp
  <;> ring

#print axioms denominator_identity
#print axioms denominator_pos
#print axioms mixing_mem_unit_interval
#print axioms hessian_bell_coefficients
#print axioms bell_spectrum_identities
#print axioms bell_spectrum_positive
#print axioms negative_root_arithmetic
#print axioms bernoulli_derivative_substitution
end BellLimitVerification
