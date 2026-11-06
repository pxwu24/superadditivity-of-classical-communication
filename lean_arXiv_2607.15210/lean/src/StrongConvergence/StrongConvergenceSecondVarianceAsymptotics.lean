import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Scalar asymptotics of the exact second-moment variance

This file proves algebra and limits for the rational expressions obtained from
fourth-order Haar integration. No probabilistic estimate is a hypothesis of
these lemmas. Connecting the rational expression to the Haar integral is a
separate finite-dimensional calculation.
-/

open Filter
open scoped Topology
noncomputable section

namespace ProjectionChannels.SecondVariance

/-- The normalized second trace, in rank density `q` and inverse dimension
squared `x`. The parameters `pⱼ` are the power sums of the coefficients. -/
def mean (k q x p₁ p₂ : ℝ) : ℝ :=
  q * (q - x) / (1 - x) * p₁ ^ 2 +
    q * (1 - q) / (k * (1 - x)) * p₂

def denominator (x : ℝ) : ℝ := (1 - x) * (1 - 4*x) * (1 - 9*x)

/-- Scaled inverse-Gram projection coefficient for the identity class. -/
def coeffId (q x : ℝ) : ℝ :=
  q * (q^3 + (-6*q^2 - 8*q^3)*x +
    (19*q + 24*q^2 + 6*q^3)*x^2 + (-30 - 6*q)*x^3) / denominator x

def coeffTransposition (q x : ℝ) : ℝ :=
  q * (1-q) * (q^2 + (-5*q - 4*q^2)*x + 10*x^2) / denominator x

def coeffDoubleTransposition (q x : ℝ) : ℝ :=
  q * (1-q) * (q - q^2 + (-4 + 6*q - 6*q^2)*x + 6*x^2) / denominator x

def coeffThreeCycle (q x : ℝ) : ℝ :=
  q * (1-q) * (q - 2*q^2 + (-3 + 6*q + 3*q^2)*x - 3*x^2) / denominator x

def coeffFourCycle (q x : ℝ) : ℝ :=
  q * (1-q) * (1 - 5*q + 5*q^2 + x) / denominator x

/-- The normalized two-trace expression computed by the five permutation
conjugacy classes in `S₄`. -/
def squareMean (k q x p₁ p₂ p₃ p₄ : ℝ) : ℝ :=
  coeffId q x * p₁^4 +
  (2/k + 4*k*x) * coeffTransposition q x * p₁^2*p₂ +
  (1/k^2 + 2*x) * coeffDoubleTransposition q x * p₂^2 +
  8*x * coeffThreeCycle q x * p₁*p₃ +
  (4*x/k + 2*k*x^2) * coeffFourCycle q x * p₄

/-- Polynomial coefficients after cancellation of the leading variance term. -/
def polyId (k q x : ℝ) : ℝ :=
  k^2 * (3*q^2*x^2 + 11*q^2*x - 2*q^2 - 21*q*x^2 + 9*q*x +
    15*x^3 - 15*x^2)
def polyTransposition (k q x : ℝ) : ℝ :=
  (-2*k) * (-4*k^2*q^2*x^2 + 5*k^2*q^2*x - k^2*q^2 -
    5*k^2*q*x^2 + 5*k^2*q*x + 10*k^2*x^3 - 10*k^2*x^2 +
    16*q^2*x - 4*q^2 - 18*q*x^2 + 4*q*x + 2*q + 5*x^2 - 5*x)
def polyThreeCycle (k q x : ℝ) : ℝ :=
  4*k^2*(x-1)*(-3*q^2*x + 2*q^2 - 6*q*x - q + 3*x^2 + 3*x)
def polyDoubleTransposition (k q x : ℝ) : ℝ :=
  6*k^2*q^2*x^2 - 5*k^2*q^2*x - k^2*q^2 - 6*k^2*q*x^2 +
    5*k^2*q*x + k^2*q - 6*k^2*x^3 + 10*k^2*x^2 - 4*k^2*x +
    21*q^2*x - 9*q^2 - 21*q*x + 9*q - 3*x^2 + 5*x - 2
def polyFourCycle (k q x : ℝ) : ℝ :=
  (-k)*(x-1)*(k^2*x+2)*(5*q^2 - 5*q + x + 1)
def numerator (k q x p₁ p₂ p₃ p₄ : ℝ) : ℝ :=
  polyId k q x * p₁^4 + polyTransposition k q x * p₁^2*p₂ +
  polyThreeCycle k q x * p₁*p₃ + polyDoubleTransposition k q x * p₂^2 +
  polyFourCycle k q x * p₄

def scale (k q x : ℝ) : ℝ :=
  2*q*(1-q) / (k^2 * (1-x)^2 * (1-4*x) * (1-9*x))

def kernel (k q x p₁ p₂ p₃ p₄ : ℝ) : ℝ :=
  scale k q x * numerator k q x p₁ p₂ p₃ p₄

private lemma cancel_id (k q x : ℝ)
    (hk : k ≠ 0) (h₁ : 1-x ≠ 0) (h₄ : 1-4*x ≠ 0) (h₉ : 1-9*x ≠ 0) :
    coeffId q x - (q*(q-x)/(1-x))^2 = x * scale k q x * polyId k q x := by
  unfold coeffId denominator scale polyId
  field_simp [hk, h₁, h₄, h₉]
  <;> ring

private lemma cancel_transposition (k q x : ℝ)
    (hk : k ≠ 0) (h₁ : 1-x ≠ 0) (h₄ : 1-4*x ≠ 0) (h₉ : 1-9*x ≠ 0) :
    (2/k + 4*k*x)*coeffTransposition q x -
      2*(q*(q-x)/(1-x))*(q*(1-q)/(k*(1-x))) =
        x * scale k q x * polyTransposition k q x := by
  unfold coeffTransposition denominator scale polyTransposition
  field_simp [hk, h₁, h₄, h₉]
  <;> ring

private lemma cancel_double (k q x : ℝ)
    (hk : k ≠ 0) (h₁ : 1-x ≠ 0) (h₄ : 1-4*x ≠ 0) (h₉ : 1-9*x ≠ 0) :
    (1/k^2 + 2*x)*coeffDoubleTransposition q x - (q*(1-q)/(k*(1-x)))^2 =
        x * scale k q x * polyDoubleTransposition k q x := by
  unfold coeffDoubleTransposition denominator scale polyDoubleTransposition
  field_simp [hk, h₁, h₄, h₉]
  <;> ring

private lemma cancel_three (k q x : ℝ)
    (hk : k ≠ 0) (h₁ : 1-x ≠ 0) (h₄ : 1-4*x ≠ 0) (h₉ : 1-9*x ≠ 0) :
    8*x*coeffThreeCycle q x = x * scale k q x * polyThreeCycle k q x := by
  unfold coeffThreeCycle denominator scale polyThreeCycle
  field_simp [hk, h₁, h₄, h₉]
  <;> ring

private lemma cancel_four (k q x : ℝ)
    (hk : k ≠ 0) (h₁ : 1-x ≠ 0) (h₄ : 1-4*x ≠ 0) (h₉ : 1-9*x ≠ 0) :
    (4*x/k + 2*k*x^2)*coeffFourCycle q x = x * scale k q x * polyFourCycle k q x := by
  unfold coeffFourCycle denominator scale polyFourCycle
  field_simp [hk, h₁, h₄, h₉]
  <;> ring

/-- Exact cancellation of the constant-order term in the variance. -/
theorem squareMean_sub_mean_sq (k q x p₁ p₂ p₃ p₄ : ℝ)
    (hk : k ≠ 0) (h₁ : 1-x ≠ 0) (h₄ : 1-4*x ≠ 0) (h₉ : 1-9*x ≠ 0) :
    squareMean k q x p₁ p₂ p₃ p₄ - (mean k q x p₁ p₂)^2 =
      x * kernel k q x p₁ p₂ p₃ p₄ := by
  calc
    _ = (coeffId q x - (q*(q-x)/(1-x))^2) * p₁^4 +
        ((2/k + 4*k*x)*coeffTransposition q x -
          2*(q*(q-x)/(1-x))*(q*(1-q)/(k*(1-x)))) * p₁^2*p₂ +
        ((1/k^2 + 2*x)*coeffDoubleTransposition q x - (q*(1-q)/(k*(1-x)))^2)*p₂^2 +
        (8*x*coeffThreeCycle q x)*p₁*p₃ +
        ((4*x/k + 2*k*x^2)*coeffFourCycle q x)*p₄ := by
      unfold squareMean mean
      ring
    _ = _ := by
      rw [cancel_id k q x hk h₁ h₄ h₉, cancel_transposition k q x hk h₁ h₄ h₉,
        cancel_double k q x hk h₁ h₄ h₉, cancel_three k q x hk h₁ h₄ h₉,
        cancel_four k q x hk h₁ h₄ h₉]
      unfold kernel numerator
      ring

/-- The rational variance expression at an arbitrary nonzero input size. -/
def variance (k q n p₁ p₂ p₃ p₄ : ℝ) : ℝ :=
  squareMean k q ((1/(k*n))^2) p₁ p₂ p₃ p₄ -
    (mean k q ((1/(k*n))^2) p₁ p₂)^2

theorem scaled_variance_eq (k q n p₁ p₂ p₃ p₄ : ℝ)
    (hk : k ≠ 0) (hn : n ≠ 0)
    (h₁ : 1-(1/(k*n))^2 ≠ 0) (h₄ : 1-4*(1/(k*n))^2 ≠ 0)
    (h₉ : 1-9*(1/(k*n))^2 ≠ 0) :
    n^2 * variance k q n p₁ p₂ p₃ p₄ =
      kernel k q ((1/(k*n))^2) p₁ p₂ p₃ p₄ / k^2 := by
  rw [variance, squareMean_sub_mean_sq k q _ p₁ p₂ p₃ p₄ hk h₁ h₄ h₉]
  field_simp [hk, hn]
  <;> ring

lemma continuousAt_kernel (k t p₁ p₂ p₃ p₄ : ℝ) (hk : k ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ => kernel k z.1 z.2 p₁ p₂ p₃ p₄) (t, 0) := by
  unfold kernel numerator scale polyId polyTransposition polyThreeCycle
    polyDoubleTransposition polyFourCycle
  fun_prop (disch := simp [hk])

/-- For any rank-density sequence tending to `t`, the variance multiplied
by the input dimension squared has a finite limit. -/
theorem scaled_variance_tendsto {q : ℕ → ℝ} {t k : ℝ}
    (hq : Tendsto q atTop (𝓝 t)) (hk : k ≠ 0) (p₁ p₂ p₃ p₄ : ℝ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2 * variance k (q n) ((n:ℝ)+1) p₁ p₂ p₃ p₄)
      atTop (𝓝 (kernel k t 0 p₁ p₂ p₃ p₄ / k^2)) := by
  have hi : Tendsto (fun n : ℕ => 1 / (k*((n:ℝ)+1))) atTop (𝓝 (0:ℝ)) := by
    simpa only [div_div, mul_comm, zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.div_const k)
  have hx := hi.pow 2
  have hx' : Tendsto (fun n : ℕ => (1 / (k*((n:ℝ)+1)))^2) atTop (𝓝 (0:ℝ)) := by
    simpa using hx
  have h₁ : ∀ᶠ n : ℕ in atTop, 1-(1/(k*((n:ℝ)+1)))^2 ≠ 0 :=
    (tendsto_const_nhds.sub hx').eventually (eventually_ne_nhds (by norm_num))
  have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 (1:ℝ)) := tendsto_const_nhds
  have h₄ : ∀ᶠ n : ℕ in atTop, 1-4*(1/(k*((n:ℝ)+1)))^2 ≠ 0 := by
    exact (hc.sub (hx'.const_mul 4)).eventually (eventually_ne_nhds (by norm_num))
  have h₉ : ∀ᶠ n : ℕ in atTop, 1-9*(1/(k*((n:ℝ)+1)))^2 ≠ 0 := by
    exact (hc.sub (hx'.const_mul 9)).eventually (eventually_ne_nhds (by norm_num))
  have h := ((continuousAt_kernel k t p₁ p₂ p₃ p₄ hk).tendsto.comp
    (hq.prodMk_nhds hx')).div_const (k^2)
  apply h.congr'
  filter_upwards [h₁, h₄, h₉] with n hn₁ hn₄ hn₉
  exact (scaled_variance_eq k (q n) ((n:ℝ)+1) p₁ p₂ p₃ p₄ hk
    (by positivity) hn₁ hn₄ hn₉).symm

/-- The exact rational variance expression is eventually bounded by a
constant times the summable inverse square of the input dimension. -/
theorem exists_eventually_variance_le {q : ℕ → ℝ} {t k : ℝ}
    (hq : Tendsto q atTop (𝓝 t)) (hk : k ≠ 0) (p₁ p₂ p₃ p₄ : ℝ) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      variance k (q n) ((n:ℝ)+1) p₁ p₂ p₃ p₄ ≤ C/((n:ℝ)+1)^2 := by
  let L := kernel k t 0 p₁ p₂ p₃ p₄ / k^2
  refine ⟨L+1, ?_⟩
  have h := (scaled_variance_tendsto hq hk p₁ p₂ p₃ p₄).eventually
    (gt_mem_nhds (lt_add_one L))
  filter_upwards [h] with n hn
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : (0:ℝ) < (n:ℝ)+1))).mpr
  simpa only [mul_comm] using hn.le

end ProjectionChannels.SecondVariance

#print axioms ProjectionChannels.SecondVariance.squareMean_sub_mean_sq
#print axioms ProjectionChannels.SecondVariance.scaled_variance_tendsto
#print axioms ProjectionChannels.SecondVariance.exists_eventually_variance_le
