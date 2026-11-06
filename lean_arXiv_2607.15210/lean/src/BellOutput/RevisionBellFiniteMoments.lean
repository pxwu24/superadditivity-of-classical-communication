import BellOutput.RevisionBellMatrixLog
import BellOutput.RevisionBellContraction
import BellOutput.RevisionBellPolarization
import Entropy.BellLimitTransfer

/-! Proposition A.3: the uniform finite-dimensional estimate with the actual
normalized block map. Analytic convergence inputs remain explicit. -/

open Finset Filter
open PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace RevisionBell

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]

theorem contraction_affine (P : Matrix (A × B) (A × B) ℂ)
    (H : Matrix B B ℂ) (x : ℝ) :
    contraction P (1+(x : ℂ) • H)=traceB P+(x : ℂ) • contraction P H := by
  have hlin : contraction P (1+(x : ℂ) • H)=
      contraction P 1+(x : ℂ) • contraction P H := by
    ext a b
    simp [contraction_entry, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rwa [contraction_one] at hlin

theorem contraction_negative_affine (P : Matrix (A × B) (A × B) ℂ)
    (H : Matrix B B ℂ) (x : ℝ) :
    contraction P (1-(x : ℂ) • H)=traceB P-(x : ℂ) • contraction P H := by
  simpa [sub_eq_add_neg] using contraction_affine P H (-x)

def matrixLogPotential (P : Matrix (A × B) (A × B) ℂ) (X : Matrix B B ℂ) : ℝ :=
  normalizedLogAbsDet (contraction P X)

/-- Equation (103), obtained from genuine matrix spectral decompositions and
the actual positive unital adjoint. The bound is uniform in the input size. -/
theorem matrixLogPotential_central_remainder
    {P : Matrix (A × B) (A × B) ℂ} (hP : P.PosSemidef)
    (D : Matrix A A ℂ) (hD : D.IsHermitian) (hn : D*traceB P*D=1)
    (H : Matrix B B ℂ) (hH : H.IsHermitian) (x : ℝ) (hx : x ≠ 0)
    (hsmall : |x| * ‖H‖ ≤ 1/2) :
    |(matrixLogPotential P (1+(x : ℂ) • H)+
        matrixLogPotential P (1-(x : ℂ) • H)-2*matrixLogPotential P 1)/x^2 +
      (1/(Fintype.card A : ℝ))*(Matrix.trace
        ((D*contraction P H*D)*(D*contraction P H*D))).re|
      ≤ 2*x^2*‖H‖^4 := by
  have hnorm := BellLimitVerification.normalized_contraction_opNorm_le hP D hD hn H hH
  have hC := hermitian_sandwich (contraction_isHermitian hP.isHermitian hH) hD
  have hs : |x| * ‖D*contraction P H*D‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hnorm (abs_nonneg x)).trans hsmall
  unfold matrixLogPotential
  rw [contraction_affine, contraction_negative_affine, contraction_one]
  apply (normalizedLogAbsDet_local_central_remainder (traceB P) (contraction P H) D hn hC x hx hs).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 4) (by positivity)

/-- Countable-step passage from log-potential convergence to genuine normalized
matrix square moments. The uniform finite-difference error is proved above,
not supplied as a hypothesis. -/
theorem matrix_square_moment_limit
    (A : ℕ → Type) [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)] [∀ n, Nonempty (A n)]
    (P : ∀ n, Matrix (A n × B) (A n × B) ℂ)
    (D : ∀ n, Matrix (A n) (A n) ℂ)
    (hP : ∀ n, (P n).PosSemidef) (hD : ∀ n, (D n).IsHermitian)
    (hn : ∀ n, D n*traceB (P n)*D n=1)
    (H : Matrix B B ℂ) (hH : H.IsHermitian)
    (F : ℝ → ℝ) (L : ℝ) (step : ℕ → ℝ)
    (hstep : Tendsto step atTop (nhds 0)) (hstep0 : ∀ j, step j ≠ 0)
    (hsmall : ∀ j, |step j| * ‖H‖ ≤ 1/2)
    (hpoint : ∀ j, Tendsto (fun n => matrixLogPotential (P n) (1+(step j : ℂ) • H))
      atTop (nhds (F (step j))))
    (hneg : ∀ j, Tendsto (fun n => matrixLogPotential (P n) (1-(step j : ℂ) • H))
      atTop (nhds (F (-step j))))
    (hzero : Tendsto (fun n => matrixLogPotential (P n) 1) atTop (nhds (F 0)))
    (hsecond : Tendsto (fun j => BellLimitVerification.centralDifference F (step j)) atTop (nhds L)) :
    Tendsto (fun n => (1/(Fintype.card (A n) : ℝ))*(Matrix.trace
      ((D n*contraction (P n) H*D n)*(D n*contraction (P n) H*D n))).re)
      atTop (nhds (-L)) := by
  apply BellLimitVerification.moment_limit_of_central_differences
    (fun n x => matrixLogPotential (P n) (1+(x : ℂ) • H)) F
    _ step (fun j => 2*(step j)^2*‖H‖^4) L
  · exact hpoint
  · intro j
    simpa only [Complex.ofReal_neg, neg_smul, ← sub_eq_add_neg] using hneg j
  · simpa using hzero
  · exact hsecond
  · simpa using ((hstep.pow 2).const_mul 2).mul_const (‖H‖^4)
  · intro j
    apply Filter.Eventually.of_forall
    intro n
    have h := matrixLogPotential_central_remainder (hP n) (D n) (hD n) (hn n)
      H hH (step j) (hstep0 j) (hsmall j)
    convert h using 1
    simp only [BellLimitVerification.centralDifference, Complex.ofReal_neg, neg_smul,
      sub_eq_add_neg, Complex.ofReal_zero, zero_smul, add_zero]
    congr 1
    ring

theorem matrix_square_moment_limit_eventual_normalization
    (A : ℕ → Type) [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)] [∀ n, Nonempty (A n)]
    (P : ∀ n, Matrix (A n × B) (A n × B) ℂ)
    (D : ∀ n, Matrix (A n) (A n) ℂ)
    (hP : ∀ n, (P n).PosSemidef) (hD : ∀ n, (D n).IsHermitian)
    (hn : ∀ᶠ n in atTop, D n*traceB (P n)*D n=1)
    (H : Matrix B B ℂ) (hH : H.IsHermitian)
    (F : ℝ → ℝ) (L : ℝ) (step : ℕ → ℝ)
    (hstep : Tendsto step atTop (nhds 0)) (hstep0 : ∀ j, step j ≠ 0)
    (hsmall : ∀ j, |step j| * ‖H‖ ≤ 1/2)
    (hpoint : ∀ j, Tendsto (fun n => matrixLogPotential (P n) (1+(step j : ℂ) • H))
      atTop (nhds (F (step j))))
    (hneg : ∀ j, Tendsto (fun n => matrixLogPotential (P n) (1-(step j : ℂ) • H))
      atTop (nhds (F (-step j))))
    (hzero : Tendsto (fun n => matrixLogPotential (P n) 1) atTop (nhds (F 0)))
    (hsecond : Tendsto (fun j => BellLimitVerification.centralDifference F (step j)) atTop (nhds L)) :
    Tendsto (fun n => (1/(Fintype.card (A n) : ℝ))*(Matrix.trace
      ((D n*contraction (P n) H*D n)*(D n*contraction (P n) H*D n))).re)
      atTop (nhds (-L)) := by
  apply BellLimitVerification.moment_limit_of_central_differences
    (fun n x => matrixLogPotential (P n) (1+(x : ℂ) • H)) F
    _ step (fun j => 2*(step j)^2*‖H‖^4) L
  · exact hpoint
  · intro j
    simpa only [Complex.ofReal_neg, neg_smul, ← sub_eq_add_neg] using hneg j
  · simpa using hzero
  · exact hsecond
  · simpa using ((hstep.pow 2).const_mul 2).mul_const (‖H‖^4)
  · intro j
    filter_upwards [hn] with n hnN
    have h := matrixLogPotential_central_remainder (hP n) (D n) (hD n) hnN
      H hH (step j) (hstep0 j) (hsmall j)
    convert h using 1
    simp only [BellLimitVerification.centralDifference, Complex.ofReal_neg, neg_smul,
      sub_eq_add_neg, Complex.ofReal_zero, zero_smul, add_zero]
    congr 1
    ring

end RevisionBell
