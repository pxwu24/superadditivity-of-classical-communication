import BellOutput.RevisionBellChannel
import Entropy.BellFiniteDifference
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! The finite-dimensional matrix logarithm/determinant calculation in
Proposition A.3. The remainder is proved for actual Hermitian matrices. -/

open Finset
open scoped BigOperators Matrix.L2OpNorm
noncomputable section
namespace RevisionBell

variable {N : Type*} [Fintype N] [DecidableEq N]

def normalizedLogAbsDet (A : Matrix N N ℂ) : ℝ :=
  (1/(Fintype.card N : ℝ))*Real.log ‖A.det‖

theorem normalizedLogAbsDet_eq_spectralMean
    (C : Matrix N N ℂ) (hC : C.IsHermitian)
    (hpos : ∀ i, 0 < hC.eigenvalues i) :
    normalizedLogAbsDet C =
      (1/(Fintype.card N : ℝ))*∑ i, Real.log (hC.eigenvalues i) := by
  unfold normalizedLogAbsDet
  rw [hC.det_eq_prod_eigenvalues, norm_prod]
  simp only [RCLike.norm_ofReal, Real.norm_eq_abs, abs_of_pos (hpos _)]
  rw [Real.log_prod Finset.univ _ (fun i _ => (hpos i).ne')]

theorem affine_matrix_spectral (C : Matrix N N ℂ) (hC : C.IsHermitian) (x : ℝ) :
    1+(x : ℂ) • C =
      (hC.eigenvectorUnitary : Matrix N N ℂ) *
        Matrix.diagonal (fun i => ((1+x*hC.eigenvalues i : ℝ) : ℂ)) *
        (hC.eigenvectorUnitary : Matrix N N ℂ).conjTranspose := by
  have hd : Matrix.diagonal (fun i => ((1+x*hC.eigenvalues i : ℝ) : ℂ)) =
      (1 : Matrix N N ℂ)+(x : ℂ) • Matrix.diagonal (fun i => (hC.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hU : (hC.eigenvectorUnitary : Matrix N N ℂ) *
      (hC.eigenvectorUnitary : Matrix N N ℂ).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hC.eigenvectorUnitary.2
  rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, hU]
  congr 1
  exact congrArg (fun X : Matrix N N ℂ => (x : ℂ) • X) hC.spectral_theorem

theorem det_affine_eq_prod (C : Matrix N N ℂ) (hC : C.IsHermitian) (x : ℝ) :
    (1+(x : ℂ) • C).det = ∏ i, ((1+x*hC.eigenvalues i : ℝ) : ℂ) := by
  rw [affine_matrix_spectral C hC x, Matrix.det_mul_right_comm]
  have hU : (hC.eigenvectorUnitary : Matrix N N ℂ) *
      (hC.eigenvectorUnitary : Matrix N N ℂ).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hC.eigenvectorUnitary.2
  rw [hU]
  simp

theorem trace_eq_eigenvalue_sum (C : Matrix N N ℂ) (hC : C.IsHermitian) :
    Matrix.trace C = ∑ i, ((hC.eigenvalues i : ℝ) : ℂ) := by
  have hU : (hC.eigenvectorUnitary : Matrix N N ℂ).conjTranspose *
      (hC.eigenvectorUnitary : Matrix N N ℂ)=1 :=
    Matrix.mem_unitaryGroup_iff'.mp hC.eigenvectorUnitary.2
  calc
    Matrix.trace C = Matrix.trace ((hC.eigenvectorUnitary : Matrix N N ℂ)*
      Matrix.diagonal (fun i => (hC.eigenvalues i : ℂ))*
      (hC.eigenvectorUnitary : Matrix N N ℂ).conjTranspose) := congrArg Matrix.trace hC.spectral_theorem
    _ = _ := by rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

theorem trace_re_eq_eigenvalue_sum (C : Matrix N N ℂ) (hC : C.IsHermitian) :
    (Matrix.trace C).re = ∑ i, hC.eigenvalues i := by
  rw [trace_eq_eigenvalue_sum C hC]
  simp

theorem logAbsDet_affine_eq_sum (C : Matrix N N ℂ) (hC : C.IsHermitian) (x : ℝ)
    (hpos : ∀ i, 0 < 1+x*hC.eigenvalues i) :
    Real.log ‖(1+(x : ℂ) • C).det‖ = ∑ i, Real.log (1+x*hC.eigenvalues i) := by
  rw [det_affine_eq_prod C hC x, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _)]
  exact Real.log_prod Finset.univ _ (fun i _ => (hpos i).ne')

theorem trace_square_eq_eigenvalue_squares (C : Matrix N N ℂ) (hC : C.IsHermitian) :
    Matrix.trace (C*C) = ∑ i, ((hC.eigenvalues i : ℝ) : ℂ)^2 := by
  let U : Matrix N N ℂ := hC.eigenvectorUnitary
  let D : Matrix N N ℂ := Matrix.diagonal (fun i => (hC.eigenvalues i : ℂ))
  have hC' : C=U*D*U.conjTranspose := hC.spectral_theorem
  have hU : U.conjTranspose*U=1 := by
    exact (Matrix.mem_unitaryGroup_iff').mp hC.eigenvectorUnitary.2
  have hmul : (U*D*U.conjTranspose)*(U*D*U.conjTranspose) = U*(D*D)*U.conjTranspose := by
    calc
      _ = U*D*(U.conjTranspose*U)*D*U.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  calc
    Matrix.trace (C*C) = Matrix.trace ((U.conjTranspose*U)*(D*D)) := by
      conv_lhs => rw [hC', hmul, Matrix.trace_mul_cycle]
    _ = ∑ i, ((hC.eigenvalues i : ℝ) : ℂ)^2 := by
      rw [hU]
      simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]

theorem trace_square_re_eq_eigenvalue_squares (C : Matrix N N ℂ) (hC : C.IsHermitian) :
    (Matrix.trace (C*C)).re = ∑ i, (hC.eigenvalues i)^2 := by
  rw [trace_square_eq_eigenvalue_squares C hC]
  simp [pow_two, Complex.mul_re]

theorem eigenvalue_abs_le_operator_norm [Nonempty N]
    (C : Matrix N N ℂ) (hC : C.IsHermitian) (i : N) :
    |hC.eigenvalues i| ≤ ‖C‖ := by
  simpa only [Real.norm_eq_abs] using
    (spectrum.norm_le_norm_of_mem (hC.eigenvalues_mem_spectrum_real i))

theorem affine_eigenvalues_pos [Nonempty N]
    (C : Matrix N N ℂ) (hC : C.IsHermitian) (x : ℝ)
    (hsmall : |x| *‖C‖ ≤ 1/2) (i : N) :
    0 < 1+x*hC.eigenvalues i := by
  have habs : |x*hC.eigenvalues i| ≤ 1/2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (eigenvalue_abs_le_operator_norm C hC i) (abs_nonneg x)).trans hsmall
  linarith [neg_abs_le (x*hC.eigenvalues i)]

theorem det_affine_ne_zero [Nonempty N]
    (C : Matrix N N ℂ) (hC : C.IsHermitian) (x : ℝ)
    (hsmall : |x| *‖C‖ ≤ 1/2) :
    (1+(x : ℂ) • C).det ≠ 0 := by
  rw [det_affine_eq_prod C hC x]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact_mod_cast (affine_eigenvalues_pos C hC x hsmall i).ne'

/-- The exact uniform matrix remainder in (103), with the stronger constant
`2`. Its quadratic term is the normalized trace of the actual square matrix. -/
theorem normalizedLogAbsDet_central_remainder [Nonempty N]
    (C : Matrix N N ℂ) (hC : C.IsHermitian) (x : ℝ) (hx : x ≠ 0)
    (hsmall : |x| *‖C‖ ≤ 1/2) :
    |(normalizedLogAbsDet (1+(x : ℂ) • C)+
        normalizedLogAbsDet (1-(x : ℂ) • C))/x^2 +
      (1/(Fintype.card N : ℝ))*(Matrix.trace (C*C)).re|
      ≤ 2*x^2*‖C‖^4 := by
  have hN : (Fintype.card N : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card N ≠ 0)
  have hrem := BellLimitVerification.weighted_log_central_remainder Finset.univ
    (fun _ : N => 1/(Fintype.card N : ℝ)) hC.eigenvalues ‖C‖ x
    (fun _ _ => by positivity)
    (by simp [hN])
    (fun i _ => eigenvalue_abs_le_operator_norm C hC i) hx hsmall
  have hm : |(-x)| *‖C‖ ≤ 1/2 := by simpa using hsmall
  have hp := logAbsDet_affine_eq_sum C hC x (affine_eigenvalues_pos C hC x hsmall)
  have hn := logAbsDet_affine_eq_sum C hC (-x) (affine_eigenvalues_pos C hC (-x) hm)
  have htrace : (Matrix.trace (C*C)).re = ∑ i, (hC.eigenvalues i)^2 := by
    rw [trace_square_eq_eigenvalue_squares C hC]
    simp [pow_two, Complex.mul_re]
  have hminus : (1-(x : ℂ) • C) = 1+((-x : ℝ) : ℂ) • C := by
    simp only [Complex.ofReal_neg, neg_smul, sub_eq_add_neg]
  rw [hminus]
  unfold normalizedLogAbsDet
  rw [hp,hn,htrace]
  dsimp only at hrem
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib] at hrem
  convert hrem using 1
  congr 1
  simp only [neg_mul, ← sub_eq_add_neg]
  ring

theorem normalizedLogAbsDet_congruence
    (D M : Matrix N N ℂ) (hD : D.det ≠ 0) (hM : M.det ≠ 0) :
    normalizedLogAbsDet (D*M*D) =
      2*normalizedLogAbsDet D+normalizedLogAbsDet M := by
  unfold normalizedLogAbsDet
  simp only [Matrix.det_mul, norm_mul]
  rw [Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr hM))
    (norm_ne_zero_iff.mpr hD),
    Real.log_mul (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr hM)]
  ring

/-- The determinant identity (102) before dividing by the step size. -/
theorem normalizedLogAbsDet_affine_congruence
    (A H D : Matrix N N ℂ) (hn : D*A*D=1) (x : ℝ)
    (hshift : (1+(x : ℂ) • (D*H*D)).det ≠ 0) :
    normalizedLogAbsDet (A+(x : ℂ) • H)-normalizedLogAbsDet A =
      normalizedLogAbsDet (1+(x : ℂ) • (D*H*D)) := by
  have hdets : D.det*A.det*D.det=1 := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, hn, Matrix.det_one]
  have hD : D.det ≠ 0 := by intro hz; simp [hz] at hdets
  have hA : A.det ≠ 0 := by intro hz; simp [hz] at hdets
  have haffine : D*(A+(x : ℂ) • H)*D=1+(x : ℂ) • (D*H*D) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hn]
  have hM : (A+(x : ℂ) • H).det ≠ 0 := by
    intro hz
    apply hshift
    rw [← haffine, Matrix.det_mul, Matrix.det_mul, hz]
    ring
  have hbase := normalizedLogAbsDet_congruence D A hD hA
  rw [hn] at hbase
  have hpoint := normalizedLogAbsDet_congruence D (A+(x : ℂ) • H) hD hM
  rw [haffine] at hpoint
  have hone : normalizedLogAbsDet (1 : Matrix N N ℂ)=0 := by simp [normalizedLogAbsDet]
  rw [hone] at hbase
  linarith

/-- The complete finite-matrix version of (103), with actual determinants
and traces and the stronger constant `2`. -/
theorem normalizedLogAbsDet_local_central_remainder [Nonempty N]
    (A H D : Matrix N N ℂ) (hn : D*A*D=1)
    (hC : (D*H*D).IsHermitian) (x : ℝ) (hx : x ≠ 0)
    (hsmall : |x| * ‖D*H*D‖ ≤ 1/2) :
    |(normalizedLogAbsDet (A+(x : ℂ) • H)+
        normalizedLogAbsDet (A-(x : ℂ) • H)-2*normalizedLogAbsDet A)/x^2 +
      (1/(Fintype.card N : ℝ))*(Matrix.trace ((D*H*D)*(D*H*D))).re|
      ≤ 2*x^2*‖D*H*D‖^4 := by
  have hp := normalizedLogAbsDet_affine_congruence A H D hn x
    (det_affine_ne_zero (D*H*D) hC x hsmall)
  have hmSmall : |(-x)| * ‖D*H*D‖ ≤ 1/2 := by simpa using hsmall
  have hm := normalizedLogAbsDet_affine_congruence A H D hn (-x)
    (det_affine_ne_zero (D*H*D) hC (-x) hmSmall)
  have hminus : A+((-x : ℝ) : ℂ) • H=A-(x : ℂ) • H := by simp [sub_eq_add_neg]
  have hminusC : (1 : Matrix N N ℂ)+((-x : ℝ) : ℂ) • (D*H*D)=1-(x : ℂ) • (D*H*D) := by
    simp [sub_eq_add_neg]
  rw [hminus,hminusC] at hm
  have hsum : normalizedLogAbsDet (A+(x : ℂ) • H)+
      normalizedLogAbsDet (A-(x : ℂ) • H)-2*normalizedLogAbsDet A =
      normalizedLogAbsDet (1+(x : ℂ) • (D*H*D))+
        normalizedLogAbsDet (1-(x : ℂ) • (D*H*D)) := by linarith
  rw [hsum]
  exact normalizedLogAbsDet_central_remainder (D*H*D) hC x hx hsmall

end RevisionBell
