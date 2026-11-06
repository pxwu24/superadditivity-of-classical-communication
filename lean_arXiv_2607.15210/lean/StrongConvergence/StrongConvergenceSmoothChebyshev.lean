import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.PSeries
import StrongConvergence.StrongConvergencePolyChebyshev
import Mathlib.Tactic

/-! Rapidly decaying Fourier/Chebyshev expansions for smooth real test functions. -/
open MeasureTheory Filter Set Real Complex
open scoped Topology ContDiff BigOperators
noncomputable section
namespace StrongConvergence

lemma periodic_iteratedDeriv {g : ℝ → ℂ} {T : ℝ} (hg : Function.Periodic g T) (p : ℕ) :
    Function.Periodic (iteratedDeriv p g) T := by
  intro x
  have heq : (fun z => g (z+T)) = g := funext hg
  have hi := congrFun (iteratedDeriv_comp_add_const p g T) x
  rw [heq] at hi
  exact hi.symm

private lemma two_pi_pos : 0 < 2 * Real.pi := by positivity

def circleFourierCoeff (g : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn two_pi_pos g n

lemma circleFourierCoeff_deriv {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi))
    {n : ℤ} (hn : n ≠ 0) :
    circleFourierCoeff g n = (Complex.I * (n : ℂ))⁻¹ * circleFourierCoeff (deriv g) n := by
  unfold circleFourierCoeff
  rw [fourierCoeffOn_of_hasDerivAt two_pi_pos hn
    (fun x _ => (hg.differentiable (by simp) x).hasDerivAt)
    ((hg.continuous_deriv (by simp)).intervalIntegrable _ _)]
  have hper : g (2 * Real.pi) = g 0 := by simpa using hp 0
  rw [hper]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  push_cast
  field_simp
  ring

lemma circleFourierCoeff_iteratedDeriv {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi))
    {n : ℤ} (hn : n ≠ 0) (p : ℕ) :
    circleFourierCoeff g n = (Complex.I * (n : ℂ))⁻¹ ^ p *
      circleFourierCoeff (iteratedDeriv p g) n := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [ih]
    have hd : ContDiff ℝ ∞ (iteratedDeriv p g) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv p hg
    rw [circleFourierCoeff_deriv hd (periodic_iteratedDeriv hp p) hn]
    simp only [iteratedDeriv_succ, pow_succ]
    ring

lemma circleFourierCoeff_norm_le {g : ℝ → ℂ} {B : ℝ}
    (hB : ∀ x ∈ Icc 0 (2*Real.pi), ‖g x‖ ≤ B) (n : ℤ) :
    ‖circleFourierCoeff g n‖ ≤ B := by
  rw [circleFourierCoeff, fourierCoeffOn_eq_integral]
  have ht := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => fourier (-n) (x : AddCircle (2*Real.pi-0)) • g x)
    (a := 0) (b := 2*Real.pi) (C := B) (by
      intro x hx
      rw [uIoc_of_le two_pi_pos.le] at hx
      simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using
        hB x ⟨hx.1.le, hx.2⟩)
  rw [norm_smul, Real.norm_eq_abs]
  have habs : |1 / (2*Real.pi-0)| = 1/(2*Real.pi) := by
    rw [sub_zero, abs_of_pos (by positivity)]
  rw [habs]
  apply (mul_le_mul_of_nonneg_left ht (by positivity)).trans
  rw [sub_zero, abs_of_pos two_pi_pos]
  exact le_of_eq (by field_simp)

lemma circleFourierCoeff_decay {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) (p : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℤ, n ≠ 0 →
      ‖circleFourierCoeff g n‖ ≤ B / |(n : ℝ)|^p := by
  have hc := (hg.continuous_iteratedDeriv p (by exact_mod_cast (le_top : (p:ℕ∞) ≤ ⊤))).norm
  obtain ⟨B, hB⟩ := (isCompact_Icc.image hc).bddAbove
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound : ∀ x ∈ Icc 0 (2*Real.pi), ‖iteratedDeriv p g x‖ ≤ C := by
    intro x hx
    exact (hB ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  refine ⟨C, hC, fun n hn => ?_⟩
  rw [circleFourierCoeff_iteratedDeriv hg hp hn p, norm_mul, norm_pow, norm_inv,
    norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
  have hb := circleFourierCoeff_norm_le hbound n
  calc
    _ ≤ (|(n:ℝ)|⁻¹)^p * C := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring


lemma circleFourierCoeff_weighted_summable {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) (p : ℕ) :
    Summable (fun n : ℤ => ‖circleFourierCoeff g n‖ * (|(n:ℝ)|+1)^p) := by
  obtain ⟨B, hB, hdecay⟩ := circleFourierCoeff_decay hg hp (p+2)
  have hs : Summable (fun n : ℤ => (B*2^p) * (1/(n:ℝ)^2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2:ℕ))).mul_left _
  apply Summable.of_norm_bounded_eventually _ hs
  filter_upwards [eventually_cofinite_ne (0:ℤ)] with n hn
  have ha1 : 1 ≤ |(n:ℝ)| := by exact_mod_cast (Int.one_le_abs hn)
  have ha : 0 < |(n:ℝ)| := by linarith
  have hw : (|(n:ℝ)|+1)^p ≤ (2*|(n:ℝ)|)^p := by gcongr; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (B / |(n:ℝ)|^(p+2)) * (2*|(n:ℝ)|)^p :=
      mul_le_mul (hdecay n hn) hw (by positivity) (by positivity)
    _ = (B*2^p) * (1/(n:ℝ)^2) := by
      rw [pow_add, mul_pow, sq_abs]
      field_simp
      ring


private lemma fourier_pair_cos (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2*Real.pi)) +
      fourier n ((-θ : ℝ) : AddCircle (2*Real.pi)) =
      (2*Real.cos ((n:ℝ)*θ) : ℝ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpos : 2*(Real.pi:ℂ)*I*n*θ/(2*Real.pi:ℝ) = ((n:ℝ)*θ:ℝ)*I := by
    push_cast
    field_simp
    ring
  have hneg : 2*(Real.pi:ℂ)*I*n*(-θ)/(2*Real.pi:ℝ) = -(((n:ℝ)*θ:ℝ):ℂ)*I := by
    push_cast
    field_simp
    ring
  rw [hpos]
  push_cast at hneg ⊢
  rw [hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

lemma hasSum_cosine_of_smooth_even {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi))
    (heven : ∀ θ, g (-θ) = g θ) (θ : ℝ) :
    HasSum (fun n : ℤ => (circleFourierCoeff g n).re * Real.cos ((n:ℝ)*θ))
      (g θ).re := by
  letI : Fact (0 < 2*Real.pi) := ⟨two_pi_pos⟩
  let G : C(AddCircle (2*Real.pi), ℂ) :=
    ⟨hp.lift, continuous_coinduced_dom.mpr hg.continuous⟩
  have hcoe (x : ℝ) : G (x : AddCircle (2*Real.pi)) = g x :=
    Function.Periodic.lift_coe hp x
  have hc (n : ℤ) : fourierCoeff G n = circleFourierCoeff g n := by
    rw [fourierCoeff_eq_intervalIntegral G n 0, circleFourierCoeff,
      fourierCoeffOn_eq_integral]
    simp only [zero_add, sub_zero, hcoe]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [fourier_coe_apply, fourier_coe_apply]
    simp
  have hsum : Summable (fourierCoeff G) := by
    apply Summable.of_norm
    simpa only [hc, pow_zero, mul_one] using circleFourierCoeff_weighted_summable hg hp 0
  have hθ := has_pointwise_sum_fourier_series_of_summable hsum (θ : AddCircle (2*Real.pi))
  have hnθ := has_pointwise_sum_fourier_series_of_summable hsum ((-θ : ℝ) : AddCircle (2*Real.pi))
  have havg := Complex.hasSum_re ((hθ.add hnθ).mul_right (1/2:ℂ))
  convert havg using 1
  · ext n
    simp only [hc, smul_eq_mul, ← mul_add, fourier_pair_cos]
    rw [mul_assoc]
    have hhalf : ((2*Real.cos ((n:ℝ)*θ) : ℝ):ℂ)*(1/2:ℂ) = (Real.cos ((n:ℝ)*θ):ℂ) := by
      push_cast
      ring
    rw [hhalf]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  · rw [hcoe, hcoe, heven]
    have he : (g θ + g θ) * (1/2:ℂ) = g θ := by ring
    rw [he]

/-- Smooth functions on a compact interval have Chebyshev expansions whose
coefficients remain summable after multiplication by every polynomial weight. -/
theorem exists_smooth_chebyshev_expansion {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {K : ℝ} (hK : 0 < K) :
    ∃ c : ℤ → ℝ,
      (∀ p : ℕ, Summable (fun n => |c n| * (|(n:ℝ)|+1)^p)) ∧
      ∀ x ∈ Icc (-K) K,
        HasSum (fun n : ℤ => c n * (Polynomial.Chebyshev.T ℝ n).eval (x/K)) (χ x) := by
  let g : ℝ → ℂ := fun θ => (χ (K*Real.cos θ) : ℂ)
  have hg : ContDiff ℝ ∞ g := by
    apply Complex.ofRealCLM.contDiff.comp
    exact hχ.comp (contDiff_const.mul Real.contDiff_cos)
  have hp : Function.Periodic g (2*Real.pi) := by
    intro θ
    simp [g, Real.cos_add_two_pi]
  have heven : ∀ θ, g (-θ) = g θ := by intro θ; simp [g]
  refine ⟨fun n => (circleFourierCoeff g n).re, ?_, ?_⟩
  · intro p
    apply Summable.of_nonneg_of_le (fun n => by positivity) _
      (circleFourierCoeff_weighted_summable hg hp p)
    intro n
    exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)
  · intro x hx
    have hx1 : -1 ≤ x/K := (le_div_iff₀ hK).mpr (by linarith [hx.1])
    have hx2 : x/K ≤ 1 := (div_le_iff₀ hK).mpr (by linarith [hx.2])
    have hcos := Real.cos_arccos hx1 hx2
    have h := hasSum_cosine_of_smooth_even hg hp heven (Real.arccos (x/K))
    convert h using 1
    · ext n
      congr 1
      simpa only [hcos] using Polynomial.Chebyshev.T_real_cos (Real.arccos (x/K)) n
    · simp only [g, hcos, Complex.ofReal_re]
      congr 1
      exact (mul_div_cancel₀ x hK.ne').symm

#print axioms exists_smooth_chebyshev_expansion
#print axioms circleFourierCoeff_weighted_summable
#print axioms circleFourierCoeff_decay
end StrongConvergence
