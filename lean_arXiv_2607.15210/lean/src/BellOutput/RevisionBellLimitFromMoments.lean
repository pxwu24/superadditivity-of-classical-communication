import BellOutput.RevisionBellNormalizedChoi

/-! Assembly of the genuine Bell-output norm limit from the Hermitian
quadratic-moment limits established by the analytic part of Proposition A.3.
This module contains no independent isotropy or commutant assumption. -/

open Filter Finset PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace RevisionBell

lemma hermitian_trace_real {N : Type*} [Fintype N]
    (H : Matrix N N ℂ) (hH : H.IsHermitian) : ((Matrix.trace H).re : ℂ)=Matrix.trace H := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace H)=Matrix.trace H
  rw [← Matrix.trace_conjTranspose, hH.eq]

theorem real_square_moment_limit_to_complex
    {B : Type} [Fintype B] [DecidableEq B]
    (A : ℕ → Type) [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
    (C : ∀ n, Matrix (A n) (A n) ℂ) (hC : ∀ n, (C n).IsHermitian)
    (H : Matrix B B ℂ) (hH : H.IsHermitian) (c0 c1 : ℝ)
    (hlim : Tendsto (fun n => (1/(Fintype.card (A n) : ℝ))*(Matrix.trace (C n*C n)).re)
      atTop (nhds (-c0*(Matrix.trace H).re*(Matrix.trace H).re-c1*(Matrix.trace (H*H)).re))) :
    Tendsto (fun n => (1/(Fintype.card (A n) : ℂ))*Matrix.trace (C n*C n)) atTop
      (nhds (-(c0 : ℂ)*Matrix.trace H*Matrix.trace H-(c1 : ℂ)*Matrix.trace (H*H))) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hHH : (H*H).IsHermitian := by simpa only [pow_two] using hH.pow 2
  have hCC (n : ℕ) : (C n*C n).IsHermitian := by simpa only [pow_two] using (hC n).pow 2
  simpa only [Function.comp_def, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast, hermitian_trace_real H hH,
    hermitian_trace_real (H*H) hHH, hermitian_trace_real (C _*C _) (hCC _)] using h

/-- Theorem IV.1 assembled from the actual Hermitian square-moment limits.
All finite channel, tensor, Choi, polarization and operator-norm steps are
proved here or in the imported modules. -/
theorem normalized_channel_bell_limit_of_square_moments
    {B : Type} [Fintype B] [DecidableEq B] [Nonempty B]
    (A : ℕ → Type) [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)] [∀ n, Nonempty (A n)]
    (P : ∀ n, Matrix (A n × B) (A n × B) ℂ)
    (D : ∀ n, Matrix (A n) (A n) ℂ)
    (hP : ∀ n, (P n).PosSemidef) (hD : ∀ n, (D n).IsHermitian)
    (hn : ∀ n, D n*traceB (P n)*D n=1)
    (t : ℝ) (hd : BellLimitVerification.denominator (Fintype.card B) t ≠ 0)
    (hq : ∀ H : Matrix B B ℂ, H.IsHermitian →
      Tendsto (fun n => (1/(Fintype.card (A n) : ℝ))*(Matrix.trace
        ((D n*contraction (P n) H*D n)*(D n*contraction (P n) H*D n))).re) atTop
        (nhds (-BellLimitVerification.hessianC0 (Fintype.card B) t*(Matrix.trace H).re*(Matrix.trace H).re-
          BellLimitVerification.hessianC1 (Fintype.card B) t*(Matrix.trace (H*H)).re))) :
    Tendsto (fun n => ‖tensorMap (normalizedOutput (P n) (D n))
      (ProjectionChannels.conjugateMap (normalizedOutput (P n) (D n))) (bellState (A n))-
      isotropic B (BellLimitVerification.mixing (Fintype.card B) t)‖) atTop (nhds 0) := by
  have hk : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  have hJ : ∀ n x y, star (normalizedChoi (P n) (D n) x y)=normalizedChoi (P n) (D n) y x := by
    intro n x y
    exact (normalizedChoi_posSemidef (hP n) (D n) (hD n) (hn n)).isHermitian.apply y x
  have hqc : ∀ H : Matrix B B ℂ, H.IsHermitian →
      Tendsto (fun n => (1/(Fintype.card (A n) : ℂ))*Matrix.trace
        (choiAdjoint (normalizedChoi (P n) (D n)) H*choiAdjoint (normalizedChoi (P n) (D n)) H))
        atTop (nhds (-(BellLimitVerification.hessianC0 (Fintype.card B) t : ℂ)*Matrix.trace H*Matrix.trace H-
          (BellLimitVerification.hessianC1 (Fintype.card B) t : ℂ)*Matrix.trace (H*H))) := by
    intro H hH
    simp_rw [choiAdjoint_normalizedChoi]
    exact real_square_moment_limit_to_complex A (fun n => D n*contraction (P n) H*D n)
      (fun n => hermitian_sandwich (contraction_isHermitian (hP n).isHermitian hH) (hD n))
      H hH _ _ (hq H hH)
  simp_rw [normalizedOutput_bell_eq]
  apply bell_operator_norm_limit_of_mixed_moments A (fun n => normalizedChoi (P n) (D n)) t hJ hk hd
  intro i j p q
  simpa only [sub_eq_add_neg, neg_mul] using choi_mixed_moments_of_hermitian_square_limits A
    (fun n => normalizedChoi (P n) (D n))
    (BellLimitVerification.hessianC0 (Fintype.card B) t : ℂ)
    (BellLimitVerification.hessianC1 (Fintype.card B) t : ℂ) hqc i j p q

end RevisionBell
