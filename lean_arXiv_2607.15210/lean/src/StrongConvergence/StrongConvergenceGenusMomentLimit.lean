import StrongConvergence.StrongConvergenceGenusMomentBound
import StrongConvergence.StrongConvergenceGenusCoefficients

/-! The leading genus coefficient is the limit of the actual expected Haar moments,
including density zero and density one. -/

open Polynomial Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

lemma continuous_genusRankTruncation_eval {k m : ℕ} (a : Fin k → ℝ) (R : ℕ) :
    Continuous (fun z : ℝ × ℝ => (genusRankTruncation k m a R z.1).eval z.2) := by
  simp only [genusRankTruncation, PolyChebyshev.xPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply continuous_finset_sum
  intro i _
  exact ((genusRankCoefficient k m a i.val).continuous.comp continuous_fst).mul
    (continuous_snd.pow _)

end ProjectionChannels.TensorHaar
namespace ProjectionChannels.Canonical
open TensorHaar

lemma ambientDimension_tendsto {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => (n + 1) * k) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
  intro n
  nlinarith

lemma inverseAmbientDimension_tendsto {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => ((((n + 1) * k : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (ambientDimension_tendsto hk))

/-- A7: all positive expected normalized moments converge to their actual genus-zero
coefficient. The endpoint densities are included. -/
theorem expectedNormalizedMoment_tendsto_genus
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (m : ℕ) (a : Fin k → ℝ) :
    Tendsto (fun n => expectedNormalizedMoment k t n m a) atTop
      (𝓝 (Complex.ofReal ((genusRankCoefficient k (m + 1) a 0).eval t))) := by
  let N : ℕ → ℕ := fun n => (n + 1) * k
  let s : ℕ → ℝ := fun n => (rankSequence k t n : ℝ) / (N n : ℝ)
  let P : ℕ → ℝ := fun n => (genusRankTruncation k (m + 1) a (2 * (m + 1)) (s n)).eval
    ((N n : ℝ)⁻¹)
  have hN : Tendsto N atTop atTop := ambientDimension_tendsto hk
  have hx : Tendsto (fun n => (N n : ℝ)⁻¹) atTop (𝓝 0) := inverseAmbientDimension_tendsto hk
  have hs : Tendsto s atTop (𝓝 t) := by
    simpa only [s, N, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm] using
      rank_density_tendsto hk ht0
  have hP : Tendsto P atTop (𝓝 ((genusRankCoefficient k (m + 1) a 0).eval t)) := by
    have h := (continuous_genusRankTruncation_eval (m := m + 1) a (2 * (m + 1))).continuousAt.tendsto.comp
      (hs.prodMk_nhds hx)
    simpa only [P, genusRankTruncation, PolyChebyshev.xPolynomial_eval_zero] using h
  have hPC : Tendsto (fun n => Complex.ofReal (P n)) atTop
      (𝓝 (Complex.ofReal ((genusRankCoefficient k (m + 1) a 0).eval t))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hP
  let C : ℝ := 4 * ((m + 1 : ℕ) : ℝ)^2 * (∑ i, |a i|)^(m+1) /
      ((8 : ℝ)^(m+1) * ((m + 1 : ℕ) : ℝ)^(m+1))
  have hbound : ∀ᶠ n in atTop,
      ‖expectedNormalizedMoment k t n m a - Complex.ofReal (P n)‖ ≤ C * ((N n : ℝ)⁻¹)^2 := by
    filter_upwards [eventually_ge_atTop m, hN.eventually (eventually_ge_atTop (8*(m+1)^4))]
      with n hn hlarge
    have h := expectedNormalizedMoment_degree_uniform_error hk ht0 ht1 n m (m+1) hn le_rfl a hlarge
    rw [← genusRankTruncation_eq_degreeTruncation (Nat.succ_pos m) a (2*(m+1))
      (s n) (2*(m+1)+(m+1)) (by omega)] at h
    simpa only [complexPolynomialEval_apply, P, C, N, s, div_eq_mul_inv, mul_inv_rev,
      inv_pow, mul_assoc, mul_comm, mul_left_comm] using h
  have hdiff : Tendsto (fun n => expectedNormalizedMoment k t n m a - Complex.ofReal (P n))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
      (by simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using (hx.pow 2).const_mul C)
  have hout := hdiff.add hPC
  simpa only [sub_add_cancel, zero_add] using hout

#print axioms expectedNormalizedMoment_tendsto_genus
end ProjectionChannels.Canonical
