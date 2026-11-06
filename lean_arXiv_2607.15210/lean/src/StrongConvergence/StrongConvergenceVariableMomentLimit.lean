import StrongConvergence.StrongConvergenceGenusMomentLimit

/-! Expected moments for the actual canonical ensemble with a converging
sequence of densities. The approximation error is uniform in density. -/
open Polynomial Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar

lemma rank_density_variable_tendsto {k : ℕ} {t : ℝ} {u : ℕ → ℝ}
    (hk : 0 < k) (hu0 : ∀ n, 0 ≤ u n) (hut : Tendsto u atTop (𝓝 t)) :
    Tendsto (fun n => (rankSequence k (u n) n : ℝ) / (((n+1)*k:ℕ):ℝ))
      atTop (𝓝 t) := by
  let N : ℕ → ℝ := fun n => (((n+1)*k:ℕ):ℝ)
  have hN (n : ℕ) : 0 < N n := by
    dsimp [N]
    exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hk
  have hx : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 0) := inverseAmbientDimension_tendsto hk
  have hb (n : ℕ) : |(rankSequence k (u n) n : ℝ) / N n - u n| ≤ (N n)⁻¹ := by
    have hprod : u n * ((k:ℝ)*(n+1)) = u n * N n := by
      simp only [N, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    have hf : rankSequence k (u n) n = ⌊u n * N n⌋₊ := by
      rw [rankSequence, hprod]
    rw [hf]
    have hlo := Nat.floor_le (mul_nonneg (hu0 n) (hN n).le)
    have hup := Nat.lt_floor_add_one (u n * N n)
    have hab : |(⌊u n * N n⌋₊:ℝ) - u n * N n| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith
    have he : (⌊u n * N n⌋₊:ℝ) / N n - u n =
        ((⌊u n * N n⌋₊:ℝ) - u n * N n) / N n := by field_simp; ring
    rw [he, abs_div, abs_of_pos (hN n), ← one_div]
    exact div_le_div_of_nonneg_right hab (hN n).le
  have hd : Tendsto (fun n => (rankSequence k (u n) n : ℝ) / N n - u n)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by simpa only [Real.norm_eq_abs] using hb n) hx
  simpa only [sub_add_cancel, zero_add, N] using hd.add hut

/-- Uniform Gaussian/Haar moment expansion and coefficient continuity imply
the same genus-zero limit when the density varies and converges. -/
theorem expectedNormalizedMoment_variable_tendsto_genus
    {k : ℕ} {t : ℝ} {u : ℕ → ℝ} (hk : 0 < k)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1)
    (hut : Tendsto u atTop (𝓝 t)) (m : ℕ) (a : Fin k → ℝ) :
    Tendsto (fun n => expectedNormalizedMoment k (u n) n m a) atTop
      (𝓝 (Complex.ofReal ((genusRankCoefficient k (m+1) a 0).eval t))) := by
  let N : ℕ → ℕ := fun n => (n + 1) * k
  let s : ℕ → ℝ := fun n => (rankSequence k (u n) n : ℝ) / (N n : ℝ)
  let P : ℕ → ℝ := fun n => (genusRankTruncation k (m + 1) a (2 * (m + 1)) (s n)).eval
    ((N n : ℝ)⁻¹)
  have hN : Tendsto N atTop atTop := ambientDimension_tendsto hk
  have hx : Tendsto (fun n => (N n : ℝ)⁻¹) atTop (𝓝 0) := inverseAmbientDimension_tendsto hk
  have hs : Tendsto s atTop (𝓝 t) := by
    simpa only [s, N, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm] using
      rank_density_variable_tendsto hk hu0 hut
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
      ‖expectedNormalizedMoment k (u n) n m a - Complex.ofReal (P n)‖ ≤ C * ((N n : ℝ)⁻¹)^2 := by
    filter_upwards [eventually_ge_atTop m, hN.eventually (eventually_ge_atTop (8*(m+1)^4))]
      with n hn hlarge
    have h := expectedNormalizedMoment_degree_uniform_error hk (hu0 n) (hu1 n) n m (m+1) hn le_rfl a hlarge
    rw [← genusRankTruncation_eq_degreeTruncation (Nat.succ_pos m) a (2*(m+1))
      (s n) (2*(m+1)+(m+1)) (by omega)] at h
    simpa only [complexPolynomialEval_apply, P, C, N, s, div_eq_mul_inv, mul_inv_rev,
      inv_pow, mul_assoc, mul_comm, mul_left_comm] using h
  have hdiff : Tendsto (fun n => expectedNormalizedMoment k (u n) n m a - Complex.ofReal (P n))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
      (by simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using (hx.pow 2).const_mul C)
  have hout := hdiff.add hPC
  simpa only [sub_add_cancel, zero_add] using hout


#print axioms expectedNormalizedMoment_variable_tendsto_genus
end ProjectionChannels.Canonical
