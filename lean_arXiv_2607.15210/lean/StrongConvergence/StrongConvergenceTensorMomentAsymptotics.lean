import StrongConvergence.StrongConvergenceTensorInverseAsymptotics
import StrongConvergence.StrongConvergenceTensorCanonical

/-!
# Finite Neumann approximations to Haar projection moments

The inverse Gram coefficients can be replaced by a finite polynomial in the
normalized Gram matrix, with an error small enough to survive the dimension
factors in the exact compression-moment formula. This does not identify the
limiting free law or establish almost-sure convergence.
-/

open Matrix MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.TensorHaar

lemma cycleCount_le {m : ℕ} (σ : Equiv.Perm (Fin m)) : cycleCount σ ≤ m := by
  have h := Fintype.card_le_of_surjective
    (Quotient.mk _ : Fin m → CycleClasses σ) Quotient.mk_surjective
  simpa only [cycleCount, Fintype.card_fin] using h

def normalizedProjectionContractions (N m d : ℕ) : Equiv.Perm (Fin m) → ℂ :=
  fun σ => (d : ℂ) ^ cycleCount σ.symm / (N : ℂ) ^ m

lemma normalizedProjectionContractions_norm_le {N m d : ℕ}
    (hN : 0 < N) (hd : d ≤ N) (σ : Equiv.Perm (Fin m)) :
    ‖normalizedProjectionContractions N m d σ‖ ≤ 1 := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hdR : (d : ℝ) ≤ N := by exact_mod_cast hd
  simp only [normalizedProjectionContractions, norm_div, norm_pow, Complex.norm_natCast]
  apply (div_le_one (pow_pos hNR m)).mpr
  exact (pow_le_pow_left₀ (by positivity) hdR _).trans
    (pow_le_pow_right₀ hN1 (cycleCount_le σ.symm))

/-- Inverse-free approximation to the finite Haar projection coefficients. -/
def neumannProjectionMomentCoefficients (E : Type*) [Fintype E] [DecidableEq E]
    (m d q : ℕ) : Equiv.Perm (Fin m) → ℂ :=
  (∑ l ∈ Finset.range q,
    (1 - ((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m) ^ l) *ᵥ
      normalizedProjectionContractions (Fintype.card E) m d

lemma projectionMomentCoefficients_sub_neumann
    (E : Type*) [Fintype E] [DecidableEq E]
    (m d q : ℕ) (hE : 0 < Fintype.card E) (σ : Equiv.Perm (Fin m)) :
    projectionMomentCoefficients E m d σ -
      neumannProjectionMomentCoefficients E m d q σ =
    (inverseGramNeumannRemainder E m q *ᵥ
      normalizedProjectionContractions (Fintype.card E) m d) σ := by
  have hNc : (Fintype.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hE.ne'
  simp only [projectionMomentCoefficients, neumannProjectionMomentCoefficients,
    inverseGramNeumannRemainder, normalizedProjectionContractions, Matrix.mulVec,
    dotProduct, ← Finset.sum_sub_distrib, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro τ _
  field_simp <;> ring

lemma projectionMomentCoefficients_sub_neumann_norm_le
    (E : Type*) [Fintype E] [DecidableEq E]
    (m d q : ℕ) (hE : 0 < Fintype.card E) (hd : d ≤ Fintype.card E)
    (σ : Equiv.Perm (Fin m)) :
    ‖projectionMomentCoefficients E m d σ -
      neumannProjectionMomentCoefficients E m d q σ‖ ≤
      ∑ τ, ‖inverseGramNeumannRemainder E m q σ τ‖ := by
  rw [projectionMomentCoefficients_sub_neumann E m d q hE σ]
  calc
    _ ≤ ∑ τ, ‖inverseGramNeumannRemainder E m q σ τ *
        normalizedProjectionContractions (Fintype.card E) m d τ‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro τ _
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (normalizedProjectionContractions_norm_le hE hd τ)

/-- The Haar coefficient approximation remains valid after any prescribed
polynomial dimension amplification, using enough Neumann terms. The rank
sequence may be arbitrary within the ambient dimensions. -/
theorem projectionMomentCoefficients_neumann_scaled_tendsto
    {m : ℕ} (hm : 0 < m) (N d : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hd : ∀ n, d n ≤ N n) (r : ℕ) (σ : Equiv.Perm (Fin m)) :
    Tendsto (fun n => (N n : ℝ) ^ r *
      ‖projectionMomentCoefficients (Fin (N n)) m (d n) σ -
        neumannProjectionMomentCoefficients (Fin (N n)) m (d n) (r+1) σ‖)
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop,
      (N n : ℝ) ^ r *
        ‖projectionMomentCoefficients (Fin (N n)) m (d n) σ -
          neumannProjectionMomentCoefficients (Fin (N n)) m (d n) (r+1) σ‖ ≤
      (N n : ℝ) ^ r *
        (∑ τ, ‖inverseGramNeumannRemainder (Fin (N n)) m (r+1) σ τ‖) := by
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact projectionMomentCoefficients_sub_neumann_norm_le _ _ _ _
      (by simpa using hn) (by simpa using hd n) σ
  exact squeeze_zero' (Eventually.of_forall (fun n => by positivity)) hbound
    (inverseGramNeumannRemainder_scaled_tendsto N hN hm r σ)

lemma permutationGram_eq_fin (E : Type*) [Fintype E] [DecidableEq E] (m : ℕ) :
    permutationGram E m = permutationGram (Fin (Fintype.card E)) m := by
  ext σ τ
  simp only [permutationGram_cycles, Fintype.card_fin]

lemma projectionMomentCoefficients_eq_fin
    (E : Type*) [Fintype E] [DecidableEq E] (m d : ℕ) :
    projectionMomentCoefficients E m d =
      projectionMomentCoefficients (Fin (Fintype.card E)) m d := by
  unfold projectionMomentCoefficients
  rw [permutationGram_eq_fin E m]

lemma neumannProjectionMomentCoefficients_eq_fin
    (E : Type*) [Fintype E] [DecidableEq E] (m d q : ℕ) :
    neumannProjectionMomentCoefficients E m d q =
      neumannProjectionMomentCoefficients (Fin (Fintype.card E)) m d q := by
  unfold neumannProjectionMomentCoefficients
  rw [permutationGram_eq_fin E m]
  simp only [Fintype.card_fin]

end ProjectionChannels.TensorHaar

namespace ProjectionChannels.Canonical
open TensorHaar

/-- An explicit finite Neumann approximation to the expected compression trace
moment; all sums are finite, and the expression contains no matrix inverse. -/
def neumannCompressionTraceMoment (k : ℕ) (t : ℝ) (m q : ℕ) (a : Fin k → ℝ)
    (n : ℕ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin (m+1)),
    neumannProjectionMomentCoefficients (Index k n) (m+1) (rankSequence k t n) q σ *
      ((n+1 : ℕ) : ℂ) ^ cycleCount (finRotate (m+1) * σ) *
      weightedCycleMoment a σ

/-- All fixed-order expected Haar compression moments admit an inverse-free
finite Neumann approximation with vanishing absolute error. This is stronger
than an error estimate only after normalized trace division, but it does not
evaluate the limit of that finite expression. -/
theorem integral_compression_trace_neumann_approximation
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (m : ℕ) (a : Fin k → ℝ) :
    Tendsto (fun n =>
      (∫ ω, Matrix.trace
        ((blockCompression (diagonalBlock (projection k t ω n)) a) ^ (m+1))
          ∂probability k) - neumannCompressionTraceMoment k t m (m+2) a n)
      atTop (𝓝 0) := by
  let N : ℕ → ℕ := fun n => (n+1)*k
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
    intro n
    dsimp [N]
    nlinarith
  have hd (n : ℕ) : rankSequence k t n ≤ N n := by
    simpa only [Index, Fintype.card_prod, Fintype.card_fin, N] using
      rankSequence_le ht0 ht1 n
  let diff (n : ℕ) (σ : Equiv.Perm (Fin (m+1))) :=
    projectionMomentCoefficients (Index k n) (m+1) (rankSequence k t n) σ -
      neumannProjectionMomentCoefficients (Index k n) (m+1)
        (rankSequence k t n) (m+2) σ
  have hc (σ : Equiv.Perm (Fin (m+1))) :
      Tendsto (fun n => (N n : ℝ) ^ (m+1) * ‖diff n σ‖) atTop (𝓝 0) := by
    have h := projectionMomentCoefficients_neumann_scaled_tendsto
      (Nat.succ_pos m) N (rankSequence k t) hN hd (m+1) σ
    have heq (n : ℕ) : diff n σ =
        projectionMomentCoefficients (Fin (N n)) (m+1) (rankSequence k t n) σ -
          neumannProjectionMomentCoefficients (Fin (N n)) (m+1)
            (rankSequence k t n) (m+2) σ := by
      dsimp [diff]
      rw [projectionMomentCoefficients_eq_fin (Index k n),
        neumannProjectionMomentCoefficients_eq_fin (Index k n)]
      have hcard : Fintype.card (Index k n) = N n := by
        simp only [Index, Fintype.card_prod, Fintype.card_fin, N]
      rw [hcard]
    simpa only [heq, Nat.add_assoc] using h
  have hterm (σ : Equiv.Perm (Fin (m+1))) :
      Tendsto (fun n => diff n σ *
        ((n+1 : ℕ) : ℂ) ^ cycleCount (finRotate (m+1) * σ) * weightedCycleMoment a σ)
        atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hpow (n : ℕ) : ((n+1 : ℕ) : ℝ) ^ cycleCount (finRotate (m+1) * σ) ≤
        (N n : ℝ) ^ (m+1) := by
      have hnN : n+1 ≤ N n := by dsimp [N]; nlinarith
      have hN1 : (1 : ℝ) ≤ N n := by exact_mod_cast (show 1 ≤ N n by omega)
      exact (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hnN) _).trans
        (pow_le_pow_right₀ hN1 (cycleCount_le _))
    apply squeeze_zero (fun n => norm_nonneg _) _
      (by simpa only [zero_mul] using (hc σ).mul_const ‖weightedCycleMoment a σ‖)
    intro n
    simp only [norm_mul, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ ‖diff n σ‖ * (N n : ℝ) ^ (m+1) * ‖weightedCycleMoment a σ‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hpow n) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hs := tendsto_finset_sum Finset.univ (fun σ _ => hterm σ)
  simp only [Finset.sum_const_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_integral_compression_trace_cycles hk ht0 ht1 m a] with n hn
  rw [hn, neumannCompressionTraceMoment, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  dsimp [diff]
  ring

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.TensorHaar.projectionMomentCoefficients_neumann_scaled_tendsto
#print axioms ProjectionChannels.Canonical.integral_compression_trace_neumann_approximation
