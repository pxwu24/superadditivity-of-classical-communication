import StrongConvergence.StrongConvergenceVariableLimitLaw
import StrongConvergence.StrongConvergenceVariableRotationTransfer
import StrongConvergence.StrongConvergenceVariableSmoothEdge
import StrongConvergence.StrongConvergenceReflectedLaw
import StrongConvergence.StrongConvergenceGenusLawIdentification
import StrongConvergence.StrongConvergenceEdgeSupport

/-! Block-modified strong convergence for every convergent sequence of rank
densities. No rate of convergence of the densities is imposed. -/
open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels.Canonical
open TensorHaar

private lemma largestEigenvalue_congr_matrix {d : ℕ} [NeZero d]
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A=B) : largestEigenvalue hA=largestEigenvalue hB := by
  subst B
  rfl

theorem ae_variable_norm_shift_tendsto_of_genus_moments {k : ℕ} {t : ℝ} {u : ℕ → ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hu0 : ∀ n, 0≤u n) (hu1 : ∀ n, u n≤1) (hut : Tendsto u atTop (𝓝 t))
    (a : Fin k → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x∈Icc (-(∑ i, |a i|)) (∑ i, |a i|))
    (hmom : ∀ j : ℕ, ∫ x, x^j ∂ν=(normalizedMomentCoefficient k j a 0).eval t) :
    ∀ᵐ ω ∂probability k, ∀ c : ℝ,
      Tendsto (fun n => ‖(c:ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) +
        blockCompression (diagonalBlock (projection k (u n) ω n)) a‖)
        atTop (𝓝 (sSup ((fun x : ℝ => |c+x|) '' realMeasureSupport ν))) := by
  have hK : 0≤∑ i, |a i| := Finset.sum_nonneg (fun i _ => abs_nonneg (a i))
  have hlaw := isBernoulliFreeSumLaw_of_genus_moments ν hk ht0.le ht1.le hK
    (hν.mono fun x hx => abs_le.mpr hx) hmom
  have hedge : sSup (realMeasureSupport ν)=bernoulliSupport t (k:ℝ) a :=
    bernoulli_free_sum_right_edge hk ht0 ht1 a ν hlaw
  have hupper := ae_variable_largestCompression_upper_of_vanishing_probability hk ht0 ht1
    u hut a (bernoulliSupport t (k:ℝ) a) (fun ε hε =>
      variable_upper_edge_measure_tendsto_zero hk ht0 ht1 a u hu0 hu1 hut hε)
  let νneg := ν.map (fun x : ℝ => -x)
  letI : IsProbabilityMeasure νneg := isProbabilityMeasure_map measurable_neg.aemeasurable
  have hnegmom := reflectedLaw_canonical_moments hk ht0.le ht1 a ν hmom
  have hnegν := reflectedLaw_ae_mem ν hν
  have hneglaw := isBernoulliFreeSumLaw_of_genus_moments νneg hk ht0.le ht1.le hK
    (hnegν.mono fun x hx => abs_le.mpr hx) hnegmom
  have hnegedge : sSup (realMeasureSupport νneg)=bernoulliSupport t (k:ℝ) (-a) :=
    bernoulli_free_sum_right_edge hk ht0 ht1 (-a) νneg hneglaw
  have hlower := ae_variable_largestCompression_upper_of_vanishing_probability hk ht0 ht1
    u hut (-a) (bernoulliSupport t (k:ℝ) (-a)) (fun ε hε =>
      variable_upper_edge_measure_tendsto_zero hk ht0 ht1 (-a) u hu0 hu1 hut hε)
  have hweak := ae_variable_spectral_tests_tendsto hk ht0 ht1 hu0 hu1 hut a ν hν hmom
  filter_upwards [hweak,hupper,hlower] with ω hω hu hl
  intro c
  apply StrongConvergence.tendsto_norm_shift_of_weak_and_edges
    (fun n => n+1) (fun n => Nat.succ_pos n)
    (fun n => blockCompression (diagonalBlock (projection k (u n) ω n)) a)
    (fun n => compressionHermitian k (u n) a ω n) ν
    ⟨∑ i, |a i|,hν.mono fun x hx => abs_le.mpr hx⟩
  · intro f hf hb
    exact hω f hf.continuousOn
  · intro ε hε
    rw [hedge]
    exact (hu ε hε).mono fun n hn => hn.le
  · intro ε hε
    change ∀ᶠ n in atTop, _ ≤ sSup (realMeasureSupport νneg)+ε
    rw [hnegedge]
    filter_upwards [hl ε hε] with n hn
    have heq : largestEigenvalue (compressionHermitian k (u n) (-a) ω n) =
        largestEigenvalue (compressionHermitian k (u n) a ω n).neg :=
      largestEigenvalue_congr_matrix _ _ (StrongConvergence.blockCompression_neg _ a)
    rw [← heq]
    exact hn.le

/-- The full affine-norm and weak-spectral theorem for arbitrary convergent
densities, including every integer-rank sequence after division by dimension. -/
theorem variableStrongInput {k : ℕ} {t : ℝ} {u : ℕ → ℝ}
    (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hu0 : ∀ n, 0≤u n) (hu1 : ∀ n, u n≤1) (hut : Tendsto u atTop (𝓝 t)) :
    FullBlockModifiedStrongInput (probability k) k t
      (fun ω n => projection k (u n) ω n)
      (fun ω n => projection_isHermitian k (u n) ω n) := by
  apply fullBlockModifiedStrongInput_of_variable_compression hk t u
  intro a
  obtain ⟨ν,hprob,hν,hmom,hweak⟩ := exists_canonical_spectral_limit hk ht0.le ht1 a
  letI := hprob
  have hlaw := isBernoulliFreeSumLaw_of_genus_moments ν hk ht0.le ht1.le
    (Finset.sum_nonneg (fun i _ => abs_nonneg (a i)))
    (hν.mono fun x hx => abs_le.mpr hx) hmom
  refine ⟨ν,hlaw,?_,?_⟩
  · intro c
    exact (ae_variable_norm_shift_tendsto_of_genus_moments hk ht0 ht1 hu0 hu1 hut a ν hν hmom).mono
      fun ω hω => hω c
  · intro f hf hb
    exact (ae_variable_spectral_tests_tendsto hk ht0 ht1 hu0 hu1 hut a ν hν hmom).mono
      fun ω hω => hω f hf.continuousOn

/-- Every admissible integer rank sequence is realized exactly, with no floor
error, by its rational density. -/
theorem arbitraryRankStrongInput {k : ℕ} {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (d : ℕ → ℕ) (hd : ∀ n, d n≤(n+1)*k)
    (hdt : Tendsto (fun n => (d n:ℝ)/(((n+1)*k:ℕ):ℝ)) atTop (𝓝 t)) :
    FullBlockModifiedStrongInput (probability k) k t
      (fun ω n => projection k ((d n:ℝ)/(((n+1)*k:ℕ):ℝ)) ω n)
      (fun ω n => projection_isHermitian k ((d n:ℝ)/(((n+1)*k:ℕ):ℝ)) ω n) := by
  apply variableStrongInput hk ht0 ht1 (fun n => by positivity) (fun n => ?_) hdt
  exact (div_le_one (by exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hk)).mpr
    (by exact_mod_cast hd n)

#print axioms variableStrongInput
#print axioms arbitraryRankStrongInput
end ProjectionChannels.Canonical
