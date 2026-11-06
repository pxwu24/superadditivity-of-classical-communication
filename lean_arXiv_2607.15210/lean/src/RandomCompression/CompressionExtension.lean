import RandomCompression.CompressionSpectral
import RandomCompression.BernoulliDuality
import Mathlib.Analysis.Normed.Lp.PiLp

open Filter Finset Set
open scoped Topology BigOperators ENNReal

namespace ProjectionChannels
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The support function in the paper, with its actual feasible region. -/
def bernoulliSupport (t k : ℝ) (a : ι → ℝ) : ℝ :=
  sSup (bernoulliObjectiveValues t k a)

lemma objective_cube_difference (a b u : ι → ℝ)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) :
    (∑ i, a i * u i) - (∑ i, b i * u i) ≤ ∑ i, |a i - b i| := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  calc
    a i * u i - b i * u i = (a i - b i) * u i := by ring
    _ ≤ |a i - b i| * u i := mul_le_mul_of_nonneg_right (le_abs_self _) (hu0 i)
    _ ≤ |a i - b i| := mul_le_of_le_one_right (abs_nonneg _) (hu1 i)

lemma bernoulliSupport_difference_le (t k : ℝ) (a b : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    bernoulliSupport t k a - bernoulliSupport t k b ≤ ∑ i, |a i - b i| := by
  obtain ⟨Ma, hMa, _⟩ := bernoulli_full_duality t k a ht0 ht1 hk
  obtain ⟨Mb, hMb, _⟩ := bernoulli_full_duality t k b ht0 ht1 hk
  unfold bernoulliSupport
  rw [hMa.csSup_eq, hMb.csSup_eq]
  obtain ⟨u, hu, hua⟩ := hMa.1
  have hub : (∑ i, b i * u i) ≤ Mb := hMb.2 ⟨u, hu, rfl⟩
  have hdiff := objective_cube_difference a b u hu.1 hu.2.1
  change (∑ i, a i * u i) = Ma at hua
  rw [hua] at hdiff
  linarith

/-- Exact ℓ¹ Lipschitz bound for the support function in the compression lemma. -/
theorem bernoulliSupport_lipschitz (t k : ℝ) (a b : ι → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hk : 0 < k) :
    |bernoulliSupport t k a - bernoulliSupport t k b| ≤ ∑ i, |a i - b i| := by
  have hab := bernoulliSupport_difference_le t k a b ht0 ht1 hk
  have hba := bernoulliSupport_difference_le t k b a ht0 ht1 hk
  have heq : (∑ i, |b i - a i|) = ∑ i, |a i - b i| := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_sub_comm _ _
  rw [heq] at hba
  exact abs_le.mpr ⟨by linarith, hab⟩

lemma l1_parameter_dist (a b : PiLp (1 : ℝ≥0∞) (fun _ : ι => ℝ)) :
    dist a b = ∑ i, |a i - b i| := by
  simp [dist_eq_norm, PiLp.norm_eq_sum]

/-- The all-real-parameter event for the actual projection block compressions.
The fixed-parameter almost-sure convergence hypothesis is explicit; the
random-matrix theorem establishing that hypothesis is not asserted here. -/
theorem ae_all_projection_compressions
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (k : ℕ) (hk : 0 < k) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ)
    (hH : ∀ ω m, (P ω m).IsHermitian)
    (hId : ∀ ω m, P ω m * P ω m = P ω m)
    (hconv : ∀ a : Fin k → ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun m => largestEigenvalue
        (blockCompression_isHermitian (diagonalBlock (P ω m))
          (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1.1) a))
        atTop (𝓝 (bernoulliSupport t (k : ℝ) a))) :
    ∀ᵐ ω ∂μ, ∀ a : Fin k → ℝ,
      Tendsto (fun m => largestEigenvalue
        (blockCompression_isHermitian (diagonalBlock (P ω m))
          (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1.1) a))
        atTop (𝓝 (bernoulliSupport t (k : ℝ) a)) := by
  let X := PiLp (1 : ℝ≥0∞) (fun _ : Fin k => ℝ)
  let f : Ω → ℕ → X → ℝ := fun ω m a => largestEigenvalue
    (blockCompression_isHermitian (diagonalBlock (P ω m))
      (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1.1) a)
  let g : X → ℝ := fun a => bernoulliSupport t (k : ℝ) a
  obtain ⟨s, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense X
  have hf : ∀ ω m a b, dist (f ω m a) (f ω m b) ≤ dist a b := by
    intro ω m a b
    rw [Real.dist_eq, l1_parameter_dist]
    exact blockCompression_largest_lipschitz (diagonalBlock (P ω m))
      (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1)
      (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).2) a b
  have hg : ∀ a b, dist (g a) (g b) ≤ dist a b := by
    intro a b
    rw [Real.dist_eq, l1_parameter_dist]
    exact bernoulliSupport_lipschitz t k a b ht0 ht1 (Nat.cast_pos.mpr hk)
  have hq : ∀ q ∈ s, ∀ᵐ ω ∂μ, Tendsto (fun m => f ω m q) atTop (𝓝 (g q)) := by
    intro q _
    exact hconv q
  have hall := ae_simultaneous_convergence_of_dense_lipschitz μ s f g hcount hdense hf hg hq
  filter_upwards [hall] with ω hω
  intro a
  exact hω ((WithLp.equiv 1 (Fin k → ℝ)).symm a)

end
end ProjectionChannels

