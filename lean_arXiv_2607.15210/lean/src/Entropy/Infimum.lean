import Entropy.Single

open Real Finset
noncomputable section
namespace AppendixB

/-- Entropies of the shuffled spectra obtained from the normalized eigenvalue body. -/
def outputEntropyValues (p t : ℝ) (k r : ℕ) : Set ℝ :=
  {s | ∃ q ∈ Lam k t,
    s = renyi p (subsets k r) (fun _ => 1) (shuffle k r q)}

/-- The optimal entropy at the level of the explicitly defined spectra.
The estimates below establish that the defining set is nonempty and bounded below
for all sufficiently large output dimensions. -/
def infimumOutputEntropy (p t : ℝ) (k r : ℕ) : ℝ :=
  sInf (outputEntropyValues p t k r)

/-- A uniform lower bound and one matching upper witness bound the actual infimum. -/
lemma entropy_sInf_abs_le {S : Set ℝ} {m e : ℝ}
    (hlower : ∀ s ∈ S, m - e ≤ s)
    (hupper : ∃ s ∈ S, s ≤ m + e) :
    |sInf S - m| ≤ e := by
  obtain ⟨s, hs, hsu⟩ := hupper
  have hne : S.Nonempty := ⟨s, hs⟩
  have hbb : BddBelow S := ⟨m - e, hlower⟩
  have hlo : m - e ≤ sInf S := le_csInf hne hlower
  have hhi : sInf S ≤ m + e := (csInf_le hbb hs).trans hsu
  exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩

/-- For `r = 1`, the entropy values are exactly those of the original spectra. -/
lemma outputEntropyValues_one (p t : ℝ) (k : ℕ) :
    outputEntropyValues p t k 1 =
      {s | ∃ q ∈ Lam k t, s = renyi p Finset.univ (fun _ => 1) q} := by
  simp only [outputEntropyValues, renyi_r1]

/-- The feasible entropy set is eventually nonempty and bounded below. -/
theorem outputEntropyValues_eventually_nonempty_bddBelow
    {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      (outputEntropyValues p t k r).Nonempty ∧
        BddBelow (outputEntropyValues p t k r) := by
  obtain ⟨C, k₀, h⟩ := single_output ht0 ht1 hp r hr
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨hlower, q, hq, _⟩ := h k hk
  refine ⟨⟨_, q, hq, rfl⟩, ?_⟩
  refine ⟨Real.log (Nat.choose k r) - 2 * p * (1 - t) / (t * r * k ^ 2)
      - C / (k ^ 2 * Real.sqrt k), ?_⟩
  rintro s ⟨q', hq', rfl⟩
  exact hlower q' hq'

/-- Antisymmetric single-output entropy asymptotics for the actual infimum.
This is a scalar-spectrum theorem; identifying these spectra with channel output
operators is the separate operator argument in the accompanying LaTeX proof. -/
theorem single_output_infimum
    {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      |infimumOutputEntropy p t k r -
        (Real.log (Nat.choose k r) - 2 * p * (1 - t) / (t * r * k ^ 2))|
        ≤ C / (k ^ 2 * Real.sqrt k) := by
  obtain ⟨C, k₀, h⟩ := single_output ht0 ht1 hp r hr
  refine ⟨|C|, abs_nonneg C, k₀, fun k hk => ?_⟩
  obtain ⟨hlower, q, hq, hupper⟩ := h k hk
  have hbound : |infimumOutputEntropy p t k r -
      (Real.log (Nat.choose k r) - 2 * p * (1 - t) / (t * r * k ^ 2))|
      ≤ C / (k ^ 2 * Real.sqrt k) := by
    apply entropy_sInf_abs_le
    · rintro s ⟨q', hq', rfl⟩
      exact hlower q' hq'
    · exact ⟨_, ⟨q, hq, rfl⟩, hupper⟩
  exact hbound.trans (div_le_div_of_nonneg_right (le_abs_self C) (by positivity))

/-- Unprocessed single-output entropy asymptotics, with the stronger
`O(k^(-5/2))` remainder, for the actual infimum. -/
theorem single_output_r1_infimum
    {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      |sInf {s : ℝ | ∃ q ∈ Lam k t,
          s = renyi p Finset.univ (fun _ => 1) q} -
        (Real.log k - 2 * p * (1 - t) / (t * k ^ 2))|
        ≤ C / (k ^ 2 * Real.sqrt k) := by
  simpa only [infimumOutputEntropy, outputEntropyValues_one,
    Nat.choose_one_right, Nat.cast_one, mul_one]
    using single_output_infimum ht0 ht1 hp 1 le_rfl

end AppendixB
end
