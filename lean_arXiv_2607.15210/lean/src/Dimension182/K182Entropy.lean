import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic
import Dimension182.K182Dual
import Dimension182.K182Numerics

/-!
# Entropy consequences for the output-dimension certificate

This file proves the entropy of a one-exceptional-eigenvalue spectrum,
its monotonicity, and the passage from a strict limiting gap to an
eventual finite-dimensional gap.

The theorem `entropy_lower_bound_of_one_high_minimizer` is a generic
conditional helper. Its shape hypothesis is proved for the actual Bernoulli
body in `RevisionLemmaC1.lean` and discharged at the certified parameters in
`RevisionK182Minimizer.lean`. `RevisionPropositionVI.lean` gives the resulting
actual matrix and finite-channel conclusions. A coordinate cap alone would
not establish the Shannon entropy lower bound.
-/

open scoped BigOperators
open Set Filter Topology

namespace ProjectionChannels

/-- Shannon entropy, with the usual `0 log 0 = 0` convention. -/
noncomputable def finiteShannon {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  -∑ i, v i * Real.log (v i)

/-- Entropy of `(x,(1-x)/(k-1),...,(1-x)/(k-1))`. -/
noncomputable def oneHighEntropy (k : ℕ) (x : ℝ) : ℝ :=
  -x * Real.log x - (1-x) * Real.log ((1-x)/((k : ℝ)-1))

theorem oneHighEntropy_eq_qaryEntropy (k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    oneHighEntropy k x = Real.qaryEntropy k (1-x) := by
  have hk1 : (k : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (k : ℤ) - 1 ≠ 0 by omega)
  by_cases hx : x = 1
  · simp [hx, oneHighEntropy, Real.qaryEntropy]
  · have hx1 : 1-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    rw [oneHighEntropy, Real.log_div hx1 hk1]
    simp only [Real.qaryEntropy, Real.binEntropy, Real.log_inv,
      Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_sub_cancel]
    ring

/-- On the relevant half of the simplex, increasing the exceptional
eigenvalue decreases Shannon entropy. This includes both endpoints. -/
theorem oneHighEntropy_antitoneOn (k : ℕ) (hk : 2 ≤ k) :
    AntitoneOn (oneHighEntropy k) (Icc (1/(k : ℝ)) 1) := by
  intro x hx y hy hxy
  rw [oneHighEntropy_eq_qaryEntropy k hk,
    oneHighEntropy_eq_qaryEntropy k hk]
  apply (Real.qaryEntropy_strictMonoOn hk).monotoneOn
  · constructor <;> linarith [hy.1, hy.2]
  · constructor <;> linarith [hx.1, hx.2]
  · linarith

theorem finiteShannon_oneHigh {k : ℕ} (hk : 2 ≤ k) (i : Fin k)
    (x : ℝ) :
    finiteShannon (fun j : Fin k => if j = i then x else (1-x)/((k:ℝ)-1))
      = oneHighEntropy k x := by
  classical
  have hk1 : (k : ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  let a : ℝ := (1-x)/((k:ℝ)-1)
  have heq (j : Fin k) :
      (if j = i then x else a) * Real.log (if j = i then x else a) =
      a * Real.log a + (if j = i then x * Real.log x - a * Real.log a else 0) := by
    split_ifs <;> ring
  change -(∑ j, (if j = i then x else a) * Real.log (if j = i then x else a)) = _
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold oneHighEntropy
  dsimp [a]
  field_simp [hk1]
  ring

/-- The minimizer-shape property, proved for the paper body in
`RevisionLemmaC1.lean`: one exceptional coordinate and equal others. -/
def HasOneHighEntropyMinimizer {k : ℕ} (C : Set (Fin k → ℝ)) : Prop :=
  ∃ v ∈ C, ∃ i : Fin k, ∃ x : ℝ,
    1/(k:ℝ) ≤ x ∧ x ≤ 1 ∧
    (∀ j, v j = if j = i then x else (1-x)/((k:ℝ)-1)) ∧
    ∀ w ∈ C, finiteShannon v ≤ finiteShannon w

/-- Generic entropy consequence of a one-high minimizer. The paper-specific
shape proof is supplied by `RevisionLemmaC1.lean`. -/
theorem entropy_lower_bound_of_one_high_minimizer {k : ℕ} (hk : 2 ≤ k)
    (C : Set (Fin k → ℝ)) (hshape : HasOneHighEntropyMinimizer C)
    (L : ℝ) (hL : L ≤ 1) (hcap : ∀ v ∈ C, ∀ i, v i ≤ L) :
    ∀ v ∈ C, oneHighEntropy k L ≤ finiteShannon v := by
  obtain ⟨w, hw, i, x, hx0, hx1, hwshape, hwmin⟩ := hshape
  have hxL : x ≤ L := by simpa [hwshape] using hcap w hw i
  have hentropy : finiteShannon w = oneHighEntropy k x := by
    rw [show w = (fun j => if j = i then x else (1-x)/((k:ℝ)-1)) from funext hwshape]
    exact finiteShannon_oneHigh hk i x
  intro v hv
  calc
    oneHighEntropy k L ≤ oneHighEntropy k x :=
      oneHighEntropy_antitoneOn k hk ⟨hx0,hx1⟩ ⟨hx0.trans hxL,hL⟩ hxL
    _ = finiteShannon w := hentropy.symm
    _ ≤ finiteShannon v := hwmin v hv

/-- The two limiting entropies need only converge separately. Strictness
of their limiting gap gives strict violation for every sufficiently
large finite input dimension. -/
theorem eventual_strict_gap_of_limits (single bell : ℕ → ℝ) (A B : ℝ)
    (hsingle : Tendsto single atTop (𝓝 A))
    (hbell : Tendsto bell atTop (𝓝 B)) (hgap : B < 2*A) :
    ∀ᶠ n in atTop, bell n < 2*single n := by
  have hlim : Tendsto (fun n => bell n - 2*single n) atTop (𝓝 (B-2*A)) :=
    hbell.sub (hsingle.const_mul 2)
  have hneg := hlim.eventually_lt_const (show B-2*A < 0 by linarith)
  filter_upwards [hneg] with n hn
  linarith

/-- The Bell state is an admissible input to the product channel, so
its output entropy bounds the minimum output entropy from above. -/
theorem eventual_product_violation_of_limits
    (single bell productMinimum : ℕ → ℝ) (A B : ℝ)
    (hsingle : Tendsto single atTop (𝓝 A))
    (hbell : Tendsto bell atTop (𝓝 B)) (hgap : B < 2*A)
    (hBellWitness : ∀ n, productMinimum n ≤ bell n) :
    ∀ᶠ n in atTop, productMinimum n < 2*single n := by
  filter_upwards [eventual_strict_gap_of_limits single bell A B hsingle hbell hgap]
    with n hn
  exact (hBellWitness n).trans_lt hn

namespace K182

/-- The normalized Bernoulli feasible body at `k=182,t=27/100000`.
This is the eigenvalue body used in the manuscript. -/
def normalizedFeasible : Set (Fin 182 → ℝ) :=
  {v | ∃ u : Fin 182 → ℝ,
    (∀ i, 0 ≤ u i) ∧ (∀ i, u i ≤ 1) ∧
    (∑ i, bernoulliCost t (u i)) ≤ 1/182 ∧
    v = (fun i => u i / ∑ j, u j)}

theorem normalizedFeasible_probability
    {v : Fin 182 → ℝ} (hv : v ∈ normalizedFeasible) :
    (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1 := by
  obtain ⟨u, hu0, _hu1, hc, rfl⟩ := hv
  have hs := sum_pos hu0 hc
  constructor
  · intro i
    exact div_nonneg (hu0 i) hs.le
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hs)

theorem normalizedFeasible_coordinate_le_L
    {v : Fin 182 → ℝ} (hv : v ∈ normalizedFeasible) (i : Fin 182) :
    v i ≤ L := by
  obtain ⟨u, hu0, hu1, hc, rfl⟩ := hv
  exact normalized_coordinate_le_L hu0 hu1 hc (sum_pos hu0 hc) i

/-- Conditional global certificate. The only analytic premise is precisely
the minimizer-shape reduction stated in the LaTeX appendix. Both the
global coordinate bound and the numerical log inequalities are proved,
not passed as hypotheses. -/
theorem entropy_gap_of_one_high_minimizer
    (hshape : HasOneHighEntropyMinimizer normalizedFeasible)
    {v : Fin 182 → ℝ} (hv : v ∈ normalizedFeasible) :
    (477 : ℝ)/1000000 < 2*finiteShannon v - _root_.ProjectionChannels.K182.bellEntropy := by
  have h := entropy_lower_bound_of_one_high_minimizer (by norm_num : 2 ≤ 182)
    normalizedFeasible hshape L (by norm_num [L])
    (fun _ hv i => normalizedFeasible_coordinate_le_L hv i) v hv
  have heq : oneHighEntropy 182 L = _root_.ProjectionChannels.K182.entropyLower := by
    norm_num [oneHighEntropy, L, _root_.ProjectionChannels.K182.entropyLower, _root_.ProjectionChannels.K182.cutoff]
  rw [heq] at h
  linarith [_root_.ProjectionChannels.K182.certified_entropy_gap]

/-- The conditional limiting-body certificate passes to finite input
dimensions once the single-output and Bell-output convergence theorems
are instantiated. It does not assume a numerical gap as a premise. -/
theorem eventual_gap_of_one_high_minimizer
    (hshape : HasOneHighEntropyMinimizer normalizedFeasible)
    {v : Fin 182 → ℝ} (hv : v ∈ normalizedFeasible)
    (single bell productMinimum : ℕ → ℝ)
    (hsingle : Tendsto single atTop (𝓝 (finiteShannon v)))
    (hbell : Tendsto bell atTop (𝓝 _root_.ProjectionChannels.K182.bellEntropy))
    (hBellWitness : ∀ n, productMinimum n ≤ bell n) :
    ∀ᶠ n in atTop, productMinimum n < 2*single n := by
  apply eventual_product_violation_of_limits single bell productMinimum
    (finiteShannon v) _root_.ProjectionChannels.K182.bellEntropy hsingle hbell _ hBellWitness
  have hgap := entropy_gap_of_one_high_minimizer hshape hv
  linarith

end K182

end ProjectionChannels

