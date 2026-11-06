import StrongConvergence.StrongConvergenceSpectralEstimate
import Mathlib.Topology.Order.Compact

/-!
# Affine norm control from the two extreme spectral bounds

The upper edge of `M` and the upper edge of `-M` enclose the full spectrum.
Their bounds give an affine operator norm bound with the same error. These
are finite-dimensional deterministic lemmas, without a random-convergence
assumption.
-/

open Matrix ProjectionChannels Filter
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section

namespace StrongConvergence

/-- The affine absolute-value maximum on a set is attained at one of its
two endpoints. The set itself need not be an interval. -/
theorem sSup_abs_add_eq_max_of_endpoints {S : Set ℝ} {l u : ℝ}
    (hl : IsLeast S l) (hu : IsGreatest S u) (c : ℝ) :
    sSup ((fun x : ℝ => |c+x|) '' S) = max |c+l| |c+u| := by
  apply IsGreatest.csSup_eq
  constructor
  · rcases le_total |c+l| |c+u| with h | h
    · rw [max_eq_right h]
      exact ⟨u, hu.1, rfl⟩
    · rw [max_eq_left h]
      exact ⟨l, hl.1, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    apply abs_le.mpr
    constructor
    · exact (neg_le_neg (le_max_left _ _)).trans
        ((neg_abs_le (c+l)).trans (add_le_add_left (hl.2 hx) c))
    · exact (add_le_add_left (hu.2 hx) c).trans
        ((le_abs_self (c+u)).trans (le_max_right _ _))

/-- Compact nonempty spectral supports have both endpoints, so their
affine support norm has the endpoint formula. -/
theorem sSup_abs_add_eq_max {S : Set ℝ} (hS : IsCompact S)
    (hne : S.Nonempty) (c : ℝ) :
    sSup ((fun x : ℝ => |c+x|) '' S) =
      max |c+sInf S| |c+sSup S| :=
  sSup_abs_add_eq_max_of_endpoints (hS.isLeast_sInf hne) (hS.isGreatest_sSup hne) c

variable {N K : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
  [Fintype K] [DecidableEq K]

omit [Fintype N] [DecidableEq N] [Nonempty N] [DecidableEq K] in
/-- Changing every coefficient sign negates the actual block compression. -/
theorem blockCompression_neg (P : K → Matrix N N ℂ) (a : K → ℝ) :
    blockCompression P (fun i => -a i) = -blockCompression P a := by
  simp only [blockCompression, Complex.ofReal_neg, neg_smul, Finset.sum_neg_distrib]

/-- Two largest-eigenvalue bounds control the entire affine operator norm. -/
theorem norm_shift_le_of_largest_le {M : Matrix N N ℂ} (hM : M.IsHermitian)
    (c l u : ℝ) (hu : largestEigenvalue hM ≤ u)
    (hl : largestEigenvalue hM.neg ≤ -l) :
    ‖(c : ℂ) • (1 : Matrix N N ℂ) + M‖ ≤ max |c+l| |c+u| := by
  have hH : ((c : ℂ) • (1 : Matrix N N ℂ) + M).IsHermitian := by
    apply Matrix.IsHermitian.add _ hM
    simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  apply hermitian_norm_le_interval hH (c+l) (c+u)
  · have h := (largest_le_iff_shift_posSemidef hM.neg (-l)).mp hl
    convert h using 1
    simp only [Complex.ofReal_add, Complex.ofReal_neg, add_smul, neg_smul]
    abel
  · have h := (largest_le_iff_shift_posSemidef hM u).mp hu
    convert h using 1
    simp only [Complex.ofReal_add, add_smul]
    abel

/-- Errors of size `ε` at the two edges give an error of at most `ε` in
every affine norm test, including tests whose shifted support changes sign. -/
theorem norm_shift_le_of_largest_le_add {M : Matrix N N ℂ} (hM : M.IsHermitian)
    (c l u ε : ℝ) (hε : 0 ≤ ε)
    (hu : largestEigenvalue hM ≤ u+ε)
    (hl : largestEigenvalue hM.neg ≤ -l+ε) :
    ‖(c : ℂ) • (1 : Matrix N N ℂ) + M‖ ≤ max |c+l| |c+u| + ε := by
  have hl' : largestEigenvalue hM.neg ≤ -(l-ε) := by linarith
  apply (norm_shift_le_of_largest_le hM c (l-ε) (u+ε) hu hl').trans
  apply max_le
  · have h := abs_sub (c+l) ε
    rw [abs_of_nonneg hε] at h
    have heq : c+(l-ε) = (c+l)-ε := by ring
    rw [heq]
    exact h.trans (add_le_add_right (le_max_left _ _) _)
  · have h := abs_add (c+u) ε
    rw [abs_of_nonneg hε] at h
    have heq : c+(u+ε) = (c+u)+ε := by ring
    rw [heq]
    exact h.trans (add_le_add_right (le_max_right _ _) _)

/-- Eventual edge enclosures transfer pointwise to eventual affine norm
enclosures; the index set and filter are arbitrary. -/
theorem eventually_norm_shift_le_of_largest_le_add
    {ι : Type*} {L : Filter ι} (d : ι → Type*)
    [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)] [∀ i, Nonempty (d i)]
    (M : (i : ι) → Matrix (d i) (d i) ℂ)
    (hM : ∀ i, (M i).IsHermitian) (c l u ε : ℝ) (hε : 0 ≤ ε)
    (hu : ∀ᶠ i in L, largestEigenvalue (hM i) ≤ u+ε)
    (hl : ∀ᶠ i in L, largestEigenvalue (hM i).neg ≤ -l+ε) :
    ∀ᶠ i in L,
      ‖(c : ℂ) • (1 : Matrix (d i) (d i) ℂ) + M i‖ ≤ max |c+l| |c+u| + ε := by
  filter_upwards [hu, hl] with i hui hli
  exact norm_shift_le_of_largest_le_add (hM i) c l u ε hε hui hli

/-- The deterministic last step of the norm argument: upper bounds for both
edges, together with the lower norm bound supplied by weak spectral
convergence, imply the affine norm limit. -/
theorem tendsto_norm_shift_of_edges_and_lower
    {ι : Type*} {L : Filter ι} (d : ι → Type*)
    [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)] [∀ i, Nonempty (d i)]
    (M : (i : ι) → Matrix (d i) (d i) ℂ)
    (hM : ∀ i, (M i).IsHermitian) (c l u : ℝ)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in L, largestEigenvalue (hM i) ≤ u+ε)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in L, largestEigenvalue (hM i).neg ≤ -l+ε)
    (hlo : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in L,
      max |c+l| |c+u| - ε <
        ‖(c : ℂ) • (1 : Matrix (d i) (d i) ℂ) + M i‖) :
    Tendsto (fun i => ‖(c : ℂ) • (1 : Matrix (d i) (d i) ℂ) + M i‖)
      L (𝓝 (max |c+l| |c+u|)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := by linarith
  have hhi := eventually_norm_shift_le_of_largest_le_add d M hM c l u (ε/2)
    hhalf.le (hu _ hhalf) (hl _ hhalf)
  filter_upwards [hhi, hlo _ hhalf] with i hhi hlo
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end StrongConvergence

#print axioms StrongConvergence.sSup_abs_add_eq_max_of_endpoints
#print axioms StrongConvergence.sSup_abs_add_eq_max
#print axioms StrongConvergence.blockCompression_neg
#print axioms StrongConvergence.norm_shift_le_of_largest_le
#print axioms StrongConvergence.norm_shift_le_of_largest_le_add
#print axioms StrongConvergence.eventually_norm_shift_le_of_largest_le_add
#print axioms StrongConvergence.tendsto_norm_shift_of_edges_and_lower
