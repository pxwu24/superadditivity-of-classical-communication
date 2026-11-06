import Entropy.Defs

/-!
Deterministic, countable finite-difference transfer used in the final draft's
Bell second-moment argument. This module does not assert the free-convolution
log-potential formula or the random-matrix convergence theorem.
-/

open Filter
noncomputable section
namespace BellLimitVerification

/-- A diagonal limit argument with a uniform approximation error.
For each fixed discretization index `j`, `d j n` converges to `ell j`.
The approximation of `-a n` by `d j n` is uniform in all sufficiently large `n`.
As its error vanishes and `ell j` converges to `L`, `a n` converges to `-L`. -/
theorem moment_limit_of_uniform_approximation
    (a : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (ell err : ℕ → ℝ) (L : ℝ)
    (hd : ∀ j, Tendsto (d j) atTop (nhds (ell j)))
    (hell : Tendsto ell atTop (nhds L))
    (herr : Tendsto err atTop (nhds 0))
    (hbound : ∀ j, ∀ᶠ n in atTop, |a n + d j n| ≤ err j) :
    Tendsto a atTop (nhds (-L)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨Je, hJe⟩ := Metric.tendsto_atTop.mp herr (ε / 3) hε3
  obtain ⟨Jl, hJl⟩ := Metric.tendsto_atTop.mp hell (ε / 3) hε3
  let j := max Je Jl
  have he : err j < ε / 3 := by
    have h := hJe j (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hl : |ell j - L| < ε / 3 := by
    simpa only [Real.dist_eq] using hJl j (le_max_right _ _)
  obtain ⟨Nd, hNd⟩ := Metric.tendsto_atTop.mp (hd j) (ε / 3) hε3
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp (hbound j)
  refine ⟨max Nd Nb, ?_⟩
  intro n hn
  have hd' : |d j n - ell j| < ε / 3 := by
    simpa only [Real.dist_eq] using hNd n (le_trans (le_max_left _ _) hn)
  have hb := hNb n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq]
  calc
    |a n - -L| = |(a n + d j n) + (ell j - d j n) + (L - ell j)| := by congr 1; ring
    _ ≤ |a n + d j n| + |ell j - d j n| + |L - ell j| := by
      exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ = |a n + d j n| + |d j n - ell j| + |ell j - L| := by
      rw [abs_sub_comm (ell j) (d j n), abs_sub_comm L (ell j)]
    _ < ε := by linarith

/-- Central difference quotient at the origin, with the same convention as the
paper. The nonzero-step condition is needed in applications, not for the purely
algebraic/continuity transfer below. -/
def centralDifference (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (f x + f (-x) - 2 * f 0) / x ^ 2

/-- Pointwise convergence at the three evaluation points implies convergence of
the corresponding fixed-step central difference. -/
theorem centralDifference_tendsto
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (hx : Tendsto (fun n => f n x) atTop (nhds (F x)))
    (hnx : Tendsto (fun n => f n (-x)) atTop (nhds (F (-x))))
    (h0 : Tendsto (fun n => f n 0) atTop (nhds (F 0))) :
    Tendsto (fun n => centralDifference (f n) x) atTop
      (nhds (centralDifference F x)) := by
  unfold centralDifference
  exact ((hx.add hnx).sub (tendsto_const_nhds.mul h0)).div_const _

/-- The central-difference argument in Proposition "Second moments after local
normalization", stated with its analytic input hypotheses explicitly exposed.
Only a countable sequence of steps and pointwise limits at those steps is used. -/
theorem moment_limit_of_central_differences
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (a step err : ℕ → ℝ) (L : ℝ)
    (hpoint : ∀ j, Tendsto (fun n => f n (step j)) atTop (nhds (F (step j))))
    (hneg : ∀ j, Tendsto (fun n => f n (-step j)) atTop (nhds (F (-step j))))
    (hzero : Tendsto (fun n => f n 0) atTop (nhds (F 0)))
    (hderiv : Tendsto (fun j => centralDifference F (step j)) atTop (nhds L))
    (herr : Tendsto err atTop (nhds 0))
    (hbound : ∀ j, ∀ᶠ n in atTop,
      |a n + centralDifference (f n) (step j)| ≤ err j) :
    Tendsto a atTop (nhds (-L)) := by
  exact moment_limit_of_uniform_approximation a
    (fun j n => centralDifference (f n) (step j))
    (fun j => centralDifference F (step j)) err L
    (fun j => centralDifference_tendsto f F (step j) (hpoint j) (hneg j) hzero)
    hderiv herr hbound

#print axioms moment_limit_of_uniform_approximation
#print axioms centralDifference_tendsto
#print axioms moment_limit_of_central_differences
end BellLimitVerification
