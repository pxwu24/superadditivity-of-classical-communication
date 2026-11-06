import StrongConvergence.StrongConvergenceMomentCumulantRecurrence

/-! Bernoulli moments from the first-block recurrence and the proved quadratic
identity for Bernoulli free cumulants. -/
open PowerSeries
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.MomentCumulantRecurrence
open FreeCumulant

@[simp] theorem mk_bernoulliCumulant (t : ℝ) :
    mk (bernoulliCumulant t) = bernoulliCumulantSeries t := by
  ext n
  simp

/-- Any first-block moment recurrence driven by Bernoulli free cumulants has
the Bernoulli moments in every order. -/
theorem bernoulli_moments_of_convolution_recurrence (t : ℝ)
    (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (hM0 : M 0=1)
    (hzero : ∀ r, B 0 r = if r=0 then 1 else 0)
    (hsucc_zero : ∀ n, B (n+1) 0=0)
    (hrec : ∀ n r, B (n+1) (r+1) = ∑ p ∈ Finset.range (n+1), M p*B (n-p) r)
    (hMrec : ∀ n, M (n+1) =
      ∑ r ∈ Finset.range (n+2), bernoulliCumulant t r*B (n+1) r) :
    ∀ n, M n = if n=0 then 1 else t := by
  have hformal := formalSubst_of_convolution_recurrence (bernoulliCumulant t) M B
    (bernoulliCumulant_zero t) hM0 hzero hsucc_zero hrec hMrec
  rw [mk_bernoulliCumulant] at hformal
  have heq := bernoulliMomentSeries_unique t (mk M) (by simpa using hM0) hformal
  intro n
  have h := congrArg (coeff ℝ n) heq
  simpa only [bernoulliMomentSeries, coeff_mk] using h

theorem bernoulli_moments_of_split_recurrence (t : ℝ)
    (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (hM0 : M 0=1)
    (hzero : ∀ r, B 0 r = if r=0 then 1 else 0)
    (hsucc_zero : ∀ n, B (n+1) 0=0)
    (hrec : ∀ n r, B (n+1) (r+1) = (if r=0 then M n else 0) +
      ∑ p ∈ Finset.range n, M p*B (n-p) r)
    (hMrec : ∀ n, M (n+1) =
      ∑ r ∈ Finset.range (n+2), bernoulliCumulant t r*B (n+1) r) :
    ∀ n, M n = if n=0 then 1 else t :=
  bernoulli_moments_of_convolution_recurrence t M B hM0 hzero hsucc_zero
    (convolution_of_split_recurrence M B hzero hrec) hMrec

#print axioms bernoulli_moments_of_split_recurrence
end ProjectionChannels.MomentCumulantRecurrence
