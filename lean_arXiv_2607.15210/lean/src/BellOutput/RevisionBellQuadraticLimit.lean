import BellOutput.RevisionBellLogConvergence
import BellOutput.RevisionBellHessianResult
import BellOutput.RevisionBellCentralDerivative
import BellOutput.RevisionBellLimitFromMoments
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual Proposition A.3 from the permitted block theorem alone, together
with finite-dimensional positivity and the definition of local normalization. -/
open MeasureTheory Filter Finset
open PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace RevisionBell

lemma exists_central_steps (R : ℝ) (hR : 0 ≤ R) :
    ∃ step : ℕ → ℝ, Tendsto step atTop (nhds 0) ∧
      (∀ j, step j ≠ 0) ∧ (∀ j, |step j| *R ≤ 1/2) := by
  let step := fun j : ℕ => (1/((j:ℝ)+1))/(2*(R+1))
  have hd : 0 < 2*(R+1) := by positivity
  refine ⟨step,?_,?_,?_⟩
  · simpa only [zero_div] using tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2*(R+1))
  · intro j
    dsimp [step]
    positivity
  · intro j
    have hj : 0 < (j:ℝ)+1 := by positivity
    have hs : 0 ≤ step j := by dsimp [step]; positivity
    rw [abs_of_nonneg hs]
    dsimp [step]
    have hi : 1/((j:ℝ)+1) ≤ 1 := (div_le_one hj).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_right hi hR]

/-- For each fixed Hermitian output test, the actual normalized matrix square
moment converges almost surely. The only probabilistic input is full
block-modified strong convergence. -/
theorem ae_normalized_square_moment_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0<k) (ht0 : 0<t) (ht1 : t<1)
    (hkt : 1<(k:ℝ)^2*t)
    (P : Ω → (n : ℕ) → Matrix (Fin (n+1) × Fin k) (Fin (n+1) × Fin k) ℂ)
    (hH : ∀ ω n, (P ω n).IsHermitian)
    (hId : ∀ ω n, P ω n*P ω n=P ω n)
    (hFull : FullBlockModifiedStrongInput μ k t P hH)
    (D : Ω → (n : ℕ) → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hD : ∀ ω n, (D ω n).IsHermitian)
    (hn : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, D ω n*traceB (P ω n)*D ω n=1)
    (H : Matrix (Fin k) (Fin k) ℂ) (hHerm : H.IsHermitian) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (1/((n+1:ℕ):ℝ))*(Matrix.trace
      ((D ω n*contraction (P ω n) H*D ω n)*(D ω n*contraction (P ω n) H*D ω n))).re)
      atTop (nhds (-BellLimitVerification.hessianC0 k t*(Matrix.trace H).re*(Matrix.trace H).re-
        BellLimitVerification.hessianC1 k t*(Matrix.trace (H*H)).re)) := by
  choose ν hν hnorm hweak using fun x : ℝ =>
    hFull hHerm.eigenvectorUnitary (fun i => 1+x*hHerm.eigenvalues i)
  let F := fun x => logPotential (ν x) 0
  have hconv (x : ℝ) (hx : |x| *‖H‖ ≤ 1/2) : ∀ᵐ ω ∂μ,
      Tendsto (fun n => matrixLogPotential (P ω n) (1+(x:ℂ) • H)) atTop (nhds (F x)) :=
    ae_matrixLogPotential_affine_tendsto μ hk ht0 ht1 hkt P hH hId hFull H hHerm x hx
      (ν x) (hν x) (hweak x)
  have hμnear : ∀ᶠ x in nhds (0:ℝ), IsBernoulliFreeSumLaw k t
      (fun i => 1+x*hHerm.eigenvalues i) (ν x) := Filter.Eventually.of_forall hν
  have hdiff := bernoulli_logPotential_eventually_differentiable hk ht0 ht1 hkt hHerm.eigenvalues ν hμnear
  have hhess := bernoulli_logPotential_hessian hk ht0 ht1 hkt hHerm.eigenvalues ν hμnear
  obtain ⟨step,hstep,hstep0,hsmall⟩ := exists_central_steps ‖H‖ (norm_nonneg _)
  have hsecond := centralDifference_sequence_tendsto F (deriv F) _
    (hdiff.mono fun x hx => hx.hasDerivAt) hhess step hstep hstep0
  have hp := ae_all_iff.mpr (fun j => hconv (step j) (hsmall j))
  have hm := ae_all_iff.mpr (fun j => hconv (-step j) (by simpa only [abs_neg] using hsmall j))
  have hz := hconv 0 (by norm_num)
  filter_upwards [hn,hp,hm,hz] with ω hnω hpω hmω hzω
  have hlim := matrix_square_moment_limit_eventual_normalization (fun n => Fin (n+1))
    (P ω) (D ω) (fun n => HaarProjection.projection_posSemidef _ (hH ω n) (hId ω n))
    (hD ω) hnω H hHerm F _ step hstep hstep0 hsmall hpω
    (fun j => by simpa only [Complex.ofReal_neg, neg_smul, ← sub_eq_add_neg] using hmω j)
    (by simpa using hzω) hsecond
  rw [← trace_re_eq_eigenvalue_sum H hHerm,
    ← trace_square_re_eq_eigenvalue_squares H hHerm] at hlim
  convert hlim using 1 <;> try simp only [Fintype.card_fin]
  congr 1
  ring

end RevisionBell
