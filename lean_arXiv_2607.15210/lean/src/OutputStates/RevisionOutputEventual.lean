import OutputStates.RevisionOutputProbability

/-!
# Removing the finite exceptional prefix

Marginal invertibility is proved eventually from the negative constant
compression. Singular early terms are replaced temporarily by the identity
projection. Strong convergence and the desired output limit are unchanged
by this almost-sure eventual equality. Thus no additional invertibility
hypothesis is needed in the final theorem.
-/

open MeasureTheory Filter Set Matrix Metric
open PreliminariesMatrix ProjectionChannels OutputSpaceVerification ProjectionChannelsCP
open scoped Topology BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma posDef_of_largest_neg_lt_zero {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (hneg : largestEigenvalue hM.neg < 0) : M.PosDef := by
  let r := largestEigenvalue hM.neg
  have hp := (largest_le_iff_shift_posSemidef hM.neg r).mp le_rfl
  have hd : ((-r : ℝ) : ℂ) • (1 : Matrix n n ℂ) |>.PosDef :=
    ProjectionChannelsCP.posDef_real_smul _ Matrix.PosDef.one (-r) (neg_pos.mpr hneg)
  have h := hd.add_posSemidef hp
  convert h using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_neg]
  ring

lemma negative_constant_bodySupport {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hkt : 1 < (k : ℝ)^2*t) :
    bodySupport k t (fun _ => -1) < 0 := by
  obtain ⟨u, hu, heq⟩ := (bodySupport_isGreatest ht ht1 (fun _ : Fin k => -1)).1
  have hp := body_mass_pos hk ht hkt u hu
  rw [← heq]
  simpa only [neg_one_mul, Finset.sum_neg_distrib] using neg_neg_of_pos hp

lemma localConjugate_one {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A]
    (P : Matrix (A × B) (A × B) ℂ) : localConjugate P (1 : Matrix B B ℂ) = P := by
  simp [localConjugate, Matrix.kronecker]

/-- Strong convergence itself forces the required local normalization to
exist eventually, using the strictly negative limiting edge at a=-1. -/
theorem ae_eventually_marginal_posDef
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hBM : AmplifiedBlockModifiedStrongInput μ k t P) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, (traceB (P ω N)).PosDef := by
  have hP := fun ω N => HaarProjection.projection_posSemidef (P ω N) (hH ω N) (hId ω N)
  have hMarg := fun ω N => HaarProjection.traceB_posSemidef (P ω N) (hP ω N)
  have hc := random_compression_from_amplified_block_strong μ k hk t ht ht1 P hH hId hBM
  filter_upwards [hc] with ω hω
  have hlim := hω (fun _ => -1)
  rw [bernoulliSupport_eq_bodySupport] at hlim
  have heq (N : ℕ) : blockCompression (diagonalBlock (P ω N)) (fun _ => -1) = -traceB (P ω N) := by
    ext a b
    simp [blockCompression, diagonalBlock, traceB, Matrix.sum_apply]
  have hc' : Tendsto (fun N => largestEigenvalue (hMarg ω N).isHermitian.neg)
      atTop (𝓝 (bodySupport k t (fun _ => -1))) := by
    simpa only [heq] using hlim
  have he := hc'.eventually (gt_mem_nhds (negative_constant_bodySupport hk ht.le ht1.le hkt))
  filter_upwards [he] with N hN
  exact posDef_of_largest_neg_lt_zero _ (hMarg ω N).isHermitian hN

/-- Replace only terms for which the marginal is singular. -/
def regularizeProjection {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  if (traceB P).PosDef then P else 1

lemma regularizeProjection_eq {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P : Matrix (A × B) (A × B) ℂ) (h : (traceB P).PosDef) : regularizeProjection P = P := by
  simp only [regularizeProjection, if_pos h]

lemma regularizeProjection_hermitian {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : Matrix (A × B) (A × B) ℂ) (hP : P.IsHermitian) : (regularizeProjection P).IsHermitian := by
  unfold regularizeProjection
  split_ifs
  · exact hP
  · exact Matrix.isHermitian_one

lemma regularizeProjection_idempotent {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : Matrix (A × B) (A × B) ℂ) (hP : P*P=P) :
    regularizeProjection P * regularizeProjection P = regularizeProjection P := by
  unfold regularizeProjection
  split_ifs
  · exact hP
  · simp

lemma regularizeProjection_marginal_posDef {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty B]
    (P : Matrix (A × B) (A × B) ℂ) : (traceB (regularizeProjection P)).PosDef := by
  unfold regularizeProjection
  split_ifs with h
  · exact h
  · have heq : traceB (1 : Matrix (A × B) (A × B) ℂ) =
        (Fintype.card B : ℂ) • (1 : Matrix A A ℂ) := by
      ext a b
      by_cases hab : a = b
      · subst b; simp [traceB, Matrix.one_apply]
      · simp [traceB, Matrix.one_apply, hab]
    rw [heq]
    exact ProjectionChannelsCP.posDef_real_smul _ Matrix.PosDef.one (Fintype.card B)
      (by exact_mod_cast Fintype.card_pos)

/-- Almost-sure eventual equality preserves the permitted strong-convergence
input, including its actual limiting probability law. -/
lemma amplified_block_input_of_ae_eventually_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ} {t : ℝ}
    (P Q : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (h : ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, Q ω N = P ω N)
    (hBM : AmplifiedBlockModifiedStrongInput μ k t P) :
    AmplifiedBlockModifiedStrongInput μ k t Q := by
  intro a
  obtain ⟨ν, hν, hnorm⟩ := hBM a
  refine ⟨ν, hν, fun c => ?_⟩
  filter_upwards [h, hnorm c] with ω hω hc
  apply hc.congr'
  filter_upwards [hω] with N hN
  rw [hN]

/-- The normalization formula is defined at every index; after eventual
invertibility this is exactly the inverse positive square root in the paper. -/
def marginalNormalizer {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P : Matrix (A × B) (A × B) ℂ) (hP : P.PosSemidef) : Matrix A A ℂ :=
  (HaarProjection.traceB_posSemidef P hP).sqrt⁻¹

lemma sqrt_congr_of_matrix_eq {n : Type} [Fintype n] [DecidableEq n]
    {M N : Matrix n n ℂ} (hM : M.PosSemidef) (hN : N.PosSemidef) (heq : M=N) :
    hM.sqrt = hN.sqrt := by
  subst N
  rfl

/-- **Theorem III.1**, with the finite exceptional prefix removed inside
the proof. Apart from the explicit projection assumptions, only the permitted
block-modified strong-convergence theorem is an input. Its repeated use for
fixed output-unitary rotations is the same black box, not an edge assumption. -/
theorem output_space_limit_eventual_from_block_strong
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hBM : ∀ V : Matrix.unitaryGroup (Fin k) ℂ,
      AmplifiedBlockModifiedStrongInput μ k t
        (fun ω N => localConjugate (P ω N) (V : Matrix (Fin k) (Fin k) ℂ))) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => traceHausdorff
      (normalizedOutput (P ω N)
        (marginalNormalizer (P ω N) (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))) ''
          densityMatrices (Fin (N+1))) (spectralBody k t)) atTop (𝓝 0) := by
  have hbase : AmplifiedBlockModifiedStrongInput μ k t P := by
    simpa only [Matrix.UnitaryGroup.one_val, localConjugate_one] using hBM 1
  have hevent := ae_eventually_marginal_posDef μ hk ht ht1 hkt P hH hId hbase
  let Q := fun ω N => regularizeProjection (P ω N)
  have hQH := fun ω N => regularizeProjection_hermitian (P ω N) (hH ω N)
  have hQI := fun ω N => regularizeProjection_idempotent (P ω N) (hId ω N)
  have hQA := fun ω N => regularizeProjection_marginal_posDef (P ω N)
  have heq : ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, Q ω N = P ω N := by
    filter_upwards [hevent] with ω hω
    filter_upwards [hω] with N hN
    exact regularizeProjection_eq _ hN
  have hQB : ∀ V : Matrix.unitaryGroup (Fin k) ℂ,
      AmplifiedBlockModifiedStrongInput μ k t
        (fun ω N => localConjugate (Q ω N) (V : Matrix (Fin k) (Fin k) ℂ)) := by
    intro V
    apply amplified_block_input_of_ae_eventually_eq
      (fun ω N => localConjugate (P ω N) (V : Matrix (Fin k) (Fin k) ℂ))
    · filter_upwards [heq] with ω hω
      filter_upwards [hω] with N hN
      rw [hN]
    · exact hBM V
  have hlimit := output_space_limit_from_block_strong μ hk ht ht1 hkt Q hQH hQI hQA hQB
  filter_upwards [heq, hevent, hlimit] with ω hω hpos hlim
  apply hlim.congr'
  filter_upwards [hω, hpos] with N heqN hposN
  have hs : (hQA ω N).posSemidef.sqrt =
      (HaarProjection.traceB_posSemidef (P ω N)
        (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))).sqrt := by
    have hm : traceB (Q ω N) = traceB (P ω N) := congrArg traceB heqN
    exact sqrt_congr_of_matrix_eq _ _ hm
  change traceHausdorff (normalizedOutput (Q ω N) (hQA ω N).posSemidef.sqrt⁻¹ '' _) _ = _
  rw [hs, heqN]
  rfl

end
end RevisionOutput
