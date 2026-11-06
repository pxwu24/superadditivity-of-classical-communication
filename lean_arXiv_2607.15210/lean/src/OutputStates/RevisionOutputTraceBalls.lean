import OutputStates.RevisionOutputTraceGeometry
import Preliminaries.RevisionTraceDuality

/-! Compact convex trace-norm balls and the reciprocal norming witness. -/
open Matrix Set
open scoped BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k : ℕ} [NeZero k]

lemma traceNorm_le_iff_pairing_le (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) (r : ℝ) :
    hermitianTraceNorm M ≤ r ↔
      ∀ H : Matrix (Fin k) (Fin k) ℂ, H.IsHermitian → hermitianOperatorNorm H ≤ 1 →
        (Matrix.trace (H*M)).re ≤ r := by
  rw [hermitianTraceNorm_eq M hM]
  have hg := trace_operator_duality_named M hM
  constructor
  · intro hr H hH hn
    exact (hg.2 ⟨H, ⟨hH, hn⟩, rfl⟩).trans hr
  · intro h
    obtain ⟨H, ⟨hH, hn⟩, heq⟩ := hg.1
    rw [← heq]
    exact h H hH hn

lemma trace_pairing_le (M H : Matrix (Fin k) (Fin k) ℂ)
    (hM : M.IsHermitian) (hH : H.IsHermitian) (hn : hermitianOperatorNorm H ≤ 1) :
    (Matrix.trace (H*M)).re ≤ hermitianTraceNorm M :=
  (traceNorm_le_iff_pairing_le M hM _).mp le_rfl H hH hn

lemma hermitianTraceNorm_neg (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) :
    hermitianTraceNorm (-M) = hermitianTraceNorm M := by
  have hupper (X : Matrix (Fin k) (Fin k) ℂ) (hX : X.IsHermitian) :
      hermitianTraceNorm (-X) ≤ hermitianTraceNorm X := by
    apply (traceNorm_le_iff_pairing_le (-X) hX.neg _).mpr
    intro H hH hn
    have hb := trace_pairing_le X (-H) hX hH.neg (by simpa only [hermitianOperatorNorm_neg] using hn)
    simpa only [Matrix.mul_neg, Matrix.neg_mul] using hb
  exact le_antisymm (hupper M hM) (by simpa only [neg_neg] using hupper (-M) hM.neg)

lemma hermitianTraceNorm_add_le (M N : Matrix (Fin k) (Fin k) ℂ)
    (hM : M.IsHermitian) (hN : N.IsHermitian) :
    hermitianTraceNorm (M+N) ≤ hermitianTraceNorm M + hermitianTraceNorm N := by
  apply (traceNorm_le_iff_pairing_le _ (hM.add hN) _).mpr
  intro H hH hn
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add (trace_pairing_le M H hM hH hn) (trace_pairing_le N H hN hH hn)

lemma hermitianTraceNorm_smul_le (c : ℝ) (hc : 0 ≤ c)
    (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) :
    hermitianTraceNorm (c • M) ≤ c * hermitianTraceNorm M := by
  have hcm : (c • M).IsHermitian := by
    rw [Matrix.IsHermitian]
    simp only [Matrix.conjTranspose_smul, hM.eq, star_trivial]
  apply (traceNorm_le_iff_pairing_le _ hcm _).mpr
  intro H hH hn
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using
    mul_le_mul_of_nonneg_left (trace_pairing_le M H hM hH hn) hc

lemma hermitianTraceNorm_zero : hermitianTraceNorm (0 : Matrix (Fin k) (Fin k) ℂ) = 0 := by
  apply le_antisymm _ (hermitianTraceNorm_nonneg _)
  apply (traceNorm_le_iff_pairing_le _ Matrix.isHermitian_zero _).mpr
  intro H _ _
  simp

def traceBall (r : ℝ) : Set (Matrix (Fin k) (Fin k) ℂ) :=
  {M | M.IsHermitian ∧ hermitianTraceNorm M ≤ r}

lemma traceBall_closed (r : ℝ) : IsClosed (traceBall (k := k) r) := by
  have heq : traceBall (k := k) r = {M | M.IsHermitian} ∩
      {M | ∀ H : Matrix (Fin k) (Fin k) ℂ, H.IsHermitian → hermitianOperatorNorm H ≤ 1 →
        (Matrix.trace (H*M)).re ≤ r} := by
    ext M
    constructor
    · rintro ⟨hM, hn⟩
      exact ⟨hM, (traceNorm_le_iff_pairing_le M hM r).mp hn⟩
    · rintro ⟨hM, hn⟩
      exact ⟨hM, (traceNorm_le_iff_pairing_le M hM r).mpr hn⟩
  rw [heq]
  apply (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro H
  apply isClosed_iInter
  intro hH
  apply isClosed_iInter
  intro hn
  exact isClosed_le (continuous_trace_pairing H) continuous_const

lemma traceBall_compact (r : ℝ) : IsCompact (traceBall (k := k) r) := by
  apply (isCompact_closedBall (0 : Matrix (Fin k) (Fin k) ℂ) r).of_isClosed_subset (traceBall_closed r)
  intro M hM
  exact mem_closedBall_zero_iff.mpr ((norm_le_hermitianTraceNorm M hM.1).trans hM.2)

lemma traceBall_convex (r : ℝ) : Convex ℝ (traceBall (k := k) r) := by
  intro M hM N hN a b ha hb hab
  have haM : (a • M).IsHermitian := by
    rw [Matrix.IsHermitian]; simp only [Matrix.conjTranspose_smul, hM.1.eq, star_trivial]
  have hbN : (b • N).IsHermitian := by
    rw [Matrix.IsHermitian]; simp only [Matrix.conjTranspose_smul, hN.1.eq, star_trivial]
  refine ⟨haM.add hbN, ?_⟩
  calc
    _ ≤ hermitianTraceNorm (a • M) + hermitianTraceNorm (b • N) :=
      hermitianTraceNorm_add_le _ _ haM hbN
    _ ≤ a*hermitianTraceNorm M + b*hermitianTraceNorm N :=
      add_le_add (hermitianTraceNorm_smul_le a ha M hM.1) (hermitianTraceNorm_smul_le b hb N hN.1)
    _ ≤ a*r+b*r := add_le_add (mul_le_mul_of_nonneg_left hM.2 ha) (mul_le_mul_of_nonneg_left hN.2 hb)
    _ = r := by rw [← add_mul, hab, one_mul]

lemma zero_mem_traceBall {r : ℝ} (hr : 0 ≤ r) : (0 : Matrix (Fin k) (Fin k) ℂ) ∈ traceBall r :=
  ⟨Matrix.isHermitian_zero, by simpa only [hermitianTraceNorm_zero] using hr⟩

/-- The operator norm is attained by a signed rank-one state on the unit
trace-norm ball. -/
lemma traceBall_norming_witness (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.IsHermitian) :
    ∃ M ∈ traceBall (k := k) 1, (Matrix.trace (H*M)).re = hermitianOperatorNorm H := by
  obtain ⟨ρ, hρ, heq⟩ := density_opNorm_witness H hH
  by_cases hp : 0 ≤ (Matrix.trace (H*ρ)).re
  · exact ⟨ρ, ⟨hρ.1.isHermitian, (hermitianTraceNorm_density hρ).le⟩,
      by rwa [abs_of_nonneg hp] at heq⟩
  · refine ⟨-ρ, ⟨hρ.1.isHermitian.neg, ?_⟩, ?_⟩
    · rw [hermitianTraceNorm_neg ρ hρ.1.isHermitian, hermitianTraceNorm_density hρ]
    · rw [Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re]
      rwa [abs_of_neg (lt_of_not_ge hp)] at heq

end
end RevisionOutput
