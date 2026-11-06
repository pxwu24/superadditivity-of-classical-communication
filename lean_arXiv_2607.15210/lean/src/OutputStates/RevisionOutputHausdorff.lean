import OutputStates.RevisionOutputTraceBalls
import OutputStates.RevisionOutputMetricComparison

/-!
# Lemma III.3: exact trace/operator support-Hausdorff duality

The trace-norm balls are genuinely compact and convex. Separating their
Minkowski sums with the state bodies, and representing the separating real
functional by a Hermitian trace pairing, proves the exact duality formula.
There is no assumed minimax or norm-duality statement in this proof.
-/

open Matrix Set Metric
open scoped BigOperators ComplexOrder Pointwise
namespace RevisionOutput
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k : ℕ} [NeZero k]

lemma hermitian_real_smul (a : ℝ) (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) :
    (a • M).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp only [Matrix.conjTranspose_smul, hM.eq, star_trivial]

lemma real_trace_smul_left (a : ℝ) (H M : Matrix (Fin k) (Fin k) ℂ) :
    (Matrix.trace ((a • H)*M)).re = a * (Matrix.trace (H*M)).re := by
  rw [Matrix.smul_mul, Matrix.trace_smul]
  simp [Complex.real_smul]

lemma trace_pairing_abs_le_traceNorm_named (M H : Matrix (Fin k) (Fin k) ℂ)
    (hM : M.IsHermitian) (hH : H.IsHermitian) :
    |(Matrix.trace (H*M)).re| ≤ hermitianOperatorNorm H * hermitianTraceNorm M := by
  rw [hermitianTraceNorm_eq M hM]
  exact trace_pairing_abs_le_traceNorm M H hM hH

/-- A support-function radius bound implies membership in the trace-norm
neighborhood; the separating functional is constructed in the proof. -/
lemma mem_add_traceBall_of_support_le
    (K : Set (Matrix (Fin k) (Fin k) ℂ)) (hK : IsCompact K) (hneK : K.Nonempty)
    (hcK : Convex ℝ K) (hHK : ∀ M ∈ K, M.IsHermitian)
    {r : ℝ} (hr : 0 ≤ r) (X : Matrix (Fin k) (Fin k) ℂ) (hX : X.IsHermitian)
    (h : ∀ H : Matrix (Fin k) (Fin k) ℂ, H.IsHermitian → hermitianOperatorNorm H ≤ 1 →
      (Matrix.trace (H*X)).re ≤ matrixSupport K H + r) :
    X ∈ K + traceBall r := by
  by_contra hx
  have hc := hcK.add (traceBall_convex r)
  have hcomp := hK.add (traceBall_compact r)
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hc hcomp.isClosed hx
  obtain ⟨a, ha⟩ := hneK
  have hfa : f a < u := hfu a ⟨a, ha, 0, zero_mem_traceBall hr, add_zero a⟩
  let H := hermitianFunctionalMatrix f
  have hH : H.IsHermitian := hermitianFunctionalMatrix_isHermitian f
  have hHne : H ≠ 0 := by
    intro hz
    have hfx := hermitian_trace_representation f hX
    have hfax := hermitian_trace_representation f (hHK a ha)
    change (Matrix.trace (H*X)).re = f X at hfx
    change (Matrix.trace (H*a)).re = f a at hfax
    simp only [hz, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re] at hfx hfax
    linarith
  have hnorm : 0 < hermitianOperatorNorm H :=
    lt_of_le_of_ne (hermitianOperatorNorm_nonneg H) (fun he => hHne ((hermitianOperatorNorm_eq_zero H).mp he.symm))
  let G : Matrix (Fin k) (Fin k) ℂ := (hermitianOperatorNorm H)⁻¹ • H
  have hG : G.IsHermitian := hermitian_real_smul _ H hH
  have hnG : hermitianOperatorNorm G ≤ 1 := by
    change hermitianOperatorNorm ((hermitianOperatorNorm H)⁻¹ • H) ≤ 1
    rw [hermitianOperatorNorm_smul, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
  obtain ⟨b, hb, hbg⟩ := (matrixSupport_isGreatest K hK ⟨a,ha⟩ G).1
  have hh := h G hG hnG
  rw [← hbg] at hh
  change (Matrix.trace (G*X)).re ≤ (Matrix.trace (G*b)).re+r at hh
  simp only [G, real_trace_smul_left] at hh
  have hfx : (Matrix.trace (H*X)).re = f X := hermitian_trace_representation f hX
  have hfb : (Matrix.trace (H*b)).re = f b := hermitian_trace_representation f (hHK b hb)
  rw [hfx, hfb] at hh
  have hmul := mul_le_mul_of_nonneg_left hh hnorm.le
  have hbound : f X ≤ f b + r * hermitianOperatorNorm H := by
    field_simp at hmul
    nlinarith only [hmul]
  obtain ⟨M, hM, hval⟩ := traceBall_norming_witness H hH
  have hrM : r • M ∈ traceBall r := by
    refine ⟨hermitian_real_smul r M hM.1, ?_⟩
    exact (hermitianTraceNorm_smul_le r hr M hM.1).trans
      ((mul_le_mul_of_nonneg_left hM.2 hr).trans_eq (mul_one r))
  have hfM : f M = hermitianOperatorNorm H :=
    (hermitian_trace_representation f hM.1).symm.trans hval
  have hsep := hfu (b+r • M) ⟨b, hb, r • M, hrM, rfl⟩
  simp only [map_add, map_smul, smul_eq_mul, hfM] at hsep
  linarith

/-- Uniform operator-norm support errors bound the exact trace-norm
max-sup-inf Hausdorff distance. -/
theorem traceHausdorff_le_of_matrixSupport_le
    (C K : Set (Matrix (Fin k) (Fin k) ℂ)) (hC : IsCompact C) (hK : IsCompact K)
    (hneC : C.Nonempty) (hneK : K.Nonempty) (hcC : Convex ℝ C) (hcK : Convex ℝ K)
    (hHC : ∀ M ∈ C, M.IsHermitian) (hHK : ∀ M ∈ K, M.IsHermitian)
    {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ H : Matrix (Fin k) (Fin k) ℂ, H.IsHermitian → hermitianOperatorNorm H ≤ 1 →
      |matrixSupport C H - matrixSupport K H| ≤ r) :
    traceHausdorff C K ≤ r := by
  apply max_le
  · apply csSup_le (hneC.image _)
    rintro _ ⟨X, hX, rfl⟩
    have hm := mem_add_traceBall_of_support_le K hK hneK hcK hHK hr X (hHC X hX) (by
      intro H hH hn
      have hu := (abs_le.mp (h H hH hn)).2
      have hv := (matrixSupport_isGreatest C hC hneC H).2 ⟨X, hX, rfl⟩
      linarith)
    obtain ⟨Y, hY, M, hM, heq⟩ := hm
    have hl : BddBelow ((fun Y => hermitianTraceNorm (X-Y)) '' K) :=
      ⟨0, by rintro _ ⟨Y, _, rfl⟩; exact hermitianTraceNorm_nonneg _⟩
    apply (csInf_le hl ⟨Y, hY, rfl⟩).trans
    change hermitianTraceNorm (X-Y) ≤ r
    change Y+M=X at heq
    rw [← heq, add_sub_cancel_left]
    exact hM.2
  · apply csSup_le (hneK.image _)
    rintro _ ⟨Y, hY, rfl⟩
    have hm := mem_add_traceBall_of_support_le C hC hneC hcC hHC hr Y (hHK Y hY) (by
      intro H hH hn
      have hu := (abs_le.mp (h H hH hn)).1
      have hv := (matrixSupport_isGreatest K hK hneK H).2 ⟨Y, hY, rfl⟩
      linarith)
    obtain ⟨X, hX, M, hM, heq⟩ := hm
    have hl : BddBelow ((fun X => hermitianTraceNorm (X-Y)) '' C) :=
      ⟨0, by rintro _ ⟨X, _, rfl⟩; exact hermitianTraceNorm_nonneg _⟩
    apply (csInf_le hl ⟨X, hX, rfl⟩).trans
    change hermitianTraceNorm (X-Y) ≤ r
    change X+M=Y at heq
    rw [← heq, sub_add_cancel_left, hermitianTraceNorm_neg M hM.1]
    exact hM.2

lemma abs_matrixSupport_sub_le_traceHausdorff
    (C K : Set (Matrix (Fin k) (Fin k) ℂ)) (hC : IsCompact C) (hK : IsCompact K)
    (hneC : C.Nonempty) (hneK : K.Nonempty)
    (hHC : ∀ M ∈ C, M.IsHermitian) (hHK : ∀ M ∈ K, M.IsHermitian)
    (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.IsHermitian) (hn : hermitianOperatorNorm H ≤ 1) :
    |matrixSupport C H - matrixSupport K H| ≤ traceHausdorff C K := by
  have hb := trace_cost_directed_bddAbove C K hC hK hneC hneK
  have hpair (X : Matrix (Fin k) (Fin k) ℂ) (hX : X ∈ C)
      (Y : Matrix (Fin k) (Fin k) ℂ) (hY : Y ∈ K) :
      |(Matrix.trace (H*X)).re - (Matrix.trace (H*Y)).re| ≤ hermitianTraceNorm (X-Y) := by
    have hp := trace_pairing_abs_le_traceNorm_named (X-Y) H ((hHC X hX).sub (hHK Y hY)) hH
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hp
    exact hp.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hn (hermitianTraceNorm_nonneg (X-Y)))
  apply abs_le.mpr
  constructor
  · obtain ⟨Y, hY, hYval⟩ := (matrixSupport_isGreatest K hK hneK H).1
    have hl : matrixSupport K H - matrixSupport C H ≤
        sInf ((fun X => hermitianTraceNorm (X-Y)) '' C) := by
      apply le_csInf (hneC.image _)
      rintro _ ⟨X, hX, rfl⟩
      have hv := (matrixSupport_isGreatest C hC hneC H).2 ⟨X, hX, rfl⟩
      have hp := (abs_le.mp (hpair X hX Y hY)).1
      change (Matrix.trace (H*Y)).re = matrixSupport K H at hYval
      linarith
    have hu : matrixSupport K H - matrixSupport C H ≤ traceHausdorff C K :=
      hl.trans ((le_csSup hb.2 ⟨Y, hY, rfl⟩).trans (le_max_right _ _))
    linarith
  · obtain ⟨X, hX, hXval⟩ := (matrixSupport_isGreatest C hC hneC H).1
    have hl : matrixSupport C H - matrixSupport K H ≤
        sInf ((fun Y => hermitianTraceNorm (X-Y)) '' K) := by
      apply le_csInf (hneK.image _)
      rintro _ ⟨Y, hY, rfl⟩
      have hv := (matrixSupport_isGreatest K hK hneK H).2 ⟨Y, hY, rfl⟩
      have hp := (abs_le.mp (hpair X hX Y hY)).2
      change (Matrix.trace (H*X)).re = matrixSupport C H at hXval
      linarith
    exact hl.trans ((le_csSup hb.1 ⟨X, hX, rfl⟩).trans (le_max_left _ _))

/-- **Lemma III.3.** Exact trace/operator support-Hausdorff duality for
nonempty compact convex Hermitian matrix sets. -/
theorem traceHausdorff_eq_matrixSupportDistance
    (C K : Set (Matrix (Fin k) (Fin k) ℂ)) (hC : IsCompact C) (hK : IsCompact K)
    (hneC : C.Nonempty) (hneK : K.Nonempty) (hcC : Convex ℝ C) (hcK : Convex ℝ K)
    (hHC : ∀ M ∈ C, M.IsHermitian) (hHK : ∀ M ∈ K, M.IsHermitian) :
    traceHausdorff C K = sSup ((fun H : Matrix (Fin k) (Fin k) ℂ =>
      |matrixSupport C H - matrixSupport K H|) ''
        {H | H.IsHermitian ∧ hermitianOperatorNorm H ≤ 1}) := by
  let S := ((fun H : Matrix (Fin k) (Fin k) ℂ =>
      |matrixSupport C H - matrixSupport K H|) ''
        {H | H.IsHermitian ∧ hermitianOperatorNorm H ≤ 1})
  have hne : S.Nonempty := ⟨_, 0, ⟨Matrix.isHermitian_zero, by simp [hermitianOperatorNorm_zero]⟩, rfl⟩
  have hb : BddAbove S := ⟨traceHausdorff C K, by
    rintro _ ⟨H, ⟨hH, hn⟩, rfl⟩
    exact abs_matrixSupport_sub_le_traceHausdorff C K hC hK hneC hneK hHC hHK H hH hn⟩
  have hn : 0 ≤ sSup S := by
    obtain ⟨x, hx⟩ := hne
    have hx0 : 0 ≤ x := by obtain ⟨H, _, rfl⟩ := hx; exact abs_nonneg _
    exact hx0.trans (le_csSup hb hx)
  apply le_antisymm
  · apply traceHausdorff_le_of_matrixSupport_le C K hC hK hneC hneK hcC hcK hHC hHK hn
    intro H hH hnorm
    exact le_csSup hb ⟨H, ⟨hH, hnorm⟩, rfl⟩
  · apply csSup_le hne
    rintro _ ⟨H, ⟨hH, hnorm⟩, rfl⟩
    exact abs_matrixSupport_sub_le_traceHausdorff C K hC hK hneC hneK hHC hHK H hH hnorm

end
end RevisionOutput
