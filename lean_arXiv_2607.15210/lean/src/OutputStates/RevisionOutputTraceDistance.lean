import OutputStates.RevisionOutputLimit

/-!
# Trace-norm Hausdorff convergence

For Hermitian matrices the trace norm is the sum of absolute eigenvalues.
We use exactly that definition for Hermitian differences. Values on
non-Hermitian differences are immaterial to the final theorem, whose sets
consist entirely of density matrices. The comparison with the elementwise
supremum norm is proved explicitly, so no norm-equivalence axiom is assumed.
-/

open Filter Matrix Set Metric PreliminariesMatrix ProjectionChannels OutputSpaceVerification
open scoped Topology BigOperators ComplexOrder
namespace RevisionOutput
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

lemma abs_eigenvalue_le_card_sq_norm (M : Matrix A A ℂ) (hM : M.IsHermitian) (l : A) :
    |hM.eigenvalues l| ≤ (Fintype.card A : ℝ)^2 * ‖M‖ := by
  rw [hM.eigenvalues_eq l]
  apply (Complex.abs_re_le_norm _).trans
  unfold dotProduct Matrix.mulVec
  apply (norm_sum_le _ _).trans
  calc
    ∑ i, ‖star (⇑(hM.eigenvectorBasis l) i) * ∑ j, M i j * ⇑(hM.eigenvectorBasis l) j‖
      ≤ ∑ i : A, ∑ j : A, ‖M‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_star]
      have hi : ‖⇑(hM.eigenvectorBasis l) i‖ ≤ 1 := by
        simpa only [Matrix.IsHermitian.eigenvectorUnitary_apply] using
          HaarProjection.unitary_entry_norm_le_one hM.eigenvectorUnitary i l
      calc
        _ ≤ 1 * ∑ j : A, ‖M i j * ⇑(hM.eigenvectorBasis l) j‖ := by
          exact mul_le_mul hi (norm_sum_le _ _) (norm_nonneg _) (by norm_num)
        _ ≤ 1 * ∑ _j : A, ‖M‖ := by
          gcongr with j
          rw [norm_mul]
          have hj : ‖⇑(hM.eigenvectorBasis l) j‖ ≤ 1 := by
            simpa only [Matrix.IsHermitian.eigenvectorUnitary_apply] using
              HaarProjection.unitary_entry_norm_le_one hM.eigenvectorUnitary j l
          have hm : ‖M i j‖ ≤ ‖M‖ := (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)
          calc
            _ ≤ ‖M‖ * 1 := mul_le_mul hm hj (norm_nonneg _) (norm_nonneg _)
            _ = _ := mul_one _
        _ = _ := one_mul _
    _ = (Fintype.card A : ℝ)^2 * ‖M‖ := by simp; ring

/-- The trace norm of a Hermitian matrix, and zero outside the Hermitian
subspace. Only its Hermitian restriction is used for output state distances. -/
def hermitianTraceNorm (M : Matrix A A ℂ) : ℝ :=
  if hM : M.IsHermitian then ∑ i, |hM.eigenvalues i| else 0

lemma hermitianTraceNorm_eq (M : Matrix A A ℂ) (hM : M.IsHermitian) :
    hermitianTraceNorm M = ∑ i, |hM.eigenvalues i| := by
  simp only [hermitianTraceNorm, dif_pos hM]

lemma hermitianTraceNorm_nonneg (M : Matrix A A ℂ) : 0 ≤ hermitianTraceNorm M := by
  unfold hermitianTraceNorm
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · exact le_rfl

lemma hermitianTraceNorm_le (M : Matrix A A ℂ) :
    hermitianTraceNorm M ≤ (Fintype.card A : ℝ)^3 * ‖M‖ := by
  unfold hermitianTraceNorm
  split_ifs with hM
  · calc
      ∑ i, |hM.eigenvalues i| ≤ ∑ _i : A, (Fintype.card A : ℝ)^2 * ‖M‖ :=
        Finset.sum_le_sum fun i _ => abs_eigenvalue_le_card_sq_norm M hM i
      _ = _ := by simp; ring
  · positivity

/-- The max–sup–inf distance used in Eq. (24), for a given nonnegative cost. -/
def costHausdorff {E : Type*} (cost : E → E → ℝ) (C K : Set E) : ℝ :=
  max (sSup ((fun x => sInf (cost x '' K)) '' C))
    (sSup ((fun y => sInf ((fun x => cost x y) '' C)) '' K))

section CostBound
variable {E : Type*} [PseudoMetricSpace E]

lemma costHausdorff_nonneg (cost : E → E → ℝ) (C K : Set E)
    (hneC : C.Nonempty) (hneK : K.Nonempty)
    (hcost : ∀ x y, 0 ≤ cost x y)
    (hbdd : BddAbove ((fun x => sInf (cost x '' K)) '' C)) :
    0 ≤ costHausdorff cost C K := by
  obtain ⟨x, hx⟩ := hneC
  have hnon : 0 ≤ sInf (cost x '' K) := by
    apply le_csInf (hneK.image _)
    rintro _ ⟨y, _, rfl⟩
    exact hcost x y
  exact hnon.trans ((le_csSup hbdd ⟨x, hx, rfl⟩).trans (le_max_left _ _))

lemma costHausdorff_le_mul_hausdorffDist (cost : E → E → ℝ) (C K : Set E)
    (hC : IsCompact C) (hK : IsCompact K) (hneC : C.Nonempty) (hneK : K.Nonempty)
    {L : ℝ} (hL : 0 ≤ L) (hcost : ∀ x y, 0 ≤ cost x y)
    (hbound : ∀ x y, cost x y ≤ L * dist x y) :
    0 ≤ costHausdorff cost C K ∧ costHausdorff cost C K ≤ L * hausdorffDist C K := by
  have hfin := hausdorffEdist_ne_top_of_nonempty_of_bounded hneC hneK hC.isBounded hK.isBounded
  have hdir : ∀ x ∈ C, sInf (cost x '' K) ≤ L * hausdorffDist C K := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hK.exists_infDist_eq_dist hneK x
    have hd := infDist_le_hausdorffDist_of_mem hx hfin
    rw [hxy] at hd
    have hlow : BddBelow (cost x '' K) := ⟨0, by rintro _ ⟨y, _, rfl⟩; exact hcost x y⟩
    exact (csInf_le hlow ⟨y, hy, rfl⟩).trans
      ((hbound x y).trans (mul_le_mul_of_nonneg_left hd hL))
  have hrev : ∀ y ∈ K, sInf ((fun x => cost x y) '' C) ≤ L * hausdorffDist C K := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hC.exists_infDist_eq_dist hneC y
    have hfin' : EMetric.hausdorffEdist K C ≠ ⊤ := by
      rw [EMetric.hausdorffEdist_comm]
      exact hfin
    have hd := infDist_le_hausdorffDist_of_mem hy hfin'
    rw [hxy, hausdorffDist_comm, dist_comm y x] at hd
    have hlow : BddBelow ((fun x => cost x y) '' C) := ⟨0, by rintro _ ⟨x, _, rfl⟩; exact hcost x y⟩
    exact (csInf_le hlow ⟨x, hx, rfl⟩).trans
      ((hbound x y).trans (mul_le_mul_of_nonneg_left hd hL))
  have hbd : BddAbove ((fun x => sInf (cost x '' K)) '' C) :=
    ⟨L * hausdorffDist C K, by rintro _ ⟨x, hx, rfl⟩; exact hdir x hx⟩
  refine ⟨costHausdorff_nonneg cost C K hneC hneK hcost hbd, ?_⟩
  apply max_le
  · exact csSup_le (hneC.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hdir x hx)
  · exact csSup_le (hneK.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hrev y hy)

end CostBound

/-- Trace-norm Hausdorff distance on sets of Hermitian matrices, using
exactly the paper's max–sup–inf formula. -/
def traceHausdorff (C K : Set (Matrix A A ℂ)) : ℝ :=
  costHausdorff (fun X Y => hermitianTraceNorm (X-Y)) C K

lemma traceHausdorff_comparison (C K : Set (Matrix A A ℂ))
    (hC : IsCompact C) (hK : IsCompact K) (hneC : C.Nonempty) (hneK : K.Nonempty) :
    0 ≤ traceHausdorff C K ∧
      traceHausdorff C K ≤ (Fintype.card A : ℝ)^3 * hausdorffDist C K := by
  apply costHausdorff_le_mul_hausdorffDist _ C K hC hK hneC hneK (by positivity)
  · intro X Y; exact hermitianTraceNorm_nonneg _
  · intro X Y
    simpa only [dist_eq_norm] using hermitianTraceNorm_le (X-Y)

/-- Trace-norm form of the deterministic output-space limit. Both sets
are actual density-matrix sets and the cost is the genuine Hermitian
trace norm. The compression input is unnormalized. -/
theorem actual_output_traceHausdorff_from_compression
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hP : ∀ N, (P N).PosSemidef) (hA : ∀ N, (traceB (P N)).PosDef)
    (hconv : ∀ (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.IsHermitian) (z : ℝ),
      Tendsto (fun N => largestEigenvalue
        (contraction_isHermitian (hP N).isHermitian
          (real_scalar_shift_hermitian hH Matrix.isHermitian_one z)))
        atTop (𝓝 (bodySupport k t (fun i => hH.eigenvalues i - z)))) :
    Tendsto (fun N => traceHausdorff
      (normalizedOutput (P N) (hA N).posSemidef.sqrt⁻¹ '' densityMatrices (Fin (N+1)))
      (spectralBody k t)) atTop (𝓝 0) := by
  have hh := actual_output_hausdorff_from_compression hk ht ht1 hkt P hP hA hconv
  have hb := fun N => traceHausdorff_comparison
    (normalizedOutput (P N) (hA N).posSemidef.sqrt⁻¹ '' densityMatrices (Fin (N+1)))
    (spectralBody k t)
    (output_image_nonempty_compact _ _).2 (isCompact_spectralBody hk ht.le hkt)
    (output_image_nonempty_compact _ _).1 (spectralBody_nonempty hk ht.le ht1.le)
  apply squeeze_zero (fun N => (hb N).1) (fun N => (hb N).2)
  simpa only [mul_zero] using hh.const_mul ((Fintype.card (Fin k) : ℝ)^3)

end
end RevisionOutput
