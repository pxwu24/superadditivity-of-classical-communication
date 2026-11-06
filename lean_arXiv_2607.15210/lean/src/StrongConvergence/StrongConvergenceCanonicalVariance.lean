import StrongConvergence.StrongConvergenceHaarVarianceResult

/-! Summable variance bound for the actual canonical Haar-compression trace. -/
open Matrix MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.Canonical

def normalizedCompressionTrace (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (ω : Sample k) (n : ℕ) : ℝ :=
  (Matrix.trace (blockCompression (diagonalBlock (projection k t ω n)) a)).re / (n+1)

def compressionTraceCenter (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ) : ℝ :=
  (rankSequence k t n : ℝ) / ((k:ℝ)*(n+1)) * ∑ i, a i

lemma compression_trace_sum (k : ℕ) (t : ℝ) (a : Fin k → ℝ)
    (ω : Sample k) (n : ℕ) :
    (Matrix.trace (blockCompression (diagonalBlock (projection k t ω n)) a)).re =
      ∑ u : Fin (n+1), ∑ i : Fin k, a i * (projection k t ω n (u,i) (u,i)).re := by
  simp [Matrix.trace,blockCompression,diagonalBlock,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,Complex.re_sum,Complex.mul_re]

lemma continuous_normalizedCompressionTrace (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (n : ℕ) :
    Continuous (fun ω => normalizedCompressionTrace k t a ω n) := by
  simp_rw [normalizedCompressionTrace,compression_trace_sum]
  exact (continuous_finset_sum _ (fun u _ => continuous_finset_sum _ (fun i _ =>
    continuous_const.mul (continuous_projection_diag k t n (u,i))))).div_const _

lemma integrable_normalizedCompressionTrace_square (k : ℕ) (t : ℝ)
    (a : Fin k → ℝ) (n : ℕ) :
    Integrable (fun ω =>
      (normalizedCompressionTrace k t a ω n-compressionTraceCenter k t a n)^2)
      (probability k) :=
  (((continuous_normalizedCompressionTrace k t a n).sub continuous_const).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem normalizedCompressionTrace_variance_le {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0≤t) (ht1 : t≤1) (a : Fin k → ℝ)
    (n : ℕ) (hn : 1≤n) :
    (∫ ω,
      (normalizedCompressionTrace k t a ω n-compressionTraceCenter k t a n)^2
      ∂probability k) ≤ ((∑ i, (a i)^2) / k) / (n+1)^2 := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let P := baseProjection k t n
  let w : Index k n → ℝ := fun l => a l.2 / (n+1)
  have hn0 : (n:ℝ)+1≠0 := by positivity
  have hk0 : (k:ℝ)≠0 := by positivity
  have hcard : (Fintype.card (Index k n):ℝ) = (k:ℝ)*(n+1) := by
    simp [Index,Fintype.card_prod]; ring
  have hN : 1<Fintype.card (Index k n) := by
    simp only [Index,Fintype.card_prod,Fintype.card_fin]
    nlinarith
  have htr : (Matrix.trace P).re = rankSequence k t n := by
    rw [ProjectionStrongConvergence.trace_projection_eq_rank _ (baseProjection_idempotent k t n),
      baseProjection_rank ht0 ht1]
    simp
  have hw : ∑ l : Index k n, w l = ∑ i : Fin k, a i := by
    simp [w,Index,Fintype.sum_prod_type,← Finset.sum_div]
    field_simp
  have hw2 : ∑ l : Index k n, (w l)^2 = (∑ i : Fin k, (a i)^2)/(n+1) := by
    simp [w,Index,Fintype.sum_prod_type,div_pow,← Finset.sum_div]
    field_simp
    ring
  let f : Matrix.unitaryGroup (Index k n) ℂ → ℝ := fun U =>
    (∑ l, w l * ((HaarMoment.orbit P U l l).re-(Matrix.trace P).re/Fintype.card (Index k n)))^2
  have hcont : Continuous f := HaarMoment.continuous_weighted_diagonal_square P w
  have heval (ω : Sample k) :
      (normalizedCompressionTrace k t a ω n-compressionTraceCenter k t a n)^2 =
        f (evaluation k n ω) := by
    dsimp [f]
    rw [HaarMoment.weighted_diagonal_centering,htr,hcard,hw]
    congr 1
    simp only [normalizedCompressionTrace,compressionTraceCenter,compression_trace_sum,
      Index,Fintype.sum_prod_type,w]
    have hsum : (∑ u : Fin (n+1), ∑ i : Fin k,
        a i*(projection k t ω n (u,i) (u,i)).re)/(n+1) =
      ∑ u : Fin (n+1), ∑ i : Fin k,
        a i/(n+1)*(HaarMoment.orbit P (evaluation k n ω) (u,i) (u,i)).re := by
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro i _
      change a i*(projection k t ω n (u,i) (u,i)).re/(n+1) =
        a i/(n+1)*(projection k t ω n (u,i) (u,i)).re
      ring
    rw [hsum]
  have hmp := evaluation_measurePreserving k n
  have hmap := integral_map (μ := probability k) hmp.measurable.aemeasurable
    (f := f) hcont.aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  simp_rw [heval]
  rw [← hmap]
  have hbound := HaarMoment.weighted_diagonal_variance_le
    (baseProjection_isHermitian k t n) (baseProjection_idempotent k t n) hN w
  change (∫ U, f U ∂HaarProjection.unitaryHaar) ≤ _ at hbound
  apply hbound.trans_eq
  rw [hw2,hcard]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,one_mul,pow_two]
  ring

theorem compressionTraceCenter_tendsto {k : ℕ} {t : ℝ}
    (hk : 0<k) (ht0 : 0≤t) (a : Fin k → ℝ) :
    Tendsto (compressionTraceCenter k t a) atTop (𝓝 (t*∑ i, a i)) :=
  (rank_density_tendsto hk ht0).mul_const _

#print axioms normalizedCompressionTrace_variance_le
end ProjectionChannels.Canonical
