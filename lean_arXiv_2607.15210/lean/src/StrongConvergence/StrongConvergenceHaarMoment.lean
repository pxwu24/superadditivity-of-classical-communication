import HaarProjections.RevisionCanonicalEnsemble
import RandomCompression.ProjectionStrongConvergence
import HaarProjections.ProjectionOrbit
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The genuine first Haar moment of a block compression.  These are
finite-dimensional integral identities, with no asymptotic-freeness
assumption.  They alone do not imply higher moments or norm convergence. -/

open Matrix MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.HaarMoment

variable {E : Type*} [Fintype E] [DecidableEq E]

def orbit (P : Matrix E E ℂ) (U : Matrix.unitaryGroup E ℂ) : Matrix E E ℂ :=
  (U : Matrix E E ℂ) * P * (U : Matrix E E ℂ).conjTranspose

lemma continuous_orbit_diag (P : Matrix E E ℂ) (i : E) :
    Continuous (fun U : Matrix.unitaryGroup E ℂ => (orbit P U i i).re) :=
  Complex.continuous_re.comp ((HaarProjection.continuous_unitary_orbit P).matrix_elem i i)

lemma integrable_orbit_diag (P : Matrix E E ℂ) (i : E) :
    Integrable (fun U : Matrix.unitaryGroup E ℂ => (orbit P U i i).re)
      HaarProjection.unitaryHaar :=
  (continuous_orbit_diag P i).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integral_orbit_diag_eq (P : Matrix E E ℂ) (i j : E) :
    (∫ U : Matrix.unitaryGroup E ℂ, (orbit P U i i).re ∂HaarProjection.unitaryHaar) =
    ∫ U : Matrix.unitaryGroup E ℂ, (orbit P U j j).re ∂HaarProjection.unitaryHaar := by
  let e := Equiv.swap i j
  let V := star (ProjectionOrbit.permuteColumns (1 : Matrix.unitaryGroup E ℂ) e)
  have he (U : Matrix.unitaryGroup E ℂ) : orbit P (V*U) i i = orbit P U j j := by
    have h := ProjectionOrbit.permuteColumns_diagonalization
      (1 : Matrix.unitaryGroup E ℂ) e (orbit P U)
    have hi := congrFun (congrFun h i) i
    simpa [orbit, V, Matrix.UnitaryGroup.mul_val, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.mul_assoc, e] using hi
  have h := integral_mul_left_eq_self (μ := HaarProjection.unitaryHaar)
    (fun U : Matrix.unitaryGroup E ℂ => (orbit P U i i).re) V
  simpa only [he] using h.symm

theorem integral_orbit_diag [Nonempty E] (P : Matrix E E ℂ) (i : E) :
    (∫ U : Matrix.unitaryGroup E ℂ, (orbit P U i i).re ∂HaarProjection.unitaryHaar) =
      (Matrix.trace P).re / Fintype.card E := by
  have htrace (U : Matrix.unitaryGroup E ℂ) :
      ∑ j : E, (orbit P U j j).re = (Matrix.trace P).re := by
    rw [← Complex.re_sum]
    change (Matrix.trace (orbit P U)).re = _
    have hU : (U : Matrix E E ℂ).conjTranspose * (U : Matrix E E ℂ) = 1 := U.prop.1
    rw [orbit, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  have hsum := integral_finset_sum Finset.univ
    (fun j _ => integrable_orbit_diag P j)
  have hc : (Fintype.card E : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hc).mpr
  calc
    _ = ∑ j : E, ∫ U : Matrix.unitaryGroup E ℂ,
          (orbit P U j j).re ∂HaarProjection.unitaryHaar := by
      simp_rw [← integral_orbit_diag_eq P i]
      simp [mul_comm]
    _ = ∫ U : Matrix.unitaryGroup E ℂ, (∑ j : E, (orbit P U j j).re)
          ∂HaarProjection.unitaryHaar := hsum.symm
    _ = _ := by simp_rw [htrace]; simp

end ProjectionChannels.HaarMoment

namespace ProjectionChannels.Canonical

lemma continuous_projection_diag (k : ℕ) (t : ℝ) (n : ℕ) (i : Index k n) :
    Continuous (fun ω : Sample k => (projection k t ω n i i).re) :=
  (HaarMoment.continuous_orbit_diag (baseProjection k t n) i).comp (continuous_apply n)

lemma integrable_projection_diag (k : ℕ) (t : ℝ) (n : ℕ) (i : Index k n) :
    Integrable (fun ω : Sample k => (projection k t ω n i i).re) (probability k) :=
  (continuous_projection_diag k t n i).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_projection_diag {k : ℕ} {t : ℝ} (hk : 0<k)
    (ht0 : 0≤t) (ht1 : t≤1) (n : ℕ) (i : Index k n) :
    (∫ ω, (projection k t ω n i i).re ∂probability k) =
      (rankSequence k t n : ℝ) / ((k:ℝ)*(n+1)) := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let f : Matrix.unitaryGroup (Index k n) ℂ → ℝ :=
    fun U => (HaarMoment.orbit (baseProjection k t n) U i i).re
  have hmp := evaluation_measurePreserving k n
  have hmap := integral_map (μ := probability k) hmp.measurable.aemeasurable
    (f := f) (HaarMoment.continuous_orbit_diag (baseProjection k t n) i).aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  change (∫ ω, f (evaluation k n ω) ∂probability k) = _
  rw [← hmap, HaarMoment.integral_orbit_diag]
  rw [ProjectionStrongConvergence.trace_projection_eq_rank _ (baseProjection_idempotent k t n),
    baseProjection_rank ht0 ht1]
  simp [Index,Fintype.card_prod]
  congr 1
  ring

theorem integral_compression_trace {k : ℕ} {t : ℝ} (hk : 0<k)
    (ht0 : 0≤t) (ht1 : t≤1) (n : ℕ) (a : Fin k → ℝ) :
    (∫ ω, (Matrix.trace (blockCompression (diagonalBlock (projection k t ω n)) a)).re
      ∂probability k) = (rankSequence k t n : ℝ) / k * ∑ i, a i := by
  have hform (ω : Sample k) :
      (Matrix.trace (blockCompression (diagonalBlock (projection k t ω n)) a)).re =
      ∑ u : Fin (n+1), ∑ i : Fin k, a i * (projection k t ω n (u,i) (u,i)).re := by
    simp [Matrix.trace,blockCompression,diagonalBlock,Matrix.sum_apply,Matrix.smul_apply,
      smul_eq_mul,Complex.re_sum,Complex.mul_re]
  simp_rw [hform]
  rw [integral_finset_sum]
  · simp_rw [integral_finset_sum _ (fun i _ =>
      (integrable_projection_diag k t n (_,i)).const_mul (a i))]
    simp_rw [integral_const_mul, integral_projection_diag hk ht0 ht1]
    have hk' : (k:ℝ) ≠ 0 := by positivity
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← Finset.sum_mul,Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  · intro u _
    exact integrable_finset_sum _ (fun i _ =>
      (integrable_projection_diag k t n (u,i)).const_mul (a i))

theorem normalized_first_moment_tendsto {k : ℕ} {t : ℝ} (hk : 0<k)
    (ht0 : 0≤t) (ht1 : t≤1) (a : Fin k → ℝ) :
    Tendsto (fun n => (∫ ω,
      (Matrix.trace (blockCompression (diagonalBlock (projection k t ω n)) a)).re
        ∂probability k) / (n+1)) atTop (𝓝 (t * ∑ i, a i)) := by
  simp_rw [integral_compression_trace hk ht0 ht1]
  have h := (rank_density_tendsto hk ht0).mul_const (∑ i, a i)
  convert h using 1
  ext n
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.HaarMoment.integral_orbit_diag
#print axioms ProjectionChannels.Canonical.integral_compression_trace
#print axioms ProjectionChannels.Canonical.normalized_first_moment_tendsto
