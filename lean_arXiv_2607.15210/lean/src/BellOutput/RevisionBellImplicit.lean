import BellOutput.RevisionBellHessian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open Filter Finset
open scoped Topology BigOperators
noncomputable section
namespace RevisionBell
open ProjectionChannels

/-- A two-variable implicit-function theorem specialized to a nonzero derivative
in the second variable and a vanishing derivative in the first variable. -/
theorem exists_contDiff_root
    (F : ℝ × ℝ → ℝ) (w0 c : ℝ) (hc : c ≠ 0)
    (h0 : F (0,w0)=0) (hF : ContDiffAt ℝ 2 F (0,w0))
    (hd : HasFDerivAt F (c • ContinuousLinearMap.snd ℝ ℝ ℝ) (0,w0)) :
    ∃ w : ℝ → ℝ, w 0 = w0 ∧ ContDiffAt ℝ 2 w 0 ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ), F (ε,w ε)=0 := by
  let L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    { toLinearEquiv :=
        { toFun := fun p => (p.1,c*p.2)
          invFun := fun p => (p.1,p.2/c)
          left_inv := by intro p; ext <;> simp [hc]
          right_inv := by intro p; ext <;> simp [hc, mul_div_cancel₀]
          map_add' := by intro p q; ext <;> simp [mul_add]
          map_smul' := by intro a p; ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let T : ℝ × ℝ → ℝ × ℝ := fun p => (p.1,F p)
  have ht : ContDiffAt ℝ 2 T (0,w0) := contDiffAt_fst.prodMk hF
  have htd : HasFDerivAt T (L : (ℝ×ℝ) →L[ℝ] (ℝ×ℝ)) (0,w0) := by
    convert (hasFDerivAt_fst : HasFDerivAt (fun p : ℝ×ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (0,w0)).prodMk hd using 1
  have ht0 : T (0,w0) = (0,0) := by simp [T,h0]
  let G := ht.localInverse htd (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hG : ContDiffAt ℝ 2 G (0,0) := by
    simpa only [ht0] using ht.to_localInverse htd (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hG0 : G (0,0)=(0,w0) := by
    simpa only [ht0] using ht.localInverse_apply_image htd (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hright : ∀ᶠ p in 𝓝 (0,0), T (G p)=p := by
    simpa only [ht0] using (ht.hasStrictFDerivAt' htd (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).eventually_right_inverse
  let w : ℝ → ℝ := fun ε => (G (ε,0)).2
  refine ⟨w, ?_, ?_, ?_⟩
  · change (G (0,0)).2 = w0
    rw [hG0]
  · have hp : ContDiffAt ℝ 2 (fun ε : ℝ => (ε,(0 : ℝ))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    exact (ContDiffAt.comp (f := fun ε : ℝ => (ε,(0 : ℝ))) (g := G) 0 hG hp).snd
  · have hlim : Tendsto (fun ε : ℝ => (ε,(0 : ℝ))) (𝓝 0) (𝓝 (0,0)) :=
      continuousAt_id.tendsto.prodMk_nhds tendsto_const_nhds
    filter_upwards [hlim.eventually hright] with ε hε
    have hfst : (G (ε,0)).1=ε := congrArg Prod.fst hε
    have hsnd : F (G (ε,0))=0 := congrArg Prod.snd hε
    change F (ε,(G (ε,0)).2)=0
    have heq : (ε,(G (ε,0)).2) = G (ε,0) := by
      ext <;> simp [hfst]
    rw [heq]
    exact hsnd


lemma contDiff_rootEquation {k : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h : Fin k → ℝ) : ContDiff ℝ 2 (fun p : ℝ×ℝ => rootEquation k t h p.1 p.2) := by
  unfold rootEquation
  apply ContDiff.add contDiff_const
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro i _
  apply (contDiff_bernoulliDual ht0 ht1 2).comp
  simp only [div_eq_mul_inv]
  fun_prop

lemma hasFDerivAt_rootEquation_traceless {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : Fin k → ℝ) (hh : ∑ i, h i = 0) (w0 : ℝ) :
    HasFDerivAt (fun p : ℝ×ℝ => rootEquation k t h p.1 p.2)
      (((k : ℝ)*bernoulliMaximizer t (w0/k)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (0,w0) := by
  let F := ContinuousLinearMap.fst ℝ ℝ ℝ
  let S := ContinuousLinearMap.snd ℝ ℝ ℝ
  let d : Fin k → ((ℝ×ℝ) →L[ℝ] ℝ) := fun i =>
    ((w0*h i/(k : ℝ)) • F + (1/(k : ℝ)) • S)
  have hargs (i : Fin k) : HasFDerivAt
      (fun p : ℝ×ℝ => (1+p.1*h i)*p.2/(k : ℝ)) (d i) (0,w0) := by
    have hp : HasFDerivAt (fun p : ℝ×ℝ => p.1) F (0,w0) := hasFDerivAt_fst
    have hq : HasFDerivAt (fun p : ℝ×ℝ => p.2) S (0,w0) := hasFDerivAt_snd
    simp only [div_eq_mul_inv]
    apply ((((hp.mul_const (h i)).const_add 1).mul hq).mul_const (k : ℝ)⁻¹).congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    simp [d,F,S, div_eq_mul_inv]
    ring
  have hi (i : Fin k) : HasFDerivAt
      (fun p : ℝ×ℝ => bernoulliDual t ((1+p.1*h i)*p.2/k))
      (bernoulliMaximizer t (w0/k) • d i) (0,w0) := by
    simpa only [zero_mul, add_zero, one_mul] using
      (hasDerivAt_bernoulliDual ht0 ht1 ((1+0*h i)*w0/k)).comp_hasFDerivAt (0,w0) (hargs i)
  have hs := ((HasFDerivAt.sum (u := Finset.univ) (fun i _ => hi i)).const_mul (k : ℝ)).const_add 1
  unfold rootEquation
  apply hs.congr_fderiv
  symm
  apply ContinuousLinearMap.ext
  intro p
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, d]
  change ((k : ℝ)*bernoulliMaximizer t (w0/k))*p.2 =
    (k : ℝ)*∑ i, bernoulliMaximizer t (w0/k)*
      ((w0*h i/k)*p.1+(1/k)*p.2)
  have heach (i : Fin k) : bernoulliMaximizer t (w0/k)*
      ((w0*h i/k)*p.1+(1/k)*p.2) =
      (bernoulliMaximizer t (w0/k)*w0*p.1/k)*h i +
        bernoulliMaximizer t (w0/k)*p.2/k := by ring
  simp_rw [heach, sum_add_distrib, ← mul_sum, hh, mul_zero,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, zero_add]
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  field_simp
  <;> ring

/-- The actual scalar equation has a C² root curve near a traceless
perturbation. Smoothness is derived by the inverse function theorem. -/
theorem exists_smooth_bernoulli_root {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : Fin k → ℝ) (hh : ∑ i, h i = 0)
    (w0 : ℝ) (hroot : rootEquation k t h 0 w0 = 0) :
    ∃ w : ℝ → ℝ, w 0=w0 ∧ ContDiffAt ℝ 2 w 0 ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ), rootEquation k t h ε (w ε)=0 := by
  have hu := (bernoulliMaximizer_mem_Ioo ht0 ht1 (w0/(k : ℝ))).1
  exact exists_contDiff_root (fun p : ℝ×ℝ => rootEquation k t h p.1 p.2) w0
    ((k : ℝ)*bernoulliMaximizer t (w0/k))
    (ne_of_gt (mul_pos (Nat.cast_pos.mpr hk) hu)) hroot
    (contDiff_rootEquation ht0 ht1 h).contDiffAt
    (hasFDerivAt_rootEquation_traceless hk ht0 ht1 h hh w0)

end RevisionBell
