import OutputStates.RevisionOutputChannel
import Entropy.Minimum
import Entropy.OutputSpaceBody
import RandomCompression.BernoulliCalculus
import HaarProjections.HaarMeasure
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Matrix.DoublyStochastic

open scoped BigOperators ComplexOrder
open Matrix Finset Set
open AppendixB OutputSpaceVerification ProjectionChannels
namespace RevisionOutput
noncomputable section

/-- The manuscript's unitarily invariant output body, with actual matrices. -/
def spectralBody (k : ℕ) (t : ℝ) : Set (Matrix (Fin k) (Fin k) ℂ) :=
  {X | ∃ lam ∈ Lam k t, ∃ U : Matrix.unitaryGroup (Fin k) ℂ,
    X = (U : Matrix (Fin k) (Fin k) ℂ) * Matrix.diagonal (fun i => (lam i : ℂ)) *
      (U : Matrix (Fin k) (Fin k) ℂ).conjTranspose}

lemma convex_Dset {k : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Convex ℝ (Dset k t) := by
  intro u hu v hv a b ha hb hab
  have hf := (strictConvexOn_bernoulliCost ht0 ht1).convexOn
  refine ⟨?_, ?_⟩
  · intro i
    exact (convex_Icc (0 : ℝ) 1) (hu.1 i) (hv.1 i) ha hb hab
  · have heach (i : Fin k) : ct t (a*u i+b*v i) ≤ a*ct t (u i)+b*ct t (v i) :=
      hf.2 (hu.1 i) (hv.1 i) ha hb hab
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
    simp only [sum_add_distrib, ← mul_sum] at hs
    have hu' := mul_le_mul_of_nonneg_left hu.2 ha
    have hv' := mul_le_mul_of_nonneg_left hv.2 hb
    change (∑ i, ct t (a*u i+b*v i)) ≤ _
    apply hs.trans ((add_le_add hu' hv').trans_eq ?_)
    rw [← add_mul, hab, one_mul]

lemma convex_Lam {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t) :
    Convex ℝ (Lam k t) := by
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩ a b ha hb hab
  let su := ∑ i, u i
  let sv := ∑ i, v i
  have hsu : 0 < su := body_mass_pos hk ht0.le hkt u hu
  have hsv : 0 < sv := body_mass_pos hk ht0.le hkt v hv
  let den := a*sv+b*su
  have hd : 0 < den := by
    have ha' : 0 ≤ a*sv := mul_nonneg ha hsv.le
    have hb' : 0 ≤ b*su := mul_nonneg hb hsu.le
    by_contra h
    have heq : a*sv+b*su = 0 := le_antisymm (le_of_not_gt h) (add_nonneg ha' hb')
    have haz : a=0 := (mul_eq_zero.mp (by linarith : a*sv=0)).resolve_right hsv.ne'
    have hbz : b=0 := (mul_eq_zero.mp (by linarith : b*su=0)).resolve_right hsu.ne'
    linarith
  let A := a*sv/den
  let B := b*su/den
  have hA : 0 ≤ A := div_nonneg (mul_nonneg ha hsv.le) hd.le
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hb hsu.le) hd.le
  have hAB : A+B=1 := by dsimp [A,B,den]; rw [← add_div]; exact div_self hd.ne'
  let w : Fin k → ℝ := A • u + B • v
  have hw : w ∈ Dset k t := convex_Dset ht0 ht1 hu hv hA hB hAB
  have hmass : (∑ i, w i) = su*sv/den := by
    simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
    change A*su+B*sv = _
    dsimp [A,B]
    field_simp
    rw [show a*sv*su+b*su*sv=(a+b)*su*sv by ring, hab]
    ring
  refine ⟨w, hw, ?_⟩
  ext i
  change a*(u i/su)+b*(v i/sv) = w i / ∑ j, w j
  rw [hmass]
  dsimp [w,A,B]
  field_simp
  <;> ring

/-- Doubly stochastic averaging preserves the unnormalized feasible body. -/
lemma doublyStochastic_mem_Dset {k : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {M : Matrix (Fin k) (Fin k) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin k)) {u : Fin k → ℝ} (hu : u ∈ Dset k t) :
    M *ᵥ u ∈ Dset k t := by
  have hf := (strictConvexOn_bernoulliCost ht0 ht1).convexOn
  have hm := (mem_doublyStochastic_iff_sum.mp hM)
  refine ⟨?_, ?_⟩
  · intro i
    have hnonneg : 0 ≤ ∑ j, M i j*u j :=
      sum_nonneg fun j _ => mul_nonneg (hm.1 i j) (hu.1 j).1
    have hle : (∑ j, M i j*u j) ≤ 1 := by
      calc
        _ ≤ ∑ j, M i j*1 := sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hu.1 j).2 (hm.1 i j)
        _ = 1 := by simp [hm.2.1 i]
    exact ⟨hnonneg, hle⟩
  · have heach (i : Fin k) : ct t ((M*ᵥu) i) ≤ ∑ j, M i j*ct t (u j) := by
      simpa only [Matrix.mulVec, dotProduct, smul_eq_mul] using
        hf.map_sum_le (t := Finset.univ) (fun j _ => hm.1 i j)
          (hm.2.1 i) (fun j _ => hu.1 j)
    calc
      _ ≤ ∑ i, ∑ j, M i j*ct t (u j) := sum_le_sum fun i _ => heach i
      _ = ∑ j, ct t (u j) := by
        rw [sum_comm]
        simp_rw [← sum_mul, hm.2.2, one_mul]
      _ ≤ _ := hu.2

/-- Doubly stochastic averaging preserves normalization because it preserves mass. -/
lemma doublyStochastic_mem_Lam {k : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {M : Matrix (Fin k) (Fin k) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin k)) {lam : Fin k → ℝ} (hlam : lam ∈ Lam k t) :
    M *ᵥ lam ∈ Lam k t := by
  obtain ⟨u, hu, rfl⟩ := hlam
  refine ⟨M*ᵥu, doublyStochastic_mem_Dset ht0 ht1 hM hu, ?_⟩
  have hmass : (∑ i, (M*ᵥu) i) = ∑ i, u i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_comm]
    simp_rw [← sum_mul, sum_col_of_mem_doublyStochastic hM, one_mul]
  ext i
  rw [hmass]
  simp only [Matrix.mulVec, dotProduct, mul_div_assoc, sum_div]

/-- Compactness of the actual matrix body follows from compactness of Lambda
and the compact unitary group. -/
theorem isCompact_spectralBody {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht0 : 0 ≤ t) (hkt : 1 < (k : ℝ)^2*t) : IsCompact (spectralBody k t) := by
  let f : (Fin k → ℝ) × Matrix.unitaryGroup (Fin k) ℂ → Matrix (Fin k) (Fin k) ℂ :=
    fun p => (p.2 : Matrix (Fin k) (Fin k) ℂ) * diagonal (fun i => (p.1 i : ℂ)) *
      (p.2 : Matrix (Fin k) (Fin k) ℂ).conjTranspose
  have hf : Continuous f := by
    apply Continuous.matrix_mul
    · apply Continuous.matrix_mul
      · exact continuous_subtype_val.comp continuous_snd
      · apply continuous_matrix
        intro i j
        by_cases h : i=j
        · subst j; simpa using (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst))
        · simpa [diagonal_apply_ne _ h] using (continuous_const : Continuous (fun _ : (Fin k → ℝ) × Matrix.unitaryGroup (Fin k) ℂ => (0 : ℂ)))
    · exact (continuous_subtype_val.comp continuous_snd).matrix_conjTranspose
  have heq : spectralBody k t = f '' (Lam k t ×ˢ Set.univ) := by
    ext X
    simp only [spectralBody, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_univ, and_true,
      Prod.exists]
    constructor
    · rintro ⟨lam, hlam, U, rfl⟩; exact ⟨lam,U,hlam,rfl⟩
    · rintro ⟨lam,U,hlam,rfl⟩; exact ⟨lam,hlam,U,rfl⟩
  rw [heq]
  exact ((isCompact_Lam hk ht0 hkt).prod isCompact_univ).image hf


/-- Squared entries of a unitary form a doubly stochastic matrix. -/
def unitaryWeights {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℂ) :
    Matrix (Fin k) (Fin k) ℝ := fun i j => Complex.normSq (U i j)

lemma unitaryWeights_doublyStochastic {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℂ) :
    unitaryWeights U ∈ doublyStochastic ℝ (Fin k) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, ?_, ?_⟩
  · intro i
    have h := congrFun (congrFun U.prop.2 i) i
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq, Complex.star_def, Complex.mul_conj] at h
    exact_mod_cast h
  · exact HaarProjection.unitary_column_normSq_sum U

def unitaryConjugate {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℂ)
    (X : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  (U : Matrix (Fin k) (Fin k) ℂ) * X * (U : Matrix (Fin k) (Fin k) ℂ).conjTranspose

lemma unitaryConjugate_comp {k : ℕ} (U V : Matrix.unitaryGroup (Fin k) ℂ)
    (X : Matrix (Fin k) (Fin k) ℂ) :
    unitaryConjugate U (unitaryConjugate V X) = unitaryConjugate (U*V) X := by
  simp only [unitaryConjugate, Submonoid.coe_mul, conjTranspose_mul, Matrix.mul_assoc]

lemma unitaryConjugate_mem_spectralBody {k : ℕ} {t : ℝ}
    (U : Matrix.unitaryGroup (Fin k) ℂ) {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X ∈ spectralBody k t) : unitaryConjugate U X ∈ spectralBody k t := by
  obtain ⟨lam, hlam, V, rfl⟩ := hX
  refine ⟨lam, hlam, U*V, ?_⟩
  exact unitaryConjugate_comp U V _

lemma unitaryConjugate_diagonal_re {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℂ)
    (lam : Fin k → ℝ) (i : Fin k) :
    (unitaryConjugate U (diagonal (fun j => (lam j : ℂ))) i i).re =
      (unitaryWeights U *ᵥ lam) i := by
  rw [unitaryConjugate, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, conjTranspose_apply,
    Complex.re_sum, Matrix.mulVec, dotProduct, unitaryWeights]
  apply sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

lemma diagonal_mem_Lam_of_spectralBody {k : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X ∈ spectralBody k t) : (fun i => (X i i).re) ∈ Lam k t := by
  obtain ⟨lam, hlam, U, rfl⟩ := hX
  have heq : (fun i => ((U : Matrix (Fin k) (Fin k) ℂ) *
      diagonal (fun j => (lam j : ℂ)) * (U : Matrix (Fin k) (Fin k) ℂ).conjTranspose) i i |>.re) =
      unitaryWeights U *ᵥ lam := by
    funext i
    exact unitaryConjugate_diagonal_re U lam i
  rw [heq]
  exact doublyStochastic_mem_Lam ht0 ht1 (unitaryWeights_doublyStochastic U) hlam

lemma isHermitian_of_spectralBody {k : ℕ} {t : ℝ}
    {X : Matrix (Fin k) (Fin k) ℂ} (hX : X ∈ spectralBody k t) : X.IsHermitian := by
  obtain ⟨lam, hlam, U, rfl⟩ := hX
  apply Matrix.isHermitian_mul_mul_conjTranspose
  exact isHermitian_diagonal_iff.mpr (fun i => by simp [_root_.IsSelfAdjoint])

/-- Convexity of the full unitary-invariant matrix body. The proof diagonalizes
the convex combination and uses only doubly stochastic averaging of its summands. -/
theorem convex_spectralBody {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t) :
    Convex ℝ (spectralBody k t) := by
  intro X hX Y hY a b ha hb hab
  let C := a • X + b • Y
  have hCH : C.IsHermitian := by
    have hXH := isHermitian_of_spectralBody hX
    have hYH := isHermitian_of_spectralBody hY
    simp only [C, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      hXH.eq, hYH.eq, star_trivial]
  let W := hCH.eigenvectorUnitary
  have hX' := diagonal_mem_Lam_of_spectralBody ht0 ht1
    (unitaryConjugate_mem_spectralBody (star W) hX)
  have hY' := diagonal_mem_Lam_of_spectralBody ht0 ht1
    (unitaryConjugate_mem_spectralBody (star W) hY)
  have hdiag : (fun i => (unitaryConjugate (star W) C i i).re) ∈ Lam k t := by
    convert convex_Lam hk ht0 ht1 hkt hX' hY' ha hb hab using 1
    ext i
    simp [C, unitaryConjugate, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Complex.real_smul]
  have hdiagEq : unitaryConjugate (star W) C =
      diagonal (fun i => (hCH.eigenvalues i : ℂ)) := by
    simpa [unitaryConjugate, W, Matrix.star_eq_conjTranspose] using hCH.star_mul_self_mul_eq_diagonal
  rw [hdiagEq] at hdiag
  simp only [diagonal_apply_eq, Complex.ofReal_re] at hdiag
  refine ⟨hCH.eigenvalues, hdiag, W, ?_⟩
  exact hCH.spectral_theorem


lemma unitaryConjugate_star_self {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℂ)
    (X : Matrix (Fin k) (Fin k) ℂ) :
    unitaryConjugate (star U) (unitaryConjugate U X) = X := by
  rw [unitaryConjugate_comp]
  have heq : star U * U = 1 := by
    apply Subtype.ext
    exact U.prop.1
  rw [heq]
  simp [unitaryConjugate]

lemma trace_pairing_in_eigenbasis {k : ℕ} (H X : Matrix (Fin k) (Fin k) ℂ)
    (hH : H.IsHermitian) :
    (Matrix.trace (H*X)).re =
      ∑ i, hH.eigenvalues i * (unitaryConjugate (star hH.eigenvectorUnitary) X i i).re := by
  let V := hH.eigenvectorUnitary
  have heq : Matrix.trace (H*X) = Matrix.trace
      (diagonal (fun i => (hH.eigenvalues i : ℂ)) * unitaryConjugate (star V) X) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Matrix.mul_assoc _ _ X]
    rw [Matrix.trace_mul_cycle]
    rw [Matrix.trace_mul_cycle]
    simp [unitaryConjugate, V, Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Function.comp_def]
  rw [heq]
  simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum, V]

lemma spectralBody_nonempty {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (spectralBody k t).Nonempty := by
  obtain ⟨lam, hlam⟩ := Lam_nonempty hk ht0 ht1
  exact ⟨_, lam, hlam, 1, rfl⟩

lemma Lam_nonnegative_and_sum {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht0 : 0 ≤ t) (hkt : 1 < (k : ℝ)^2*t) {lam : Fin k → ℝ} (hlam : lam ∈ Lam k t) :
    (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 := by
  obtain ⟨u, hu, rfl⟩ := hlam
  have hs := body_mass_pos hk ht0 hkt u hu
  refine ⟨fun i => div_nonneg (hu.1 i).1 hs.le, ?_⟩
  rw [← sum_div, div_self hs.ne']

lemma spectralBody_subset_densityMatrices {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht0 : 0 ≤ t) (hkt : 1 < (k : ℝ)^2*t) :
    spectralBody k t ⊆ densityMatrices (Fin k) := by
  rintro X ⟨lam, hlam, U, rfl⟩
  have hl := Lam_nonnegative_and_sum hk ht0 hkt hlam
  have hd : (diagonal (fun i => (lam i : ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast hl.1 i
  refine ⟨hd.mul_mul_conjTranspose_same (U : Matrix (Fin k) (Fin k) ℂ), ?_⟩
  rw [Matrix.trace_mul_cycle, show (U : Matrix (Fin k) (Fin k) ℂ).conjTranspose * U = 1 from U.prop.1,
    Matrix.one_mul, Matrix.trace_diagonal]
  exact_mod_cast hl.2

/-- The exact maximum over the actual matrix body. The maximizing eigenbasis
is aligned with H; the upper bound follows from doubly stochastic averaging. -/
theorem spectralBody_support_isGreatest {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t)
    (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.IsHermitian) :
    IsGreatest ((fun X => (Matrix.trace (H*X)).re) '' spectralBody k t)
      (normalizedBodySupport k t hH.eigenvalues) := by
  have hs := normalizedBodySupport_isGreatest hk ht0.le ht1.le hkt hH.eigenvalues
  constructor
  · obtain ⟨u, hu, huval⟩ := hs.1
    let lam : Fin k → ℝ := fun i => u i / ∑ j, u j
    let V := hH.eigenvectorUnitary
    let X := unitaryConjugate V (diagonal (fun i => (lam i : ℂ)))
    refine ⟨X, ⟨lam, ⟨u, hu, rfl⟩, V, rfl⟩, ?_⟩
    change (Matrix.trace (H*X)).re = _
    rw [trace_pairing_in_eigenbasis H X hH]
    change (∑ i, hH.eigenvalues i * (unitaryConjugate (star V)
      (unitaryConjugate V (diagonal (fun i => (lam i : ℂ)))) i i).re) = _
    rw [unitaryConjugate_star_self]
    simp only [diagonal_apply_eq, Complex.ofReal_re, lam, ← mul_div_assoc, ← sum_div]
    exact huval
  · rintro v ⟨X, hX, rfl⟩
    change (Matrix.trace (H*X)).re ≤ _
    rw [trace_pairing_in_eigenbasis H X hH]
    have hdiag := diagonal_mem_Lam_of_spectralBody ht0 ht1
      (unitaryConjugate_mem_spectralBody (star hH.eigenvectorUnitary) hX)
    obtain ⟨u, hu, heq⟩ := hdiag
    have hv : (∑ i, hH.eigenvalues i *
        (unitaryConjugate (star hH.eigenvectorUnitary) X i i).re) =
        (∑ i, hH.eigenvalues i*u i)/∑ i, u i := by
      change (∑ i, hH.eigenvalues i * (fun i =>
        (unitaryConjugate (star hH.eigenvectorUnitary) X i i).re) i) = _
      rw [heq]
      simp only [← mul_div_assoc, ← sum_div]
    rw [hv]
    exact hs.2 ⟨u, hu, rfl⟩

theorem spectralBody_support {k : ℕ} {t : ℝ} (hk : 0 < k)
    (ht0 : 0 < t) (ht1 : t < 1) (hkt : 1 < (k : ℝ)^2*t)
    (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.IsHermitian) :
    sSup ((fun X => (Matrix.trace (H*X)).re) '' spectralBody k t) =
      normalizedBodySupport k t hH.eigenvalues :=
  (spectralBody_support_isGreatest hk ht0 ht1 hkt H hH).csSup_eq

end
end RevisionOutput
