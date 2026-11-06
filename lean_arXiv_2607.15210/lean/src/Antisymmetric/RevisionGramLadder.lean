import Antisymmetric.RevisionGramSpectrum
import RandomCompression.CompressionSpectral
import Preliminaries.CompletePositivity

/-! Spectral multiplicities obtained from the actual antisymmetric Gram
ladder. The induction uses only its matrix recurrence and dimensions.
All surjectivity and eigenspace transfer steps are proved. -/

open Matrix Module.End LinearMap
open scoped ComplexOrder
noncomputable section
namespace AntisymmetricVerification

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma matrix_scalar_shift_eigenspace (M : Matrix n n ℂ) (c z : ℂ) :
    eigenspace (Matrix.toLin' (c • (1 : Matrix n n ℂ)+M)) (c+z) =
      eigenspace (Matrix.toLin' M) z := by
  ext v
  simp only [mem_eigenspace_iff,Matrix.toLin'_apply,Matrix.add_mulVec,
    Matrix.smul_mulVec_assoc,Matrix.one_mulVec,add_smul]
  exact add_left_cancel_iff

/-- Nonzero scalar multiplication transports eigenspaces exactly. -/
lemma matrix_scalar_smul_eigenspace (M : Matrix n n ℂ) (c z : ℂ) (hc : c≠0) :
    eigenspace (Matrix.toLin' (c • M)) (c*z) = eigenspace (Matrix.toLin' M) z := by
  ext v
  simp only [mem_eigenspace_iff,Matrix.toLin'_apply,Matrix.smul_mulVec_assoc,MulAction.mul_smul]
  constructor
  · intro h
    have hh := congrArg (fun v : n → ℂ => c⁻¹ • v) h
    simpa only [smul_smul,← mul_assoc,inv_mul_cancel₀ hc,one_mul,one_smul] using hh
  · exact congrArg (fun v : n → ℂ => c • v)

lemma gram_surjective_of_posDef (A : Matrix m n ℂ)
    (h : (A*A.conjTranspose).PosDef) : Function.Surjective (Matrix.toLin' A) := by
  intro y
  refine ⟨A.conjTranspose.mulVec ((A*A.conjTranspose)⁻¹.mulVec y),?_⟩
  simp only [Matrix.toLin'_apply,Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit),Matrix.one_mulVec]

/-- Unscaled ladder eigenvalue: multiplication by ell² restores the
normalization of the partial-trace map in the paper. -/
def ladderValue (k ell j : ℕ) : ℝ :=
  ((ell:ℝ)-j)*((k:ℝ)-ell-j+1)

def ladderMultiplicity (k j : ℕ) : ℕ :=
  if j=0 then 1 else (k.choose j)^2-(k.choose (j-1))^2

lemma ladderValue_step (k ell j : ℕ) :
    ladderValue k (ell+1) j = ((k:ℝ)-2*ell)+ladderValue k ell j := by
  unfold ladderValue
  push_cast
  ring

lemma ladderValue_diag (k ell : ℕ) : ladderValue k ell ell=0 := by
  simp [ladderValue]

lemma ladderValue_step_pos {k ell j : ℕ} (hj : j≤ell) (hk : 2*(ell+1)≤k) :
    0<ladderValue k (ell+1) j := by
  have hj' : (j:ℝ)≤ell := by exact_mod_cast hj
  have hk' : 2*((ell:ℝ)+1)≤k := by exact_mod_cast hk
  unfold ladderValue
  push_cast
  apply mul_pos <;> linarith

variable {V : ℕ → Type*} [∀ ell, Fintype (V ell)] [∀ ell, DecidableEq (V ell)]

/-- The recurrence itself forces all lowering maps up to the middle level
to be surjective. -/
theorem gram_ladder_surjective (k r : ℕ) (hkr : 2*r≤k)
    (G : ∀ ell, Matrix (V ell) (V ell) ℂ)
    (A : ∀ ell, Matrix (V ell) (V (ell+1)) ℂ)
    (hzero : G 0=0)
    (hgram : ∀ ell<r, G (ell+1)=(A ell).conjTranspose*A ell)
    (hrec : ∀ ell<r, A ell*(A ell).conjTranspose =
      ((((k:ℝ)-2*ell):ℝ):ℂ) • (1 : Matrix (V ell) (V ell) ℂ)+G ell)
    (ell : ℕ) (hell : ell<r) : Function.Surjective (Matrix.toLin' (A ell)) := by
  have hG : (G ell).PosSemidef := by
    cases ell with
    | zero => rw [hzero]; exact Matrix.PosSemidef.zero
    | succ l => rw [hgram l (by omega)]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hc : 0<(k:ℝ)-2*ell := by
    have h : 2*(ell+1)≤k := by omega
    have h' : 2*((ell:ℝ)+1)≤k := by exact_mod_cast h
    linarith
  apply gram_surjective_of_posDef
  rw [hrec ell hell]
  have hid : (((((k:ℝ)-2*ell):ℝ):ℂ) • (1 : Matrix (V ell) (V ell) ℂ)).PosDef := by
    have hh := Matrix.PosDef.diagonal (fun _ : V ell => Complex.zero_lt_real.mpr hc)
    convert hh using 1
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
  exact hid.add_posSemidef hG

/-- Every multiplicity in the antisymmetric Gram ladder is determined by
its genuine recurrence. There is no assumed spectral decomposition. -/
theorem gram_ladder_multiplicities (k r : ℕ) (hkr : 2*r≤k)
    (G : ∀ ell, Matrix (V ell) (V ell) ℂ)
    (A : ∀ ell, Matrix (V ell) (V (ell+1)) ℂ)
    (hzero : G 0=0)
    (hgram : ∀ ell<r, G (ell+1)=(A ell).conjTranspose*A ell)
    (hrec : ∀ ell<r, A ell*(A ell).conjTranspose =
      ((((k:ℝ)-2*ell):ℝ):ℂ) • (1 : Matrix (V ell) (V ell) ℂ)+G ell)
    (hcard : ∀ ell≤r, Fintype.card (V ell)=(k.choose ell)^2) :
    ∀ ell≤r, ∀ j≤ell,
      Module.finrank ℂ (eigenspace (Matrix.toLin' (G ell)) (ladderValue k ell j : ℂ)) =
        ladderMultiplicity k j := by
  intro ell
  induction ell with
  | zero =>
    intro hell j hj
    have hj0 : j=0 := by omega
    subst j
    rw [hzero]
    rw [ladderValue_diag k 0,Complex.ofReal_zero,eigenspace_zero]
    have hz : Matrix.toLin' (0 : Matrix (V 0) (V 0) ℂ)=0 := map_zero _
    rw [hz,LinearMap.ker_zero,finrank_top,Module.finrank_pi,hcard 0 hell]
    simp [ladderMultiplicity]
  | succ ell ih =>
    intro hell j hj
    have helr : ell<r := by omega
    have hkel : 2*(ell+1)≤k := by omega
    by_cases hjlast : j=ell+1
    · subst j
      rw [ladderValue_diag,Complex.ofReal_zero,hgram ell helr]
      have hz := gram_zero_multiplicity (A ell)
        (gram_ladder_surjective k r hkr G A hzero hgram hrec ell helr)
      rw [hcard ell (by omega),hcard (ell+1) hell] at hz
      simpa [ladderMultiplicity] using Nat.eq_sub_of_add_eq hz
    · have hjprev : j≤ell := by omega
      have hp := ladderValue_step_pos hjprev hkel
      have hne : (ladderValue k (ell+1) j : ℂ)≠0 := by exact_mod_cast hp.ne'
      rw [hgram ell helr,gram_eigenspace_finrank _ _ hne,hrec ell helr]
      have hv : (ladderValue k (ell+1) j : ℂ) =
          ((((k:ℝ)-2*ell):ℝ):ℂ)+(ladderValue k ell j : ℂ) := by
        rw [ladderValue_step,Complex.ofReal_add]
      rw [hv,matrix_scalar_shift_eigenspace]
      exact ih (by omega) j hjprev

lemma matrix_zero_eigenspace {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (hz : z≠0) :
    eigenspace (Matrix.toLin' (0 : Matrix n n ℂ)) z=⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have he := mem_eigenspace_iff.mp hv
  simp only [Matrix.toLin'_apply,Matrix.zero_mulVec] at he
  have hv0 : v=0 := (smul_eq_zero.mp he.symm).resolve_left hz
  simpa only [Submodule.mem_bot] using hv0

/-- There are no additional eigenvalues besides the ladder values. -/
theorem gram_ladder_no_other_eigenvalues (k r : ℕ)
    (G : ∀ ell, Matrix (V ell) (V ell) ℂ)
    (A : ∀ ell, Matrix (V ell) (V (ell+1)) ℂ)
    (hzero : G 0=0)
    (hgram : ∀ ell<r, G (ell+1)=(A ell).conjTranspose*A ell)
    (hrec : ∀ ell<r, A ell*(A ell).conjTranspose =
      ((((k:ℝ)-2*ell):ℝ):ℂ) • (1 : Matrix (V ell) (V ell) ℂ)+G ell) :
    ∀ ell≤r, ∀ z : ℂ, (∀ j≤ell, z≠(ladderValue k ell j : ℂ)) →
      eigenspace (Matrix.toLin' (G ell)) z=⊥ := by
  intro ell
  induction ell with
  | zero =>
    intro hell z hz
    rw [hzero]
    apply matrix_zero_eigenspace z
    simpa only [ladderValue_diag,Complex.ofReal_zero] using hz 0 le_rfl
  | succ ell ih =>
    intro hell z hz
    have helr : ell<r := by omega
    have hz0 : z≠0 := by simpa only [ladderValue_diag,Complex.ofReal_zero] using hz (ell+1) le_rfl
    apply Submodule.finrank_eq_zero.mp
    rw [hgram ell helr,gram_eigenspace_finrank _ _ hz0,hrec ell helr]
    let c : ℂ := ((((k:ℝ)-2*ell):ℝ):ℂ)
    have hez : z=c+(z-c) := by ring
    rw [hez,matrix_scalar_shift_eigenspace]
    have hn : ∀ j≤ell, z-c≠(ladderValue k ell j : ℂ) := by
      intro j hj heq
      apply hz j (by omega)
      rw [ladderValue_step,Complex.ofReal_add]
      change z=c+(ladderValue k ell j : ℂ)
      rw [← heq]
      ring
    rw [ih (by omega) (z-c) hn]
    simp

/-- Distinct levels yield distinct eigenvalues up to the middle degree. -/
theorem ladderValue_strictAntiOn {k ell : ℕ} (hk : 2*ell≤k) :
    StrictAntiOn (ladderValue k ell) (Set.Icc 0 ell) := by
  intro i hi j hj hij
  have hi' : (i:ℝ)<j := by exact_mod_cast hij
  have hj' : (j:ℝ)≤ell := by exact_mod_cast hj.2
  have hk' : 2*(ell:ℝ)≤k := by exact_mod_cast hk
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg i
  have hfactor : 0<((j:ℝ)-i)*((k:ℝ)+1-i-j) := mul_pos (by linarith) (by linarith)
  unfold ladderValue
  nlinarith

end AntisymmetricVerification
