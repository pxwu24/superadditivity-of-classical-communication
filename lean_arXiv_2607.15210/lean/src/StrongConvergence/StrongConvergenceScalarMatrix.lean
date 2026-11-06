import HaarProjections.RevisionCanonicalEnsemble
import HaarProjections.ProjectionOrbit

/-! Exact finite-dimensional identities for the one-dimensional output case.
These require no probabilistic convergence theorem: output rotation is scalar,
block modification is scalar multiplication, and affine norms are eventually
exactly the two-point norm. -/

open MeasureTheory Filter Set Matrix
open scoped Topology BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace ProjectionChannels.ScalarStrong
set_option maxHeartbeats 800000

variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

local instance scalarStrongMatrixCStarAlgebra : CStarAlgebra (Matrix A A ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance
  norm_mul_self_le := CStarRing.norm_mul_self_le

lemma localConjugate_one_output (P : Matrix (A×Fin 1) (A×Fin 1) ℂ)
    (U : Matrix.unitaryGroup (Fin 1) ℂ) : RevisionOutput.localConjugate P U=P := by
  have hU : star (U 0 0)*U 0 0=1 := by
    have h := congrArg (fun M:Matrix (Fin 1) (Fin 1) ℂ=>M 0 0) U.prop.1
    simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply] using h
  ext ⟨a,i⟩ ⟨b,j⟩
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  simp only [RevisionOutput.localConjugate,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.conjTranspose_apply,
    Fin.sum_univ_one,ite_mul,one_mul,zero_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  calc
    star (U 0 0)*P (a,0) (b,0)*U 0 0 = (star (U 0 0)*U 0 0)*P (a,0) (b,0) := by ring
    _ = _ := by rw [hU,one_mul]

lemma amplified_one_output (P : Matrix (A×Fin 1) (A×Fin 1) ℂ) (a : Fin 1→ℝ) :
    ProjectionChannelsCP.amplify (diagonalTraceLinearMap a) P=(a 0:ℂ) • P := by
  ext ⟨i,u⟩ ⟨j,v⟩
  have hu : u=0 := Subsingleton.elim _ _
  have hv : v=0 := Subsingleton.elim _ _
  subst u; subst v
  simp [ProjectionChannelsCP.amplify,diagonalTraceLinearMap,Matrix.smul_apply]

lemma compression_one_output (P : Matrix (A×Fin 1) (A×Fin 1) ℂ) (a : Fin 1→ℝ) :
    blockCompression (diagonalBlock P) a =
      (a 0:ℂ) • P.submatrix (fun i=>(i,0)) (fun i=>(i,0)) := by
  ext i j
  simp [blockCompression,diagonalBlock,Matrix.sum_apply,Matrix.smul_apply]

lemma affine_projection_cfc (P : Matrix A A ℂ) (hP : P.IsHermitian) (c a : ℝ) :
    cfc (fun x:ℝ=>c+a*x) P=(c:ℂ) • (1:Matrix A A ℂ)+(a:ℂ) • P := by
  have hmul : cfc (fun x:ℝ=>a*x) P=(a:ℂ) • P := by
    change cfc (fun x:ℝ=>a*id x) P = _
    rw [cfc_const_mul a id P,cfc_id ℝ P hP.isSelfAdjoint]
    ext i j
    simp [Algebra.algebraMap_eq_smul_one,Matrix.smul_mul,Matrix.smul_apply,Complex.real_smul]
  rw [cfc_const_add c (fun x:ℝ=>a*x) P (ha:=hP.isSelfAdjoint),hmul]
  congr 1
  ext i j
  simp [Algebra.algebraMap_eq_smul_one,Matrix.smul_apply,Complex.real_smul]

/-- A projection containing both eigenvalues has the exact two-atom affine norm. -/
theorem norm_affine_projection (P : Matrix A A ℂ) (hP : P.IsHermitian) (hp : P*P=P)
    (h0 : (0:ℝ)∈spectrum ℝ P) (h1 : (1:ℝ)∈spectrum ℝ P) (c a : ℝ) :
    ‖(c:ℂ) • (1:Matrix A A ℂ)+(a:ℂ) • P‖=max |c| |c+a| := by
  rw [←affine_projection_cfc P hP c a]
  apply le_antisymm
  · apply norm_cfc_le (le_trans (abs_nonneg c) (le_max_left _ _))
    intro x hx
    obtain ⟨i,rfl⟩ := hP.eigenvalues_eq_spectrum_real ▸ hx
    rcases ProjectionOrbit.eigenvalues_zero_or_one hP hp i with he|he
    · simpa only [he,mul_zero,add_zero,Real.norm_eq_abs] using le_max_left |c| |c+a|
    · simpa only [he,mul_one,Real.norm_eq_abs] using le_max_right |c| |c+a|
  · apply max_le
    · simpa only [mul_zero,add_zero,Real.norm_eq_abs] using
        norm_apply_le_norm_cfc (fun x:ℝ=>c+a*x) P h0 (ha:=hP.isSelfAdjoint)
    · simpa only [mul_one,Real.norm_eq_abs] using
        norm_apply_le_norm_cfc (fun x:ℝ=>c+a*x) P h1 (ha:=hP.isSelfAdjoint)

lemma canonical_projection_mem_spectrum (t : ℝ) (ω : Canonical.Sample 1) (n : ℕ)
    (i : Canonical.Index 1 n) :
    (if (Canonical.coordinateNumber 1 n i).val<Canonical.rankSequence 1 t n then (1:ℝ) else 0)
      ∈ spectrum ℝ (Canonical.projection 1 t ω n) := by
  unfold Canonical.projection
  change _∈spectrum ℝ ((ω n:Matrix _ _ ℂ)*Canonical.baseProjection 1 t n*star (ω n:Matrix _ _ ℂ))
  rw [unitary.spectrum.unitary_conjugate,←spectrum.algebraMap_mem_iff ℂ]
  unfold Canonical.baseProjection
  rw [spectrum_diagonal]
  refine ⟨i,?_⟩
  split_ifs <;> simp_all [Algebra.algebraMap_eq_smul_one]

lemma canonical_rank_eventually_nontrivial {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    ∀ᶠ n:ℕ in atTop, 0<Canonical.rankSequence 1 t n ∧ Canonical.rankSequence 1 t n<n+1 := by
  have h := Canonical.rank_density_tendsto (k:=1) (by norm_num) ht0.le
  have he := h.eventually (Ioo_mem_nhds ht0 ht1)
  filter_upwards [he] with n hn
  have hd : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hpos : (0:ℝ)<(Canonical.rankSequence 1 t n:ℝ) := by
    apply (div_pos_iff_of_pos_right hd).mp
    simpa using hn.1
  have hlt : (Canonical.rankSequence 1 t n:ℝ)<(n:ℝ)+1 := by
    apply (div_lt_one hd).mp
    simpa using hn.2
  constructor
  · exact_mod_cast hpos
  · exact_mod_cast hlt

/-- The norm part of strong convergence is eventually an exact equality,
for every sample and every signed coefficient and shift. -/
theorem canonical_scalar_norm_eventually {t : ℝ} (ht0 : 0<t) (ht1 : t<1)
    (ω : Canonical.Sample 1) (U : Matrix.unitaryGroup (Fin 1) ℂ) (a : Fin 1→ℝ) (c : ℝ) :
    ∀ᶠ n:ℕ in atTop,
      ‖(c:ℂ) • (1:Matrix (Canonical.Index 1 n) (Canonical.Index 1 n) ℂ)+
        ProjectionChannelsCP.amplify (diagonalTraceLinearMap a)
          (RevisionOutput.localConjugate (Canonical.projection 1 t ω n) U)‖ = max |c| |c+a 0| := by
  filter_upwards [canonical_rank_eventually_nontrivial ht0 ht1] with n hn
  rw [localConjugate_one_output,amplified_one_output]
  apply norm_affine_projection _ (Canonical.projection_isHermitian 1 t ω n)
    (Canonical.projection_idempotent 1 t ω n)
  · let j : Fin (Fintype.card (Canonical.Index 1 n)) :=
      ⟨Canonical.rankSequence 1 t n,by simpa [Canonical.Index,Fintype.card_prod] using hn.2⟩
    have h := canonical_projection_mem_spectrum t ω n ((Canonical.coordinateNumber 1 n).symm j)
    simpa [j] using h
  · let j : Fin (Fintype.card (Canonical.Index 1 n)) := ⟨0,by simp [Canonical.Index,Fintype.card_prod]⟩
    have h := canonical_projection_mem_spectrum t ω n ((Canonical.coordinateNumber 1 n).symm j)
    simpa [j,hn.1] using h

end ScalarStrong
end ProjectionChannels
