import Antisymmetric.RevisionGramLadder
import HaarProjections.HaarProjection

/-! Relating genuine Hermitian eigenspace dimensions to the finite spectral
list used by matrix entropy. -/

open Matrix Module.End LinearMap Finset
open scoped BigOperators
noncomputable section
namespace AntisymmetricVerification

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

lemma hermitian_eigenspace_finrank_eq_count {M : Matrix n n ℂ} (hM : M.IsHermitian) (z : ℝ) :
    Module.finrank ℂ (eigenspace (Matrix.toLin' M) (z:ℂ)) =
      Fintype.card {i : n // hM.eigenvalues i=z} := by
  classical
  let N := (z:ℂ) • (1 : Matrix n n ℂ)-M
  have hker : LinearMap.ker (Matrix.toLin' N) = eigenspace (Matrix.toLin' M) (z:ℂ) := by
    ext v
    simp only [LinearMap.mem_ker,mem_eigenspace_iff,Matrix.toLin'_apply,N,
      Matrix.sub_mulVec,Matrix.smul_mulVec_assoc,Matrix.one_mulVec,sub_eq_zero,eq_comm]
  have hr : N.rank = Fintype.card {i : n // hM.eigenvalues i≠z} := by
    rw [show N=(z:ℂ) • (1 : Matrix n n ℂ)-M from rfl,
      ProjectionChannels.scalar_shift_spectral hM z,HaarProjection.unitary_conjugation_rank,
      Matrix.rank_diagonal]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun i => by simp [sub_eq_zero,ne_comm])
  have hdim := (Matrix.toLin' N).finrank_range_add_finrank_ker
  have hrange : Module.finrank ℂ (LinearMap.range (Matrix.toLin' N))=N.rank := rfl
  rw [hrange,hker,Module.finrank_pi,hr] at hdim
  have hcomp := Fintype.card_subtype_compl (fun i : n => hM.eigenvalues i=z)
  have hle := Fintype.card_subtype_le (fun i : n => hM.eigenvalues i=z)
  rw [hcomp] at hdim
  have hh := hdim.trans (Nat.sub_add_cancel hle).symm
  exact Nat.add_left_cancel hh

/-- A finite spectral sum may be evaluated using the exact geometric
multiplicity of each distinct eigenvalue. -/
theorem sum_eigenvalues_by_multiplicity
    {J : Type*} [Fintype J] [DecidableEq J]
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (v : J → ℝ) (hv : Function.Injective v)
    (hfull : ∀ i, ∃ j, hM.eigenvalues i=v j) (f : ℝ → ℝ) :
    ∑ i, f (hM.eigenvalues i) =
      ∑ j, (Module.finrank ℂ (eigenspace (Matrix.toLin' M) (v j:ℂ)):ℝ)*f (v j) := by
  classical
  simp_rw [hermitian_eigenspace_finrank_eq_count hM]
  have hsum (j : J) : (Fintype.card {i : n // hM.eigenvalues i=v j}:ℝ)*f (v j) =
      ∑ i : n, if hM.eigenvalues i=v j then f (hM.eigenvalues i) else 0 := by
    rw [Fintype.card_subtype]
    simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero]
    have heq : (∑ i ∈ Finset.univ.filter (fun i => hM.eigenvalues i=v j), f (hM.eigenvalues i)) =
        ∑ i ∈ Finset.univ.filter (fun i => hM.eigenvalues i=v j), f (v j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    rw [heq]
    simp
  simp_rw [hsum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨j,hj⟩ := hfull i
  rw [hj]
  have he : ∀ l : J, v j=v l ↔ j=l := fun l => hv.eq_iff
  simp_rw [he]
  simp

/-- Absence of further eigenspaces covers every entry of the actual
Hermitian spectral list. -/
theorem hermitian_eigenvalues_covered
    {J : Type*} [Fintype J] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (v : J → ℝ)
    (hno : ∀ z : ℝ, (∀ j, z≠v j) → eigenspace (Matrix.toLin' M) (z:ℂ)=⊥) :
    ∀ i, ∃ j, hM.eigenvalues i=v j := by
  classical
  intro i
  by_contra h
  push_neg at h
  have hz := hno (hM.eigenvalues i) h
  have hc := hermitian_eigenspace_finrank_eq_count hM (hM.eigenvalues i)
  rw [hz,finrank_bot] at hc
  letI : Nonempty {j : n // hM.eigenvalues j=hM.eigenvalues i} := ⟨⟨i,rfl⟩⟩
  have hp : 0<Fintype.card {j : n // hM.eigenvalues j=hM.eigenvalues i} := Fintype.card_pos
  omega

end AntisymmetricVerification
