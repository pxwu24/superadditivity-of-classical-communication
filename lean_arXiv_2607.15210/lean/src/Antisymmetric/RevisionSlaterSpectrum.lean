import Antisymmetric.RevisionSlaterWeightedLadder
import Antisymmetric.RevisionHermitianMultiplicity
import Entropy.Defs

/-! The actual spectrum of the antisymmetric Slater partial-trace ladder.
This instantiates the generic Gram induction with the proved permutation
recurrence, including all multiplicities and absence of extra eigenvalues. -/

open Matrix Module.End LinearMap
open scoped BigOperators ComplexOrder
noncomputable section
namespace AntisymmetricVerification

lemma slater_ladder_card (k r : ℕ) :
    Fintype.card (SubsetIndex k r × SubsetIndex k r)=(k.choose r)^2 := by
  simp [Fintype.card_prod,card_subsetIndex,pow_two]

lemma slater_ladder_recurrence_real (k r : ℕ) :
    weightedSlaterReduction k r*(weightedSlaterReduction k r).conjTranspose =
      (((k:ℝ)-2*r:ℝ):ℂ) • 1+slaterLadderGram k r := by
  simpa only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_natCast]
    using weightedSlaterReduction_ladder k r

/-- Proposition B.2: the actual weighted reduction Gram multiplicities. -/
theorem slaterLadderGram_multiplicity {k r : ℕ} (hkr : 2*r≤k) (j : ℕ) (hj : j≤r) :
    Module.finrank ℂ (eigenspace (Matrix.toLin' (slaterLadderGram k r))
      (ladderValue k r j : ℂ)) = ladderMultiplicity k j :=
  gram_ladder_multiplicities k r hkr (slaterLadderGram k) (weightedSlaterReduction k)
    rfl (fun _ _ => rfl) (fun l _ => slater_ladder_recurrence_real k l)
    (fun l _ => slater_ladder_card k l) r le_rfl j hj

/-- No extra spectral values occur in the actual Slater Gram matrix. -/
theorem slaterLadderGram_no_other_eigenvalues (k r : ℕ) (z : ℂ)
    (hz : ∀ j≤r, z≠(ladderValue k r j : ℂ)) :
    eigenspace (Matrix.toLin' (slaterLadderGram k r)) z=⊥ :=
  gram_ladder_no_other_eigenvalues k r (slaterLadderGram k) (weightedSlaterReduction k)
    rfl (fun _ _ => rfl) (fun l _ => slater_ladder_recurrence_real k l) r le_rfl z hz

lemma slaterLadderGram_posSemidef (k r : ℕ) : (slaterLadderGram k r).PosSemidef := by
  cases r with
  | zero => exact Matrix.PosSemidef.zero
  | succ r => exact Matrix.posSemidef_conjTranspose_mul_self _

lemma slaterLadderGram_isHermitian (k r : ℕ) : (slaterLadderGram k r).IsHermitian :=
  (slaterLadderGram_posSemidef k r).isHermitian

lemma subsetIndex_nonempty_of_le {k r : ℕ} (hrk : r≤k) : Nonempty (SubsetIndex k r) := by
  apply Fintype.card_pos_iff.mp
  rw [card_subsetIndex]
  exact Nat.choose_pos hrk

/-- Every entry of the actual spectral list has one of the ladder values. -/
theorem slaterLadderGram_eigenvalues_covered {k r : ℕ} (hrk : r≤k) :
    ∀ i, ∃ j : Fin (r+1),
      (slaterLadderGram_isHermitian k r).eigenvalues i=ladderValue k r j := by
  letI := subsetIndex_nonempty_of_le hrk
  apply hermitian_eigenvalues_covered (slaterLadderGram_isHermitian k r)
    (fun j : Fin (r+1) => ladderValue k r j)
  intro z hz
  apply slaterLadderGram_no_other_eigenvalues
  intro j hj heq
  apply hz ⟨j,by omega⟩
  exact_mod_cast heq

/-- Evaluation of arbitrary spectral sums in the actual Gram matrix. -/
theorem slaterLadderGram_spectral_sum {k r : ℕ} (hkr : 2*r≤k) (f : ℝ→ℝ) :
    ∑ i, f ((slaterLadderGram_isHermitian k r).eigenvalues i) =
      ∑ j : Fin (r+1), (ladderMultiplicity k j:ℝ)*f (ladderValue k r j) := by
  letI := subsetIndex_nonempty_of_le (show r≤k by omega)
  have hinj : Function.Injective (fun j : Fin (r+1) => ladderValue k r j) := by
    intro i j hij
    apply Fin.ext
    exact (ladderValue_strictAntiOn hkr).injOn ⟨Nat.zero_le _,by omega⟩ ⟨Nat.zero_le _,by omega⟩ hij
  rw [sum_eigenvalues_by_multiplicity (slaterLadderGram_isHermitian k r)
    (fun j : Fin (r+1) => ladderValue k r j) hinj (slaterLadderGram_eigenvalues_covered (by omega)) f]
  apply Finset.sum_congr rfl
  intro j _
  rw [slaterLadderGram_multiplicity hkr j (by omega)]

/-- The geometric multiplicities agree with the real-valued multiplicities
used in Appendix B, including the zero-degree convention. -/
theorem ladderMultiplicity_cast_eq_dm {k j : ℕ} (hkj : 2*j≤k) :
    (ladderMultiplicity k j:ℝ)=AppendixB.dm k j := by
  by_cases hj : j=0
  · subst j
    simp [ladderMultiplicity,AppendixB.dm]
  · have hj1 : 1≤j := by omega
    have hlt : j-1<k/2 := by omega
    have hc := Nat.choose_le_succ_of_lt_half_left hlt
    rw [Nat.sub_add_cancel hj1] at hc
    have hp : (k.choose (j-1))^2≤(k.choose j)^2 := Nat.pow_le_pow_left hc 2
    simp only [ladderMultiplicity,if_neg hj,AppendixB.dm,Nat.cast_sub hp,Nat.cast_pow]

end AntisymmetricVerification
