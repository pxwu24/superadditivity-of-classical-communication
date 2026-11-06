import StrongConvergence.StrongConvergenceTensorGramBounds
import StrongConvergence.StrongConvergenceTensorPhase
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Sym.Card
import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.Nat.Factorial.BigOperators

open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

/-- The multiset of entries of a tensor coordinate. -/
def tupleSym (i : Fin m → E) : Sym E m :=
  ⟨Finset.univ.val.map i, by simp⟩

lemma tupleSym_count (i : Fin m → E) (e : E) :
    (tupleSym i).val.count e = tupleCount i e := by
  change (Finset.univ.val.map i).count e = tupleCount i e
  rw [Multiset.count_map]
  simp only [tupleCount, ← Finset.filter_val, Finset.card_def, eq_comm]

lemma tupleSym_surjective : Function.Surjective (tupleSym (E := E) (m := m)) := by
  intro s
  let e : Fin m ≃ s.val := Fintype.equivOfCardEq (by simp [s.property])
  refine ⟨fun l => (e l : E), ?_⟩
  apply Subtype.ext
  change Finset.univ.val.map ((fun x : s.val => (x : E)) ∘ e) = s.val
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv, Multiset.map_univ_coe]

lemma tupleSym_eq_iff (i j : Fin m → E) :
    tupleSym i = tupleSym j ↔ ∃ σ : Equiv.Perm (Fin m), i = fun l => j (σ l) := by
  constructor
  · intro h
    have hc (e : E) : Fintype.card {l // i l = e} = Fintype.card {l // j l = e} := by
      have hh := congrArg (fun s : Sym E m => s.val.count e) h
      change (tupleSym i).val.count e = (tupleSym j).val.count e at hh
      rw [tupleSym_count, tupleSym_count] at hh
      simpa only [tupleCount, Fintype.card_subtype] using hh
    let e := Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hc a))
    refine ⟨e, ?_⟩
    funext l
    exact (Equiv.ofFiberEquiv_map (fun a => Fintype.equivOfCardEq (hc a)) l).symm
  · rintro ⟨σ, rfl⟩
    apply Subtype.ext
    change Finset.univ.val.map (j ∘ σ) = Finset.univ.val.map j
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

lemma tuple_orbitRel_iff (i j : Fin m → E) :
    MulAction.orbitRel (Equiv.Perm (Fin m))ᵈᵐᵃ (Fin m → E) i j ↔ tupleSym i = tupleSym j := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, tupleSym_eq_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨DomMulAct.mk.symm g, hg.symm⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨DomMulAct.mk σ, hσ.symm⟩

/-- Orbits of position permutations are precisely multisets of fixed cardinality. -/
def tupleOrbitEquivSym :
    MulAction.orbitRel.Quotient (Equiv.Perm (Fin m))ᵈᵐᵃ (Fin m → E) ≃ Sym E m :=
  (Quotient.congrRight (tuple_orbitRel_iff (E := E))).trans
    (Setoid.quotientKerEquivOfSurjective _ tupleSym_surjective)

lemma fixedBy_card_eq_fixedTupleCount (σ : Equiv.Perm (Fin m)) :
    Fintype.card (MulAction.fixedBy (Fin m → E) (DomMulAct.mk σ)) =
      fixedTupleCount (E := E) σ := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl (Fin m → E))
  intro i
  change (fun l => i (σ l)) = i ↔ i = (fun l => i (σ l))
  exact eq_comm

set_option maxHeartbeats 1000000 in
/-- Burnside's lemma evaluates the complete Haar permutation Gram row sum. -/
theorem sum_fixedTupleCount :
    (∑ σ : Equiv.Perm (Fin m), fixedTupleCount (E := E) σ) =
      (Fintype.card E).ascFactorial m := by
  letI : Fintype (Equiv.Perm (Fin m))ᵈᵐᵃ :=
    Fintype.ofEquiv (Equiv.Perm (Fin m)) DomMulAct.mk
  letI : Fintype (MulAction.orbitRel.Quotient (Equiv.Perm (Fin m))ᵈᵐᵃ (Fin m → E)) :=
    Fintype.ofEquiv (Sym E m) tupleOrbitEquivSym.symm
  calc
    _ = ∑ σ : Equiv.Perm (Fin m),
        Fintype.card (MulAction.fixedBy (Fin m → E) (DomMulAct.mk σ)) := by
      simp only [fixedBy_card_eq_fixedTupleCount]
    _ = ∑ g : (Equiv.Perm (Fin m))ᵈᵐᵃ,
        Fintype.card (MulAction.fixedBy (Fin m → E) g) :=
      Equiv.sum_comp (DomMulAct.mk : Equiv.Perm (Fin m) ≃
        (Equiv.Perm (Fin m))ᵈᵐᵃ)
        (fun g => Fintype.card (MulAction.fixedBy (Fin m → E) g))
    _ = Fintype.card (MulAction.orbitRel.Quotient
          (Equiv.Perm (Fin m))ᵈᵐᵃ (Fin m → E)) *
        Fintype.card (Equiv.Perm (Fin m))ᵈᵐᵃ :=
      MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group _ _
    _ = Fintype.card (Sym E m) * Fintype.card (Equiv.Perm (Fin m)) := by
      rw [Fintype.card_congr (tupleOrbitEquivSym (E := E) (m := m)),
        ← Fintype.card_congr (DomMulAct.mk : Equiv.Perm (Fin m) ≃ _)]
    _ = (Fintype.card E).ascFactorial m := by
      rw [Sym.card_sym_eq_multichoose, Fintype.card_perm, Fintype.card_fin,
        Nat.multichoose_eq, mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose,
        Nat.add_descFactorial_eq_ascFactorial']

lemma normalized_gram_error_entry (hE : 0 < Fintype.card E)
    (σ τ : Equiv.Perm (Fin m)) :
    ‖(((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m - 1) σ τ‖ =
      ((Fintype.card E : ℝ) ^ m)⁻¹ * (fixedTupleCount (E := E) (τ * σ.symm) : ℝ) -
        if σ = τ then 1 else 0 := by
  have hNc : (Fintype.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hE)
  have hNr : (Fintype.card E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hE)
  by_cases hστ : σ = τ
  · subst τ
    simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hNc, hNr]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne hστ, sub_zero, if_neg hστ, norm_mul, norm_inv,
      norm_pow, Complex.norm_natCast, permutationGram_eq_fixedTupleCount]

/-- Exact row error; the formula is uniform in the row permutation. -/
theorem normalized_permutationGram_sub_one_row_exact
    (hE : 0 < Fintype.card E) (σ : Equiv.Perm (Fin m)) :
    (∑ τ : Equiv.Perm (Fin m),
      ‖(((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m - 1) σ τ‖) =
      ((Fintype.card E).ascFactorial m : ℝ) / (Fintype.card E : ℝ) ^ m - 1 := by
  simp_rw [normalized_gram_error_entry hE]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hs : (∑ τ : Equiv.Perm (Fin m),
      (fixedTupleCount (E := E) (τ * σ.symm) : ℝ)) =
      ((Fintype.card E).ascFactorial m : ℝ) := by
    have hh := Equiv.sum_comp (Equiv.mulRight σ.symm)
      (fun τ => (fixedTupleCount (E := E) τ : ℝ))
    simpa only [Equiv.coe_mulRight, ← Nat.cast_sum, sum_fixedTupleCount] using hh
  rw [hs]
  simp [div_eq_mul_inv, mul_comm]

/-- This sharper error grows quadratically, rather than factorially, in the
moment degree at first order in the inverse dimension. -/
theorem normalized_permutationGram_sub_one_row_product
    (hE : 0 < Fintype.card E) (σ : Equiv.Perm (Fin m)) :
    (∑ τ : Equiv.Perm (Fin m),
      ‖(((Fintype.card E : ℂ) ^ m)⁻¹ • permutationGram E m - 1) σ τ‖) =
      (∏ j ∈ Finset.range m, (1 + (j : ℝ) / Fintype.card E)) - 1 := by
  rw [normalized_permutationGram_sub_one_row_exact hE]
  congr 1
  have hN : (Fintype.card E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hE)
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
  have hp : (Fintype.card E : ℝ) ^ m = ∏ _j ∈ Finset.range m, (Fintype.card E : ℝ) := by
    simp
  rw [hp, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  field_simp

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.sum_fixedTupleCount
#print axioms ProjectionChannels.TensorHaar.normalized_permutationGram_sub_one_row_product
