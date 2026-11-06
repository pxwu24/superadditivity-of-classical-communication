import StrongConvergence.StrongConvergenceTensorPower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! An elementary invariant-tensor spanning argument.  The ambient matrix
dimension is at least the tensor degree, represented by an explicit embedding
of the tensor positions into the coordinate index type. -/

open Matrix
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

lemma tensorPower_diagonal_comm_entry
    (T : Matrix (Fin m → E) (Fin m → E) ℂ) (a : E → ℂ)
    (h : T * tensorPower m (Matrix.diagonal a) =
      tensorPower m (Matrix.diagonal a) * T) (i j : Fin m → E) :
    T i j * (∏ l, a (j l)) = (∏ l, a (i l)) * T i j := by
  rw [tensorPower_diagonal] at h
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using
    congrFun (congrFun h i) j

lemma prod_erase_coordinate (r : E) (i : Fin m → E) :
    (∏ l, if i l = r then (0 : ℂ) else 1) =
      if r ∈ Set.range i then 0 else 1 := by
  classical
  by_cases h : r ∈ Set.range i
  · obtain ⟨l, hl⟩ := h
    rw [if_pos (Set.mem_range.mpr ⟨l, hl⟩)]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])
  · rw [if_neg h]
    apply Finset.prod_eq_one
    intro l _
    exact if_neg (fun hl => h ⟨l, hl⟩)

/-- Every nonzero entry of a matrix commuting with all tensor powers preserves
the set of coordinate labels.  At a tuple of distinct labels this already
forces the output tuple to be a permutation of the input tuple. -/
lemma range_eq_of_commuting_entry_ne_zero
    (T : Matrix (Fin m → E) (Fin m → E) ℂ)
    (hT : ∀ A : Matrix E E ℂ, T * tensorPower m A = tensorPower m A * T)
    {i j : Fin m → E} (hij : T i j ≠ 0) : Set.range i = Set.range j := by
  classical
  ext r
  have h := tensorPower_diagonal_comm_entry T
    (fun x => if x = r then (0 : ℂ) else 1)
    (hT (Matrix.diagonal (fun x => if x = r then (0 : ℂ) else 1))) i j
  simp_rw [prod_erase_coordinate] at h
  by_cases hi : r ∈ Set.range i <;> by_cases hj : r ∈ Set.range j
  · simp [hi, hj]
  · simp [hi, hj] at h
    exact (hij h).elim
  · simp [hi, hj] at h
    exact (hij h.symm).elim
  · simp [hi, hj]

lemma exists_permutation_of_range_eq (e : Fin m ↪ E) (i : Fin m → E)
    (h : Set.range i = Set.range e) :
    ∃ σ : Equiv.Perm (Fin m), i = fun l => e (σ l) := by
  classical
  have hx : ∀ l, ∃ a, e a = i l := by
    intro l
    have hi : i l ∈ Set.range i := Set.mem_range_self l
    rw [h] at hi
    exact hi
  let f : Fin m → Fin m := fun l => Classical.choose (hx l)
  have hf : ∀ l, e (f l) = i l := fun l => Classical.choose_spec (hx l)
  have hs : Function.Surjective f := by
    intro a
    have ha : e a ∈ Set.range i := h.symm ▸ Set.mem_range_self a
    obtain ⟨l, hl⟩ := ha
    exact ⟨l, e.injective ((hf l).trans hl)⟩
  refine ⟨Equiv.ofBijective f hs.bijective_of_finite, ?_⟩
  funext l
  exact (hf l).symm

def permutationTensor (σ : Equiv.Perm (Fin m)) :
    Matrix (Fin m → E) (Fin m → E) ℂ :=
  fun i j => if i = (fun l => j (σ l)) then 1 else 0

lemma tuple_permutation_injective (e : Fin m ↪ E) :
    Function.Injective (fun σ : Equiv.Perm (Fin m) => fun l => e (σ l)) := by
  intro σ τ h
  apply Equiv.ext
  intro l
  exact e.injective (congrFun h l)

/-- A matrix with prescribed values on a selected list of distinct columns. -/
def tupleColumnMap (e : Fin m ↪ E) (j : Fin m → E) : Matrix E E ℂ :=
  fun a b => ∑ l, if b = e l then (if a = j l then 1 else 0) else 0

lemma tupleColumnMap_apply (e : Fin m ↪ E) (j : Fin m → E) (a : E) (l : Fin m) :
    tupleColumnMap e j a (e l) = if a = j l then 1 else 0 := by
  classical
  simp only [tupleColumnMap, e.injective.eq_iff]
  simp

lemma tensorPower_tupleColumnMap (e : Fin m ↪ E) (j i : Fin m → E)
    (σ : Equiv.Perm (Fin m)) :
    tensorPower m (tupleColumnMap e j) i (fun l => e (σ l)) =
      if i = (fun l => j (σ l)) then 1 else 0 := by
  classical
  simp only [tensorPower, tupleColumnMap_apply]
  by_cases h : i = fun l => j (σ l)
  · simp [h]
  · rw [if_neg h]
    have hn : ∃ l, i l ≠ j (σ l) := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨l, hl⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)

/-- Schur--Weyl's commutant spanning assertion for a family that commutes with
all matrix tensor powers.  The unitary-to-matrix extension is proved separately.
No invariant-theory or integration formula is assumed here. -/
theorem eq_sum_permutationTensor_of_commutes
    (e : Fin m ↪ E) (T : Matrix (Fin m → E) (Fin m → E) ℂ)
    (hT : ∀ A : Matrix E E ℂ, T * tensorPower m A = tensorPower m A * T) :
    T = ∑ σ : Equiv.Perm (Fin m),
      T (fun l => e (σ l)) e • permutationTensor (E := E) σ := by
  classical
  have hz (v : Fin m → E)
      (hv : v ∉ Set.range (fun σ : Equiv.Perm (Fin m) => fun l => e (σ l))) :
      T v e = 0 := by
    by_contra hh
    obtain ⟨σ, hσ⟩ := exists_permutation_of_range_eq e v
      (range_eq_of_commuting_entry_ne_zero T hT hh)
    exact hv ⟨σ, hσ.symm⟩
  ext i j
  have hcomm := congrFun (congrFun (hT (tupleColumnMap e j)) i) e
  have hbase (v : Fin m → E) :
      tensorPower m (tupleColumnMap e j) v e = if v = j then 1 else 0 := by
    simpa using tensorPower_tupleColumnMap e j v (Equiv.refl _)
  simp only [Matrix.mul_apply, hbase] at hcomm
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at hcomm
  rw [hcomm]
  have hsum := Fintype.sum_of_injective
    (fun σ : Equiv.Perm (Fin m) => fun l => e (σ l))
    (tuple_permutation_injective e)
    (fun σ => tensorPower m (tupleColumnMap e j) i (fun l => e (σ l)) *
      T (fun l => e (σ l)) e)
    (fun v => tensorPower m (tupleColumnMap e j) i v * T v e)
    (fun v hv => by dsimp; rw [hz v hv, mul_zero]) (fun _ => rfl)
  rw [← hsum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensorPower_tupleColumnMap, permutationTensor]
  apply Finset.sum_congr rfl
  intro σ _
  exact mul_comm _ _

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.eq_sum_permutationTensor_of_commutes
