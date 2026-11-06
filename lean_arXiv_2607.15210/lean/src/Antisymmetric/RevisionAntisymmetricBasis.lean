import Antisymmetric.RevisionAntisymmetric
import Mathlib.LinearAlgebra.Basis.Defs

/-! The actual standard Slater coordinate family. These proofs identify the
 alternating subspace with coordinates indexed by `r`-subsets. -/
noncomputable section
open Finset Equiv
namespace AntisymmetricVerification
variable {k r : ℕ}

abbrev SubsetIndex (k r : ℕ) := {I : Finset (Fin k) // I.card = r}

def subsetEnum (I : SubsetIndex k r) : Fin r → Fin k := I.val.orderEmbOfFin I.property

def standardVector (a : Fin k) : Fin k → ℂ := fun b => if a = b then 1 else 0

def standardSlater (I : SubsetIndex k r) : TensorVector k r :=
  slater (fun j => standardVector (subsetEnum I j))

lemma subsetEnum_injective (I : SubsetIndex k r) : Function.Injective (subsetEnum I) :=
  (I.val.orderEmbOfFin I.property).injective

lemma subsetEnum_mem (I : SubsetIndex k r) (j : Fin r) : subsetEnum I j ∈ I.val :=
  I.val.orderEmbOfFin_mem I.property j

lemma standardSlater_self (I : SubsetIndex k r) : standardSlater I (subsetEnum I) = 1 := by
  have heq : (fun i j => standardVector (subsetEnum I i) (subsetEnum I j)) =
      (1 : Matrix (Fin r) (Fin r) ℂ) := by
    funext i j
    simp only [standardVector, Matrix.one_apply, (subsetEnum_injective I).eq_iff]
  change Matrix.det _ = 1
  rw [heq, Matrix.det_one]

lemma standardSlater_ne_zero (I : SubsetIndex k r) : standardSlater I ≠ 0 := by
  intro h
  have hx := congrFun h (subsetEnum I)
  rw [standardSlater_self] at hx
  exact one_ne_zero hx

lemma standardSlater_of_missing (I : SubsetIndex k r) (x : TensorIndex k r)
    {a : Fin k} (ha : a ∈ I.val) (hx : ∀ j, x j ≠ a) : standardSlater I x = 0 := by
  obtain ⟨j, hj⟩ := (I.val.orderIsoOfFin I.property).surjective ⟨a, ha⟩
  have hja : subsetEnum I j = a := congrArg Subtype.val hj
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro l
  change standardVector (subsetEnum I j) (x l) = 0
  rw [hja]
  simp [standardVector, Ne.symm (hx l)]

lemma standardSlater_other (I J : SubsetIndex k r) (h : I ≠ J) :
    standardSlater I (subsetEnum J) = 0 := by
  have hnsub : ¬ I.val ⊆ J.val := by
    intro hs
    apply h
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hs (by rw [I.property, J.property])
  obtain ⟨a, haI, haJ⟩ := Finset.not_subset.mp hnsub
  apply standardSlater_of_missing I (subsetEnum J) haI
  intro j heq
  apply haJ
  rw [← heq]
  exact subsetEnum_mem J j

/-- Evaluation on increasing tensor indices gives the Kronecker delta. -/
theorem standardSlater_evaluation (I J : SubsetIndex k r) :
    standardSlater I (subsetEnum J) = if I = J then 1 else 0 := by
  classical
  by_cases h : I = J
  · subst I
    simp [standardSlater_self]
  · simp [h, standardSlater_other I J h]

/-- In particular, no multiplicities are lost by merging the different
 subset labels: their Slater vectors are linearly independent. -/
theorem standardSlater_linearIndependent :
    LinearIndependent ℂ (standardSlater : SubsetIndex k r → TensorVector k r) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc I hI
  have heval := congrFun hc (subsetEnum I)
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, standardSlater_evaluation,
    Pi.zero_apply, mul_ite, mul_one, mul_zero, sum_ite_eq', if_pos hI] using heval

lemma alternating_zero_of_not_injective {f : TensorVector k r} (hf : alternating f)
    {x : TensorIndex k r} (hx : ¬ Function.Injective x) : f x = 0 := by
  classical
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  have hcomp : x ∘ Equiv.swap i j = x := by
    funext l
    by_cases hli : l = i
    · subst l
      simpa using hij.symm
    · by_cases hlj : l = j
      · subst l
        simpa using hij
      · simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hli hlj]
  have h := congrFun (hf (Equiv.swap i j)) x
  simp only [permute, hcomp, Pi.smul_apply, smul_eq_mul, signC,
    Perm.sign_swap hne, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
    neg_one_mul] at h
  linear_combination (1 / 2 : ℂ) * h

lemma standardSlater_zero_of_not_injective (I : SubsetIndex k r)
    {x : TensorIndex k r} (hx : ¬ Function.Injective x) : standardSlater I x = 0 :=
  alternating_zero_of_not_injective (slater_alternating _) hx

/-- An injective tensor index is the increasing enumeration of its support,
 followed by a permutation. -/
lemma tensorIndex_eq_enum_perm (x : TensorIndex k r) (hx : Function.Injective x) :
    ∃ (I : SubsetIndex k r) (σ : Perm (Fin r)), x = subsetEnum I ∘ σ := by
  classical
  let I : SubsetIndex k r := ⟨univ.image x, by
    rw [card_image_of_injective _ hx, card_univ, Fintype.card_fin]⟩
  let f : Fin r → I.val := fun j => ⟨x j, mem_image.mpr ⟨j, mem_univ j, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact hx (congrArg Subtype.val hab)
    · intro a
      obtain ⟨j, hj, heq⟩ := mem_image.mp a.property
      exact ⟨j, Subtype.ext heq⟩
  let e : Fin r ≃ I.val := Equiv.ofBijective f hf
  let σ : Perm (Fin r) := e.trans (I.val.orderIsoOfFin I.property).toEquiv.symm
  refine ⟨I, σ, ?_⟩
  funext j
  change (e j).val = ((I.val.orderIsoOfFin I.property)
    ((I.val.orderIsoOfFin I.property).symm (e j))).val
  rw [OrderIso.apply_symm_apply]

/-- The standard Slater family spans every alternating coordinate vector.
 This is an explicit decomposition, not a dimension assumption. -/
theorem alternating_slater_expansion {f : TensorVector k r} (hf : alternating f) :
    f = fun x => ∑ I : SubsetIndex k r, f (subsetEnum I) * standardSlater I x := by
  classical
  funext x
  by_cases hx : Function.Injective x
  · obtain ⟨J, σ, heq⟩ := tensorIndex_eq_enum_perm x hx
    have hfσ := congrFun (hf σ) (subsetEnum J)
    have hsσ : ∀ I : SubsetIndex k r,
        standardSlater I x = signC σ * standardSlater I (subsetEnum J) := by
      intro I
      have h := congrFun (slater_alternating (fun j => standardVector (subsetEnum I j)) σ)
        (subsetEnum J)
      simpa only [permute, ← heq, Pi.smul_apply, smul_eq_mul, standardSlater] using h
    simp only [permute, ← heq, Pi.smul_apply, smul_eq_mul] at hfσ
    rw [hfσ]
    simp only [hsσ, standardSlater_evaluation]
    rw [sum_eq_single J]
    · simp [mul_comm]
    · intro I hI hIJ
      simp [hIJ]
    · simp
  · rw [alternating_zero_of_not_injective hf hx]
    simp only [standardSlater_zero_of_not_injective _ hx, mul_zero, sum_const_zero]

end AntisymmetricVerification
