import Entropy.Combinatorics
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul

/-! Finite tensor-coordinate proofs for Proposition V.2.

The vectors below are actual complex coordinate vectors on `(Fin r → Fin k)`.
`antisymmetrize` is the signed permutation average, not an assumed projector.
`oneLeg` is the actual action of `X` on one tensor coordinate. The final theorem
proves the compressed one-leg eigenvector identity for Slater vectors formed
from eigenvectors of `X`. No eigenvalue-shuffling hypothesis is used.
-/
noncomputable section
open Finset Equiv
namespace AntisymmetricVerification
variable {k r : ℕ}
abbrev TensorIndex (k r : ℕ) := Fin r → Fin k
abbrev TensorVector (k r : ℕ) := TensorIndex k r → ℂ

def permute (σ : Perm (Fin r)) (f : TensorVector k r) : TensorVector k r :=
  fun x => f (x ∘ σ)

def signC (σ : Perm (Fin r)) : ℂ := ((Perm.sign σ : ℤ) : ℂ)

def antisymmetrize (f : TensorVector k r) : TensorVector k r :=
  fun x => (r.factorial : ℂ)⁻¹ * ∑ σ : Perm (Fin r), signC σ * permute σ f x

def pureTensor (v : Fin r → Fin k → ℂ) : TensorVector k r :=
  fun x => ∏ j, v j (x j)

def slater (v : Fin r → Fin k → ℂ) : TensorVector k r :=
  fun x => Matrix.det (fun i j => v i (x j))

def oneLeg (X : Matrix (Fin k) (Fin k) ℂ) (j : Fin r)
    (f : TensorVector k r) : TensorVector k r :=
  fun x => ∑ a, X (x j) a * f (Function.update x j a)

def allLegs (X : Matrix (Fin k) (Fin k) ℂ) (f : TensorVector k r) : TensorVector k r :=
  fun x => ∑ j, oneLeg X j f x

def alternating (f : TensorVector k r) : Prop :=
  ∀ σ, permute σ f = signC σ • f

lemma signC_mul_self (σ : Perm (Fin r)) : signC σ * signC σ = 1 := by
  unfold signC
  norm_cast
  exact congrArg (fun z : ℤˣ => (z : ℤ)) (Int.units_mul_self (Perm.sign σ))

lemma signC_mul (σ τ : Perm (Fin r)) : signC (σ * τ) = signC σ * signC τ := by
  simp [signC, Perm.sign_mul]

lemma slater_expansion (v : Fin r → Fin k → ℂ) (x : TensorIndex k r) :
    slater v x = ∑ σ : Perm (Fin r), signC σ * pureTensor (v ∘ σ) x := by
  simp [slater, Matrix.det_apply', signC, pureTensor, Function.comp_def]

lemma slater_alternating (v : Fin r → Fin k → ℂ) : alternating (slater v) := by
  intro σ
  funext x
  simpa only [permute, slater, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.submatrix, id_eq, signC] using
    Matrix.det_permute' σ (fun i j => v i (x j))

lemma antisymmetrize_of_alternating {f : TensorVector k r} (hf : alternating f) :
    antisymmetrize f = f := by
  funext x
  simp only [antisymmetrize]
  have h : ∀ σ, signC σ * permute σ f x = f x := by
    intro σ
    rw [hf σ]
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, signC_mul_self, one_mul]
  simp only [h, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hf0 : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  simp [hf0]

lemma antisymmetrize_slater (v : Fin r → Fin k → ℂ) :
    antisymmetrize (slater v) = slater v :=
  antisymmetrize_of_alternating (slater_alternating v)

lemma pureTensor_update (v : Fin r → Fin k → ℂ) (x : TensorIndex k r)
    (j : Fin r) (a : Fin k) :
    pureTensor v (Function.update x j a) =
      v j a * ∏ l ∈ univ.erase j, v l (x l) := by
  unfold pureTensor
  rw [← mul_prod_erase univ (fun l => v l (Function.update x j a l)) (mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro l hl
  rw [Function.update_of_ne (mem_erase.mp hl).1]

lemma oneLeg_pureTensor (X : Matrix (Fin k) (Fin k) ℂ)
    (v : Fin r → Fin k → ℂ) (lam : Fin r → ℂ)
    (hv : ∀ j, X.mulVec (v j) = lam j • v j) (j : Fin r) :
    oneLeg X j (pureTensor v) = lam j • pureTensor v := by
  funext x
  simp only [oneLeg, pureTensor_update, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc]
  rw [← sum_mul]
  have h := congrFun (hv j) (x j)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [h, mul_assoc, mul_prod_erase univ (fun l => v l (x l)) (mem_univ j)]
  rfl

lemma allLegs_pureTensor (X : Matrix (Fin k) (Fin k) ℂ)
    (v : Fin r → Fin k → ℂ) (lam : Fin r → ℂ)
    (hv : ∀ j, X.mulVec (v j) = lam j • v j) :
    allLegs X (pureTensor v) = (∑ j, lam j) • pureTensor v := by
  funext x
  simp only [allLegs, oneLeg_pureTensor X v lam hv, Pi.smul_apply, smul_eq_mul, sum_mul]

lemma allLegs_sum_smul {ι : Type*} [Fintype ι]
    (X : Matrix (Fin k) (Fin k) ℂ) (c : ι → ℂ) (f : ι → TensorVector k r) :
    allLegs X (fun x => ∑ i, c i * f i x) =
      fun x => ∑ i, c i * allLegs X (f i) x := by
  funext x
  simp only [allLegs, oneLeg, mul_sum, sum_mul]
  conv_lhs => enter [2, j]; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro a ha
  ring

/-- The second-quantized one-body operator acts on an actual Slater vector with
 eigenvalue equal to the sum of the occupied one-body eigenvalues. -/
theorem allLegs_slater (X : Matrix (Fin k) (Fin k) ℂ)
    (v : Fin r → Fin k → ℂ) (lam : Fin r → ℂ)
    (hv : ∀ j, X.mulVec (v j) = lam j • v j) :
    allLegs X (slater v) = (∑ j, lam j) • slater v := by
  have hs : slater v = fun x => ∑ σ : Perm (Fin r), signC σ * pureTensor (v ∘ σ) x := by
    funext x
    exact slater_expansion v x
  rw [hs, allLegs_sum_smul]
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro σ hσ
  have hσv : ∀ j, X.mulVec ((v ∘ σ) j) = (lam ∘ σ) j • (v ∘ σ) j := by
    intro j
    exact hv (σ j)
  rw [allLegs_pureTensor X (v ∘ σ) (lam ∘ σ) hσv]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsum : ∑ j, (lam ∘ σ) j = ∑ j, lam j := Equiv.sum_comp σ lam
  rw [hsum]
  ring

lemma antisymmetrize_smul (c : ℂ) (f : TensorVector k r) :
    antisymmetrize (c • f) = c • antisymmetrize f := by
  funext x
  simp only [antisymmetrize, permute, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (signC _) c, mul_assoc]
  rw [← mul_sum]
  ring

lemma permute_oneLeg (σ : Perm (Fin r)) (X : Matrix (Fin k) (Fin k) ℂ)
    (j : Fin r) (f : TensorVector k r) :
    permute σ (oneLeg X j f) = oneLeg X (σ j) (permute σ f) := by
  funext x
  simp only [permute, oneLeg, Function.comp_apply]
  apply sum_congr rfl
  intro a ha
  congr 2
  funext l
  by_cases h : l = j
  · subst l
    simp
  · have hσ : σ l ≠ σ j := fun e => h (σ.injective e)
    simp [Function.update_of_ne h, Function.update_of_ne hσ]

lemma oneLeg_smul (X : Matrix (Fin k) (Fin k) ℂ) (j : Fin r)
    (c : ℂ) (f : TensorVector k r) :
    oneLeg X j (c • f) = c • oneLeg X j f := by
  funext x
  simp only [oneLeg, Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro a ha
  ring

lemma antisymmetrize_oneLeg_formula (X : Matrix (Fin k) (Fin k) ℂ)
    (j : Fin r) {f : TensorVector k r} (hf : alternating f) (x : TensorIndex k r) :
    antisymmetrize (oneLeg X j f) x =
      (r.factorial : ℂ)⁻¹ * ∑ σ : Perm (Fin r), oneLeg X (σ j) f x := by
  change ∀ σ, permute σ f = signC σ • f at hf
  simp only [antisymmetrize, permute_oneLeg, hf, oneLeg_smul, Pi.smul_apply,
    smul_eq_mul, ← mul_assoc, signC_mul_self, one_mul]

/-- Compressing any one tensor factor gives the same operator on alternating
 vectors. This is the two-sign cancellation in equations (57)--(58). -/
theorem antisymmetrize_oneLeg_eq (X : Matrix (Fin k) (Fin k) ℂ)
    (i j : Fin r) {f : TensorVector k r} (hf : alternating f) :
    antisymmetrize (oneLeg X i f) = antisymmetrize (oneLeg X j f) := by
  funext x
  rw [antisymmetrize_oneLeg_formula X i hf, antisymmetrize_oneLeg_formula X j hf]
  congr 1
  let e : Perm (Fin r) ≃ Perm (Fin r) := Equiv.mulRight (Equiv.swap i j)
  apply Fintype.sum_equiv e
  intro σ
  simp [e, Perm.mul_apply]

lemma antisymmetrize_allLegs (X : Matrix (Fin k) (Fin k) ℂ) (f : TensorVector k r) :
    antisymmetrize (allLegs X f) = fun x => ∑ j, antisymmetrize (oneLeg X j f) x := by
  funext x
  simp only [antisymmetrize, permute, allLegs, mul_sum]
  rw [sum_comm]

/-- The exact one-leg Slater eigenvector identity, before the normalization of
 the channel. Both antisymmetrizers are explicitly defined permutation sums. -/
theorem compressed_oneLeg_slater (hr : 0 < r) (X : Matrix (Fin k) (Fin k) ℂ)
    (v : Fin r → Fin k → ℂ) (lam : Fin r → ℂ)
    (hv : ∀ j, X.mulVec (v j) = lam j • v j) (i : Fin r) :
    antisymmetrize (oneLeg X i (antisymmetrize (slater v))) =
      ((∑ j, lam j) / (r : ℂ)) • slater v := by
  rw [antisymmetrize_slater]
  have h := congrArg antisymmetrize (allLegs_slater X v lam hv)
  rw [antisymmetrize_smul, antisymmetrize_slater, antisymmetrize_allLegs] at h
  funext x
  have hx := congrFun h x
  have heq : ∀ j, antisymmetrize (oneLeg X j (slater v)) x =
      antisymmetrize (oneLeg X i (slater v)) x := by
    intro j
    exact congrFun (antisymmetrize_oneLeg_eq X j i (slater_alternating v)) x
  simp only [heq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    Pi.smul_apply, smul_eq_mul] at hx ⊢
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hr0).2
  simpa only [mul_comm] using hx

/-- The channel in its one-leg form (57), acting on tensor vectors. -/
def postprocess (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r)
    (f : TensorVector k r) : TensorVector k r :=
  ((k : ℂ) / (Nat.choose k r : ℂ)) •
    antisymmetrize (oneLeg X i (antisymmetrize f))

lemma channel_normalization (hr : 1 ≤ r) (hrk : r ≤ k) :
    (k : ℂ) / (Nat.choose k r : ℂ) / (r : ℂ) =
      (Nat.choose (k - 1) (r - 1) : ℂ)⁻¹ := by
  have hk : 1 ≤ k := hr.trans hrk
  have hnat : k * Nat.choose (k - 1) (r - 1) = r * Nat.choose k r := by
    exact_mod_cast AppendixB.choose_mul_left hr hk
  have heq : (k : ℂ) * (Nat.choose (k - 1) (r - 1) : ℂ) =
      (r : ℂ) * (Nat.choose k r : ℂ) := by exact_mod_cast hnat
  have hD : (Nat.choose k r : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hrk)
  have hN : (Nat.choose (k - 1) (r - 1) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (Nat.sub_le_sub_right hrk 1))
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  field_simp
  linear_combination heq

/-- Proposition V.2, equation (62), for actual one-body eigenvectors and the
 explicit signed-permutation compression. Orthonormality is unnecessary for
 the eigenvector equation itself. -/
theorem postprocess_slater_eigenvector (hr : 1 ≤ r) (hrk : r ≤ k)
    (X : Matrix (Fin k) (Fin k) ℂ) (v : Fin r → Fin k → ℂ)
    (lam : Fin r → ℂ) (hv : ∀ j, X.mulVec (v j) = lam j • v j) (i : Fin r) :
    postprocess X i (slater v) =
      ((∑ j, lam j) / (Nat.choose (k - 1) (r - 1) : ℂ)) • slater v := by
  unfold postprocess
  rw [compressed_oneLeg_slater hr X v lam hv, smul_smul]
  congr 1
  have h := channel_normalization hr hrk
  calc
    (↑k / ↑(k.choose r)) * ((∑ j, lam j) / ↑r) =
        (∑ j, lam j) * (↑k / ↑(k.choose r) / ↑r) := by ring
    _ = _ := by rw [h]; rfl

lemma postprocess_smul (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r)
    (c : ℂ) (f : TensorVector k r) :
    postprocess X i (c • f) = c • postprocess X i f := by
  simp only [postprocess, antisymmetrize_smul, oneLeg_smul, smul_smul]
  congr 1
  ring

/-- The normalization in (59) leaves the eigenvalue unchanged. -/
theorem postprocess_normalized_slater (hr : 1 ≤ r) (hrk : r ≤ k)
    (X : Matrix (Fin k) (Fin k) ℂ) (v : Fin r → Fin k → ℂ)
    (lam : Fin r → ℂ) (hv : ∀ j, X.mulVec (v j) = lam j • v j) (i : Fin r) :
    postprocess X i (((Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹) • slater v) =
      ((∑ j, lam j) / (Nat.choose (k - 1) (r - 1) : ℂ)) •
        (((Real.sqrt (r.factorial : ℝ) : ℂ)⁻¹) • slater v) := by
  rw [postprocess_smul, postprocess_slater_eigenvector hr hrk X v lam hv]
  exact smul_comm _ _ _

lemma antisymmetrize_alternating (f : TensorVector k r) :
    alternating (antisymmetrize f) := by
  intro τ
  funext x
  simp only [permute, antisymmetrize, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm]
  congr 1
  rw [mul_sum]
  let e : Perm (Fin r) ≃ Perm (Fin r) := Equiv.mulLeft τ
  apply Fintype.sum_equiv e
  intro σ
  simp only [e, Equiv.coe_mulLeft]
  rw [signC_mul]
  simp only [Perm.coe_mul, Function.comp_def]
  rw [← mul_assoc (signC τ), ← mul_assoc (signC τ), signC_mul_self, one_mul]

/-- The explicitly defined signed permutation average is idempotent. -/
theorem antisymmetrize_idempotent (f : TensorVector k r) :
    antisymmetrize (antisymmetrize f) = antisymmetrize f :=
  antisymmetrize_of_alternating (antisymmetrize_alternating f)

/-- The one-leg definition does not depend on the selected tensor factor. -/
theorem postprocess_independent_leg (X : Matrix (Fin k) (Fin k) ℂ)
    (i j : Fin r) (f : TensorVector k r) :
    postprocess X i f = postprocess X j f := by
  unfold postprocess
  rw [antisymmetrize_oneLeg_eq X i j (antisymmetrize_alternating f)]

/-- The sum along the increasing enumeration of a subset is its finite sum. -/
lemma sum_subset_enumeration (I : Finset (Fin k)) (hI : I.card = r) (q : Fin k → ℂ) :
    (∑ j, q (I.orderEmbOfFin hI j)) = ∑ a ∈ I, q a := by
  calc
    (∑ j, q (I.orderEmbOfFin hI j)) = ∑ a : I, q a :=
      Equiv.sum_comp (I.orderIsoOfFin hI).toEquiv (fun a : I => q a)
    _ = ∑ a ∈ I, q a := Finset.sum_coe_sort I q

/-- Equation (62) with the eigenvalue written exactly as `AppendixB.shuffle`,
 the spectrum used in the already checked entropy estimates. -/
theorem subset_shuffling_eigenvector (hr : 1 ≤ r) (hrk : r ≤ k)
    (X : Matrix (Fin k) (Fin k) ℂ) (v : Fin k → Fin k → ℂ) (q : Fin k → ℝ)
    (hv : ∀ a, X.mulVec (v a) = (q a : ℂ) • v a)
    (I : Finset (Fin k)) (hI : I.card = r) (i : Fin r) :
    postprocess X i (slater (fun j => v (I.orderEmbOfFin hI j))) =
      (AppendixB.shuffle k r q I : ℂ) • slater (fun j => v (I.orderEmbOfFin hI j)) := by
  rw [postprocess_slater_eigenvector hr hrk X _
    (fun j => (q (I.orderEmbOfFin hI j) : ℂ)) (fun j => hv _)]
  congr 1
  rw [sum_subset_enumeration I hI (fun a => (q a : ℂ))]
  simp only [AppendixB.shuffle, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

end AntisymmetricVerification
