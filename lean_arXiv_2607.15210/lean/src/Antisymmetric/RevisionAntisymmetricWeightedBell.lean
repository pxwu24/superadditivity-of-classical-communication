import Antisymmetric.RevisionAntisymmetricBellBridge
import Antisymmetric.RevisionGramLadder
import Antisymmetric.RevisionSlaterWeightedLadder

/-! Exact normalization of the Bell Gram matrix in the weighted ladder
coordinates used for the multiplicity induction in Proposition B.2. -/

open Matrix PreliminariesMatrix RevisionBell ProjectionChannels
noncomputable section
namespace AntisymmetricVerification
variable {k r : ℕ}

lemma antisymmetric_choose_relation (hk : 0 < k) :
    (k:ℂ) * (Nat.choose (k-1) r:ℂ) =
      (Nat.choose k (r+1):ℂ) * ((r+1:ℕ):ℂ) := by
  have h := Nat.succ_mul_choose_eq (k-1) r
  rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] at h
  exact_mod_cast h

lemma antisymmetric_bell_normalization (hrk : r+1 ≤ k) :
    (k:ℂ)/(Nat.choose k (r+1):ℂ)^2 =
      ((r+1:ℕ):ℂ)^2 / ((k:ℂ)*(Nat.choose (k-1) r:ℂ)^2) := by
  have hk : 0 < k := by omega
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hD : (Nat.choose k (r+1):ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hrk).ne'
  have hN : (Nat.choose (k-1) r:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : r ≤ k-1)).ne'
  apply (div_eq_div_iff (pow_ne_zero 2 hD) (mul_ne_zero hk0 (pow_ne_zero 2 hN))).mpr
  calc
    _ = ((k:ℂ)*(Nat.choose (k-1) r:ℂ))^2 := by ring
    _ = ((Nat.choose k (r+1):ℂ)*((r+1:ℕ):ℂ))^2 := by rw [antisymmetric_choose_relation hk]
    _ = _ := by ring

/-- Bell output as the exact weighted ladder Gram matrix of Proposition B.2. -/
theorem antisymmetricChannel_bell_weighted_gram (hrk : r+1 ≤ k) :
    tensorMap (antisymmetricChannel (k:=k) (r:=r))
      (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) (bellState (Fin k)) =
      (1/((k:ℂ)*(Nat.choose (k-1) r:ℂ)^2)) •
        ((weightedSlaterReduction k r).conjTranspose * weightedSlaterReduction k r) := by
  rw [antisymmetricChannel_bell_gram (by omega), weightedSlaterReduction_gram,
    smul_smul, antisymmetric_bell_normalization hrk]
  congr 1
  ring

/-- The exact postprocessed isotropic state: a scalar shift of the same
weighted Gram operator. -/
theorem antisymmetricChannel_isotropic_weighted_gram (hrk : r+1 ≤ k) (q : ℝ) :
    tensorMap (antisymmetricChannel (k:=k) (r:=r))
      (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) (isotropic (Fin k) q) =
      ((q:ℂ)/((k:ℂ)*(Nat.choose (k-1) r:ℂ)^2)) •
        ((weightedSlaterReduction k r).conjTranspose * weightedSlaterReduction k r) +
      (((1-q:ℝ):ℂ)/(Nat.choose k (r+1):ℂ)^2) • 1 := by
  rw [antisymmetricChannel_isotropic_gram (by omega), weightedSlaterReduction_gram, smul_smul]
  congr 1
  congr 1
  calc
    _ = (q:ℂ)*((k:ℂ)/(Nat.choose k (r+1):ℂ)^2) := by ring
    _ = _ := by rw [antisymmetric_bell_normalization hrk]; ring

/-- The eigenvalues in the finite-dimensional Bell evaluation of B.2. -/
def antisymmetricBellEigenvalue (k r : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  (1-q)/(Nat.choose k (r+1):ℝ)^2 +
    q * ladderValue k (r+1) j / ((k:ℝ)*(Nat.choose (k-1) r:ℝ)^2)

/-- The actual output eigenspaces are precisely the weighted ladder
eigenspaces. Thus the Gram multiplicities apply to the channel output. -/
theorem antisymmetricChannel_isotropic_eigenspace (hrk : r+1 ≤ k)
    (q : ℝ) (hq : q ≠ 0) (j : ℕ) :
    Module.End.eigenspace (Matrix.toLin'
      (tensorMap (antisymmetricChannel (k:=k) (r:=r))
        (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) (isotropic (Fin k) q)))
        (antisymmetricBellEigenvalue k r q j : ℂ) =
      Module.End.eigenspace (Matrix.toLin'
        ((weightedSlaterReduction k r).conjTranspose * weightedSlaterReduction k r))
        (ladderValue k (r+1) j : ℂ) := by
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (show 0 < k by omega).ne'
  have hN : (Nat.choose (k-1) r:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : r ≤ k-1)).ne'
  have hq0 : (q:ℂ) ≠ 0 := by exact_mod_cast hq
  have ha : (q:ℂ)/((k:ℂ)*(Nat.choose (k-1) r:ℂ)^2) ≠ 0 :=
    div_ne_zero hq0 (mul_ne_zero hk0 (pow_ne_zero 2 hN))
  rw [antisymmetricChannel_isotropic_weighted_gram hrk]
  rw [add_comm
    (((q:ℂ)/((k:ℂ)*(Nat.choose (k-1) r:ℂ)^2)) •
      ((weightedSlaterReduction k r).conjTranspose * weightedSlaterReduction k r))
    ((((1-q:ℝ):ℂ)/(Nat.choose k (r+1):ℂ)^2) •
      (1 : Matrix (SubsetIndex k (r+1) × SubsetIndex k (r+1))
        (SubsetIndex k (r+1) × SubsetIndex k (r+1)) ℂ))]
  have he : (antisymmetricBellEigenvalue k r q j : ℂ) =
      (((1-q:ℝ):ℂ)/(Nat.choose k (r+1):ℂ)^2) +
        ((q:ℂ)/((k:ℂ)*(Nat.choose (k-1) r:ℂ)^2)) * (ladderValue k (r+1) j : ℂ) := by
    simp only [antisymmetricBellEigenvalue, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_mul]
    ring
  rw [he, matrix_scalar_shift_eigenspace, matrix_scalar_smul_eigenspace _ _ _ ha]

end AntisymmetricVerification
