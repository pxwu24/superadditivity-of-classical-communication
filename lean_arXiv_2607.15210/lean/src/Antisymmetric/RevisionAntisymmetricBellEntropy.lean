import Antisymmetric.RevisionAntisymmetricWeightedBell
import Antisymmetric.RevisionHermitianMultiplicity
import Entropy.RevisionMatrixEntropyConjugate
import Antisymmetric.RevisionSlaterSpectrum
import Entropy.BellGeneral

/-! From the actual antisymmetric Bell spectrum to the weighted entropy
formula used in Appendix B. -/

open Matrix Module.End RevisionMatrixEntropy RevisionBell ProjectionChannels
open scoped BigOperators
noncomputable section
namespace AntisymmetricVerification

variable {A J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype J] [DecidableEq J]

lemma matrixRenyiEntropy_by_multiplicity (p : ℝ) (hp : 0 < p)
    (M : Matrix A A ℂ) (hM : M.IsHermitian)
    (v : J → ℝ) (hv : Function.Injective v)
    (hfull : ∀ i, ∃ j, hM.eigenvalues i = v j) :
    matrixRenyiEntropy p M = AppendixB.renyi p Finset.univ
      (fun j => (Module.finrank ℂ (eigenspace (Matrix.toLin' M) (v j:ℂ)):ℝ)) v := by
  rw [matrixRenyiEntropy_eq_eigenvalues p hp M hM]
  unfold AppendixB.renyi
  split_ifs
  · simp only [one_mul]
    rw [sum_eigenvalues_by_multiplicity hM v hv hfull (fun x => x*Real.log x)]
  · simp only [one_mul]
    rw [sum_eigenvalues_by_multiplicity hM v hv hfull (fun x => x^p)]

lemma antisymmetricBellEigenvalue_eq_bellNu (k r j : ℕ) (t : ℝ) :
    antisymmetricBellEigenvalue k r (AppendixB.rkt k t) j = AppendixB.bellNu k (r+1) t j := by
  unfold antisymmetricBellEigenvalue AppendixB.bellNu AppendixB.wm ladderValue
  rw [Nat.add_sub_cancel]
  ring

lemma unitaryDiagonal_affine (U : Matrix.unitaryGroup A ℂ) (v : A → ℝ) (a b : ℝ) :
    (a:ℂ) • unitaryDiagonal U v + (b:ℂ) • 1 =
      unitaryDiagonal U (fun i => a*v i+b) := by
  have he : (fun i => ((a*v i+b:ℝ):ℂ)) =
      a • (fun i => (v i:ℂ)) + b • (1 : A → ℂ) := by
    ext i
    simp [smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
  change (a:ℂ) • unitaryConjugateDiagonalHom U (fun i => (v i:ℂ)) + (b:ℂ) • 1 =
    unitaryConjugateDiagonalHom U (fun i => ((a*v i+b:ℝ):ℂ))
  rw [he, map_add, map_smul, map_smul, map_one]
  rfl

/-- Diagonalizing the Gram operator diagonalizes every affine shift of it. -/
lemma matrixRenyiEntropy_affine_spectrum (p : ℝ) (hp : 0 < p)
    (M : Matrix A A ℂ) (hM : M.IsHermitian) (a b : ℝ) :
    matrixRenyiEntropy p ((a:ℂ) • M + (b:ℂ) • 1) =
      AppendixB.renyi p Finset.univ (fun _ : A => 1) (fun i => a*hM.eigenvalues i+b) := by
  have he : M = unitaryDiagonal hM.eigenvectorUnitary hM.eigenvalues := hM.spectral_theorem
  conv_lhs => rw [he, unitaryDiagonal_affine]
  exact matrixRenyiEntropy_unitaryDiagonal p hp _ _

/-- Actual postprocessed isotropic entropy, with proved Gram multiplicities. -/
theorem antisymmetricChannel_isotropic_entropy_ladder {k r : ℕ}
    (hkr : 2*(r+1) ≤ k) (p : ℝ) (hp : 0 < p) (q : ℝ) :
    matrixRenyiEntropy p
      (tensorMap (antisymmetricChannel (k:=k) (r:=r))
        (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) (isotropic (Fin k) q)) =
      AppendixB.renyi p Finset.univ (fun j : Fin (r+2) => (ladderMultiplicity k j:ℝ))
        (fun j : Fin (r+2) => antisymmetricBellEigenvalue k r q j) := by
  letI := subsetIndex_nonempty_of_le (show r+1 ≤ k by omega)
  let a : ℝ := q/((k:ℝ)*(Nat.choose (k-1) r:ℝ)^2)
  let b : ℝ := (1-q)/(Nat.choose k (r+1):ℝ)^2
  have he : tensorMap (antisymmetricChannel (k:=k) (r:=r))
      (conjugateMap (antisymmetricChannel (k:=k) (r:=r))) (isotropic (Fin k) q) =
        (a:ℂ) • slaterLadderGram k (r+1) + (b:ℂ) • 1 := by
    rw [antisymmetricChannel_isotropic_weighted_gram (by omega)]
    simp only [a, b, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_natCast, slaterLadderGram_successor]
  rw [he, matrixRenyiEntropy_affine_spectrum p hp _ (slaterLadderGram_isHermitian k (r+1)) a b]
  have hv (j : ℕ) : a*ladderValue k (r+1) j+b = antisymmetricBellEigenvalue k r q j := by
    simp only [a, b, antisymmetricBellEigenvalue]
    ring
  unfold AppendixB.renyi
  split_ifs
  · simp only [one_mul]
    rw [slaterLadderGram_spectral_sum hkr (fun x => (a*x+b)*Real.log (a*x+b))]
    simp only [hv]
  · simp only [one_mul]
    rw [slaterLadderGram_spectral_sum hkr (fun x => (a*x+b)^p)]
    simp only [hv]

/-- The actual postprocessed Bell-limit entropy equals exactly the finite
weighted spectrum used in Appendix B. This includes p=1. -/
theorem antisymmetricChannel_bell_entropy {k r : ℕ}
    (hkr : 2*(r+1) ≤ k) (p : ℝ) (hp : 0 < p) (t : ℝ) :
    matrixRenyiEntropy p
      (tensorMap (antisymmetricChannel (k:=k) (r:=r))
        (conjugateMap (antisymmetricChannel (k:=k) (r:=r)))
        (isotropic (Fin k) (AppendixB.rkt k t))) =
      AppendixB.renyi p (Finset.range (r+2)) (AppendixB.dm k) (AppendixB.bellNu k (r+1) t) := by
  rw [antisymmetricChannel_isotropic_entropy_ladder hkr p hp]
  have hs (f : ℝ → ℝ) :
      (∑ j : Fin (r+2), (ladderMultiplicity k j:ℝ)*
        f (antisymmetricBellEigenvalue k r (AppendixB.rkt k t) j)) =
      ∑ j ∈ Finset.range (r+2), AppendixB.dm k j * f (AppendixB.bellNu k (r+1) t j) := by
    calc
      _ = ∑ j : Fin (r+2), AppendixB.dm k j * f (AppendixB.bellNu k (r+1) t j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [ladderMultiplicity_cast_eq_dm (by omega : 2*(j:ℕ) ≤ k),
          antisymmetricBellEigenvalue_eq_bellNu]
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun j : ℕ => AppendixB.dm k j * f (AppendixB.bellNu k (r+1) t j)) (r+2)
  unfold AppendixB.renyi
  split_ifs
  · rw [hs (fun x => x*Real.log x)]
  · rw [hs (fun x => x^p)]

/-- Proposition B.2 for the actual postprocessed Bell-limit matrix,
including the quantitative O(k^-3) error and the von Neumann case. -/
theorem antisymmetricChannel_bell_entropy_asymptotics {t p : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) (r : ℕ) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k:ℝ) →
      |matrixRenyiEntropy p
        (tensorMap (antisymmetricChannel (k:=k) (r:=r))
          (conjugateMap (antisymmetricChannel (k:=k) (r:=r)))
          (isotropic (Fin k) (AppendixB.rkt k t))) -
        (2*Real.log (Nat.choose k (r+1)) -
          AppendixB.Bpr p (r+1) ((1-t)/t)/(k:ℝ)^2)| ≤ C/(k:ℝ)^3 := by
  obtain ⟨C,K,h⟩ := AppendixB.bell_output ht0 ht1 hp (r+1) (by omega)
  refine ⟨C, max K ((2*(r+1):ℕ):ℝ), ?_⟩
  intro k hk
  have hkr : 2*(r+1) ≤ k := by exact_mod_cast (le_trans (le_max_right _ _) hk)
  rw [antisymmetricChannel_bell_entropy hkr p hp]
  simpa only [Nat.cast_add, Nat.cast_one] using h k (le_trans (le_max_left _ _) hk)

end AntisymmetricVerification
