import OutputStates.RevisionOutputGeometry
import Mathlib.Analysis.Matrix
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Topology
import Entropy.Defs

/-!
# Continuity of actual density-matrix Rényi entropy

The entropy is defined by the trace of continuous functional calculus. Its
spectral formula is proved using a concrete diagonalization homomorphism.
Continuity descends through the compact space of unitary diagonalizations;
no choice or continuity of ordered eigenvectors is required.
-/

open Matrix PreliminariesMatrix ProjectionChannels RevisionOutput Set
open scoped BigOperators ComplexOrder Topology
noncomputable section
namespace RevisionMatrixEntropy
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 500000
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Diagonal matrices conjugated by a fixed unitary, as a star algebra map. -/
def unitaryConjugateDiagonalHom (U : Matrix.unitaryGroup A ℂ) :
    (A → ℂ) →⋆ₐ[ℝ] Matrix A A ℂ where
  toFun v := (U : Matrix A A ℂ) * Matrix.diagonal v * star (U : Matrix A A ℂ)
  map_one' := by simp [Pi.one_def]
  map_zero' := by simp [Pi.zero_def]
  map_add' v w := by
    change (U:Matrix A A ℂ)*diagonal (fun i => v i+w i)*star (U:Matrix A A ℂ) = _
    rw [← Matrix.diagonal_add]
    simp only [mul_add, add_mul]
  map_mul' v w := by
    rw [show (U : Matrix A A ℂ)*diagonal v*star (U:Matrix A A ℂ) *
      ((U:Matrix A A ℂ)*diagonal w*star (U:Matrix A A ℂ)) =
      (U:Matrix A A ℂ)*diagonal v*(star (U:Matrix A A ℂ)*(U:Matrix A A ℂ))*
        diagonal w*star (U:Matrix A A ℂ) by simp only [mul_assoc]]
    rw [U.prop.1, mul_one, mul_assoc (U:Matrix A A ℂ) (diagonal v) (diagonal w), Matrix.diagonal_mul_diagonal]
    rfl
  commutes' r := by
    change (U:Matrix A A ℂ)*diagonal (fun _ : A => (r:ℂ))*star (U:Matrix A A ℂ) = _
    rw [← Matrix.scalar_apply, Matrix.scalar_apply]
    simp [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Algebra.algebraMap_eq_smul_one]
  map_star' v := by
    simp only [StarMul.star_mul, star_star, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.conjTranspose_conjTranspose, mul_assoc]

def unitaryDiagonal (U : Matrix.unitaryGroup A ℂ) (v : A → ℝ) : Matrix A A ℂ :=
  unitaryConjugateDiagonalHom U (fun i => (v i:ℂ))

lemma unitaryConjugateDiagonalHom_continuous (U : Matrix.unitaryGroup A ℂ) :
    Continuous (unitaryConjugateDiagonalHom U) := by
  change Continuous (fun v : A → ℂ =>
    (U:Matrix A A ℂ)*diagonal v*star (U:Matrix A A ℂ))
  fun_prop

lemma unitaryDiagonal_hermitian (U : Matrix.unitaryGroup A ℂ) (v : A → ℝ) :
    (unitaryDiagonal U v).IsHermitian := by
  change star (unitaryConjugateDiagonalHom U (fun i => (v i:ℂ))) = _
  rw [← map_star]
  congr 1
  ext i
  simp

lemma cfc_unitaryDiagonal (U : Matrix.unitaryGroup A ℂ) (v : A → ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (unitaryDiagonal U v) = unitaryDiagonal U (fun i => f (v i)) := by
  have hv : _root_.IsSelfAdjoint (fun i => (v i:ℂ)) := by ext i; simp [_root_.IsSelfAdjoint]
  have hmap := (unitaryConjugateDiagonalHom U).map_cfc f (fun i => (v i:ℂ)) hf.continuousOn
    (unitaryConjugateDiagonalHom_continuous U) hv (unitaryDiagonal_hermitian U v)
  change cfc f (unitaryConjugateDiagonalHom U (fun i => (v i:ℂ))) = _
  rw [← hmap, cfc_map_pi (S:=ℝ) f (fun i => (v i:ℂ)) hf.continuousOn hv (fun i => by simp [_root_.IsSelfAdjoint])]
  change unitaryConjugateDiagonalHom U _ = unitaryConjugateDiagonalHom U _
  congr 1
  ext i
  exact cfc_algebraMap (R:=ℝ) (A:=ℂ) (v i) f

/-- Sum of a scalar function over the actual matrix spectrum. -/
def spectralTrace (f : ℝ → ℝ) (M : Matrix A A ℂ) : ℝ :=
  (Matrix.trace (cfc f M)).re

lemma spectralTrace_unitaryDiagonal (U : Matrix.unitaryGroup A ℂ) (v : A → ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    spectralTrace f (unitaryDiagonal U v) = ∑ i, f (v i) := by
  rw [spectralTrace, cfc_unitaryDiagonal U v f hf]
  change (Matrix.trace ((U:Matrix A A ℂ)*diagonal (fun i => ((f (v i)):ℂ))*
    star (U:Matrix A A ℂ))).re = _
  rw [Matrix.trace_mul_cycle]
  simp [Matrix.trace_diagonal, Complex.re_sum]

/-- The standard Rényi entropy, with the von Neumann value at p=1. -/
def matrixRenyiEntropy (p : ℝ) (M : Matrix A A ℂ) : ℝ :=
  if p=1 then -spectralTrace (fun x => x*Real.log x) M
  else Real.log (spectralTrace (fun x => x^p) M)/(1-p)

lemma matrixRenyiEntropy_unitaryDiagonal (p : ℝ) (hp : 0 < p)
    (U : Matrix.unitaryGroup A ℂ) (v : A → ℝ) :
    matrixRenyiEntropy p (unitaryDiagonal U v) =
      AppendixB.renyi p Finset.univ (fun _ : A => 1) v := by
  unfold matrixRenyiEntropy AppendixB.renyi
  split_ifs
  · rw [spectralTrace_unitaryDiagonal U v _ Real.continuous_mul_log]
    simp
  · rw [spectralTrace_unitaryDiagonal U v _ (Real.continuous_rpow_const hp.le)]
    simp

variable [Nonempty A]

lemma unitaryDiagonal_density (U : Matrix.unitaryGroup A ℂ) (v : stdSimplex ℝ A) :
    unitaryDiagonal U v ∈ densityMatrices A := by
  constructor
  · have hd : (diagonal (fun i => ((v.val i):ℂ))).PosSemidef := by
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      exact_mod_cast v.property.1 i
    have hh := hd.conjTranspose_mul_mul_same (star (U:Matrix A A ℂ))
    simpa only [unitaryDiagonal, unitaryConjugateDiagonalHom, StarAlgHom.coe_mk,
      AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using hh
  · change Matrix.trace ((U:Matrix A A ℂ)*diagonal (fun i => ((v.val i):ℂ))*star (U:Matrix A A ℂ)) = 1
    rw [Matrix.trace_mul_cycle, U.prop.1, one_mul, Matrix.trace_diagonal]
    exact_mod_cast v.property.2

def diagonalizationMap : Matrix.unitaryGroup A ℂ × stdSimplex ℝ A → densityMatrices A :=
  fun x => ⟨unitaryDiagonal x.1 x.2, unitaryDiagonal_density x.1 x.2⟩

lemma diagonalizationMap_continuous : Continuous (diagonalizationMap (A:=A)) := by
  apply Continuous.subtype_mk
  change Continuous (fun x : Matrix.unitaryGroup A ℂ × stdSimplex ℝ A =>
    (x.1:Matrix A A ℂ)*diagonal (fun i => ((x.2.val i):ℂ))*star (x.1:Matrix A A ℂ))
  apply Continuous.matrix_mul
  · apply Continuous.matrix_mul
    · exact continuous_subtype_val.comp continuous_fst
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      simp only [diagonal_apply]
      split_ifs
      · exact Complex.continuous_ofReal.comp ((continuous_apply i).comp
          (continuous_subtype_val.comp continuous_snd))
      · exact continuous_const
  · exact (continuous_subtype_val.comp continuous_fst).star

lemma diagonalizationMap_surjective : Function.Surjective (diagonalizationMap (A:=A)) := by
  intro ρ
  let h := ρ.property.1.isHermitian
  let v : stdSimplex ℝ A := ⟨h.eigenvalues, ρ.property.1.eigenvalues_nonneg,
    RevisionOutput.density_eigenvalues_sum ρ.property⟩
  refine ⟨⟨h.eigenvectorUnitary, v⟩, ?_⟩
  apply Subtype.ext
  exact h.spectral_theorem.symm

lemma spectralTrace_continuousOn_density (f : ℝ → ℝ) (hf : Continuous f) :
    ContinuousOn (spectralTrace f) (densityMatrices A) := by
  rw [continuousOn_iff_continuous_restrict]
  apply (IsQuotientMap.of_surjective_continuous
    diagonalizationMap_surjective diagonalizationMap_continuous).continuous_iff.mpr
  change Continuous (fun x : Matrix.unitaryGroup A ℂ × stdSimplex ℝ A =>
    spectralTrace f (unitaryDiagonal x.1 x.2))
  simp_rw [spectralTrace_unitaryDiagonal _ _ f hf]
  apply continuous_finset_sum
  intro i _
  exact hf.comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))

lemma simplex_power_sum_pos (p : ℝ) (v : stdSimplex ℝ A) :
    0 < ∑ i, (v.val i)^p := by
  have hex : ∃ i, 0 < v.val i := by
    by_contra hn
    push_neg at hn
    have hsum := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hn i)
    rw [v.property.2] at hsum
    norm_num at hsum
  obtain ⟨i, hi⟩ := hex
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hi p)
    (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (v.property.1 j) p) (Finset.mem_univ i))

lemma density_power_trace_pos (p : ℝ) (hp : 0 < p)
    {ρ : Matrix A A ℂ} (hρ : ρ ∈ densityMatrices A) :
    0 < spectralTrace (fun x => x^p) ρ := by
  obtain ⟨⟨U,v⟩, heq⟩ := diagonalizationMap_surjective (⟨ρ,hρ⟩ : densityMatrices A)
  have heq' : unitaryDiagonal U v = ρ := congrArg Subtype.val heq
  rw [← heq', spectralTrace_unitaryDiagonal U v _ (Real.continuous_rpow_const hp.le)]
  exact simplex_power_sum_pos p v

/-- Rényi entropy is continuous on the full state space, including singular states,
for every positive finite order. -/
theorem matrixRenyiEntropy_continuousOn (p : ℝ) (hp : 0 < p) :
    ContinuousOn (matrixRenyiEntropy p) (densityMatrices A) := by
  unfold matrixRenyiEntropy
  split_ifs with hp1
  · exact (spectralTrace_continuousOn_density _ Real.continuous_mul_log).neg
  · apply ContinuousOn.div_const
    apply ContinuousOn.log
    · exact spectralTrace_continuousOn_density _ (Real.continuous_rpow_const hp.le)
    · intro ρ hρ
      exact (density_power_trace_pos p hp hρ).ne'

/-- Compactness upgrades continuity to the uniform continuity needed for
Hausdorff convergence of minimum output entropies. -/
theorem matrixRenyiEntropy_uniformContinuousOn (p : ℝ) (hp : 0 < p) :
    UniformContinuousOn (matrixRenyiEntropy p) (densityMatrices A) :=
  RevisionOutput.isCompact_densityMatrices.uniformContinuousOn_of_continuous
    (matrixRenyiEntropy_continuousOn p hp)

end RevisionMatrixEntropy
