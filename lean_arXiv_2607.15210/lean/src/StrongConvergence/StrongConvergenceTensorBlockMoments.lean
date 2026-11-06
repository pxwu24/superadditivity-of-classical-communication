import StrongConvergence.StrongConvergenceTensorWeingarten
import StrongConvergence.StrongConvergenceHaarSecondCompression
import Mathlib.Algebra.BigOperators.Fin

/-! Exact finite Haar moments of every order for diagonal block compressions.
All matrix-power and block-entry expansions are proved here; the final formula
contains only finite sums and the explicitly defined permutation Gram inverse. -/

open Matrix MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A] [DecidableEq K]

def pathRows {m : ℕ} (i : A) (x : Fin m → A) : Fin (m+1) → A := Fin.cons i x
def pathCols {m : ℕ} (x : Fin m → A) (j : A) : Fin (m+1) → A := Fin.snoc x j

lemma sum_fin_cons {m : ℕ} (f : (Fin (m+1) → A) → ℂ) :
    (∑ x, f x) = ∑ a, ∑ y : Fin m → A, f (Fin.cons a y) := by
  simpa [Fintype.sum_prod_type] using
    ((Fin.consEquiv (fun _ : Fin (m+1) => A)).sum_comp f).symm

/-- Finite path expansion of a matrix power. -/
lemma matrix_pow_path (M : Matrix A A ℂ) (m : ℕ) (i j : A) :
    (M ^ (m+1)) i j =
      ∑ x : Fin m → A, ∏ l : Fin (m+1), M (pathRows i x l) (pathCols x j l) := by
  induction m generalizing i with
  | zero => simp [pathRows, pathCols, Fin.snoc]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply, sum_fin_cons]
    apply Finset.sum_congr rfl
    intro a _
    rw [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [pathRows, pathCols]
    rw [← Fin.cons_snoc_eq_snoc_cons]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]

lemma trace_pow_path (M : Matrix A A ℂ) (m : ℕ) :
    Matrix.trace (M ^ (m+1)) =
      ∑ i : A, ∑ x : Fin m → A,
        ∏ l : Fin (m+1), M (pathRows i x l) (pathCols x i l) := by
  simp only [Matrix.trace, Matrix.diag_apply, matrix_pow_path]

lemma tensorPower_compression (P : Matrix (A×K) (A×K) ℂ) (a : K → ℝ)
    (m : ℕ) (u v : Fin m → A) :
    tensorPower m (blockCompression (diagonalBlock P) a) u v =
      ∑ b : Fin m → K, (∏ l, (a (b l) : ℂ)) *
        tensorPower m P (fun l => (u l, b l)) (fun l => (v l, b l)) := by
  simp only [tensorPower, HaarMoment.compression_entry]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.prod_mul_distrib

lemma integral_tensorPower_compression (P : Matrix (A×K) (A×K) ℂ)
    (a : K → ℝ) (m : ℕ) (u v : Fin m → A) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      tensorPower m (blockCompression (diagonalBlock (HaarMoment.orbit P U)) a) u v
        ∂HaarProjection.unitaryHaar) =
      ∑ b : Fin m → K, (∏ l, (a (b l) : ℂ)) *
        tensorHaarMoment m P (fun l => (u l, b l)) (fun l => (v l, b l)) := by
  simp_rw [tensorPower_compression]
  rw [integral_finset_sum _ (fun b _ =>
    (integrable_tensorPower_orbit_entry m P _ _).const_mul _)]
  simp only [integral_const_mul, tensorHaarMoment]

/-- Every mixed compression entry moment is evaluated by finite inverse Gram
coefficients.  The dimension condition is the only restriction on the order. -/
theorem integral_compression_entry_product (m : ℕ) (e : Fin m ↪ A×K)
    (P : Matrix (A×K) (A×K) ℂ) (a : K → ℝ) (u v : Fin m → A) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      (∏ l, blockCompression (diagonalBlock (HaarMoment.orbit P U)) a (u l) (v l))
        ∂HaarProjection.unitaryHaar) =
      ∑ b : Fin m → K, (∏ l, (a (b l) : ℂ)) *
        ∑ σ : Equiv.Perm (Fin m),
          ((permutationGram (A×K) m)⁻¹ *ᵥ permutationContractions (tensorPower m P)) σ *
            (if (fun l => (u l, b l)) = (fun l => (v (σ l), b (σ l))) then 1 else 0) := by
  change (∫ U : Matrix.unitaryGroup (A×K) ℂ,
    tensorPower m (blockCompression (diagonalBlock (HaarMoment.orbit P U)) a) u v
      ∂HaarProjection.unitaryHaar) = _
  rw [integral_tensorPower_compression, tensorHaarMoment_weingarten e P]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, permutationTensor]

lemma integrable_compression_entry_product (P : Matrix (A×K) (A×K) ℂ)
    (a : K → ℝ) (m : ℕ) (u v : Fin m → A) :
    Integrable (fun U : Matrix.unitaryGroup (A×K) ℂ =>
      ∏ l, blockCompression (diagonalBlock (HaarMoment.orbit P U)) a (u l) (v l))
      HaarProjection.unitaryHaar := by
  change Integrable (fun U : Matrix.unitaryGroup (A×K) ℂ =>
    tensorPower m (blockCompression (diagonalBlock (HaarMoment.orbit P U)) a) u v) _
  simp_rw [tensorPower_compression]
  exact integrable_finset_sum _ (fun b _ =>
    (integrable_tensorPower_orbit_entry m P _ _).const_mul _)

/-- Exact expected trace of every positive power of a Haar block compression.
This proves an all-order finite-moment formula, without assuming convergence
of any moments or the limiting free probability law. -/
theorem integral_compression_trace_power (m : ℕ) (e : Fin (m+1) ↪ A×K)
    (P : Matrix (A×K) (A×K) ℂ) (a : K → ℝ) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      Matrix.trace ((blockCompression (diagonalBlock (HaarMoment.orbit P U)) a) ^ (m+1))
        ∂HaarProjection.unitaryHaar) =
      ∑ i : A, ∑ x : Fin m → A, ∑ b : Fin (m+1) → K,
        (∏ l, (a (b l) : ℂ)) *
          ∑ σ : Equiv.Perm (Fin (m+1)),
            ((permutationGram (A×K) (m+1))⁻¹ *ᵥ
              permutationContractions (tensorPower (m+1) P)) σ *
              (if (fun l => (pathRows i x l, b l)) =
                (fun l => (pathCols x i (σ l), b (σ l))) then 1 else 0) := by
  simp_rw [trace_pow_path]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun x _ =>
    integrable_compression_entry_product P a (m+1) (pathRows i x) (pathCols x i)))]
  simp_rw [integral_finset_sum _ (fun x _ =>
    integrable_compression_entry_product P a (m+1) (pathRows _ x) (pathCols x _)),
      integral_compression_entry_product (m+1) e P a]

/-- All finite Haar projection compression moments, with coefficients depending
only on the projection rank and the ambient dimension. -/
theorem integral_projection_compression_trace_power (m : ℕ)
    (e : Fin (m+1) ↪ A×K) {P : Matrix (A×K) (A×K) ℂ}
    (hP : P.IsHermitian) (hp : P * P = P) (a : K → ℝ) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      Matrix.trace ((blockCompression (diagonalBlock (HaarMoment.orbit P U)) a) ^ (m+1))
        ∂HaarProjection.unitaryHaar) =
      ∑ i : A, ∑ x : Fin m → A, ∑ b : Fin (m+1) → K,
        (∏ l, (a (b l) : ℂ)) *
          ∑ σ : Equiv.Perm (Fin (m+1)),
            projectionMomentCoefficients (A×K) (m+1) P.rank σ *
              (if (fun l => (pathRows i x l, b l)) =
                (fun l => (pathCols x i (σ l), b (σ l))) then 1 else 0) := by
  rw [integral_compression_trace_power m e P a,
    permutationContractions_tensorPower_projection hP hp]
  rfl

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.integral_compression_entry_product
#print axioms ProjectionChannels.TensorHaar.integral_compression_trace_power
#print axioms ProjectionChannels.TensorHaar.integral_projection_compression_trace_power
