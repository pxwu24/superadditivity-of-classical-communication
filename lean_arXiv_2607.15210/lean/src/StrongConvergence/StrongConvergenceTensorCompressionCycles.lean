import StrongConvergence.StrongConvergenceTensorBlockMoments
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The exact Haar projection compression moment formula, with the input
coordinate sums evaluated as powers of the input dimension. -/

open Matrix MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A] [DecidableEq K]

lemma trace_pow_tensorCycle (M : Matrix A A ℂ) (m : ℕ) :
    Matrix.trace (M ^ (m+1)) = ∑ u : Fin (m+1) → A,
      tensorPower (m+1) M u (fun l => u (finRotate (m+1) l)) := by
  rw [trace_pow_path, sum_fin_cons]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  simp only [tensorPower, pathRows, pathCols, Fin.snoc_eq_cons_rotate]

def weightedCycleMoment {m : ℕ} (a : K → ℝ) (σ : Equiv.Perm (Fin m)) : ℂ :=
  ∑ b : Fin m → K, (∏ l, (a (b l) : ℂ)) *
    (if b = (fun l => b (σ l)) then 1 else 0)

lemma sum_pair_matching {m : ℕ} (γ σ : Equiv.Perm (Fin m)) (b : Fin m → K) :
    (∑ u : Fin m → A,
      if (fun l => (u l, b l)) = (fun l => (u (γ (σ l)), b (σ l))) then (1 : ℂ) else 0) =
      (Fintype.card A : ℂ) ^ cycleCount (γ * σ) *
        (if b = (fun l => b (σ l)) then 1 else 0) := by
  have heq (u : Fin m → A) :
      ((fun l => (u l, b l)) = (fun l => (u (γ (σ l)), b (σ l)))) ↔
        (u = (fun l => u ((γ * σ) l)) ∧ b = (fun l => b (σ l))) := by
    constructor
    · intro h
      exact ⟨funext (fun l => congrArg Prod.fst (congrFun h l)),
        funext (fun l => congrArg Prod.snd (congrFun h l))⟩
    · rintro ⟨hu, hb⟩
      funext l
      exact Prod.ext (congrFun hu l) (congrFun hb l)
  simp_rw [heq]
  by_cases hb : b = fun l => b (σ l)
  · simp only [and_iff_left hb, if_pos hb, mul_one]
    have h := permutationTensor_trace_cycles (E := A) (γ * σ)
    simpa only [Matrix.trace, Matrix.diag_apply, permutationTensor] using h
  · simp [hb]

lemma compression_cycle_sum {m : ℕ} (γ : Equiv.Perm (Fin m))
    (a : K → ℝ) (c : Equiv.Perm (Fin m) → ℂ) :
    (∑ u : Fin m → A, ∑ b : Fin m → K, (∏ l, (a (b l) : ℂ)) *
      ∑ σ : Equiv.Perm (Fin m), c σ *
        (if (fun l => (u l, b l)) = (fun l => (u (γ (σ l)), b (σ l))) then 1 else 0)) =
      ∑ σ : Equiv.Perm (Fin m), c σ *
        (Fintype.card A : ℂ) ^ cycleCount (γ * σ) * weightedCycleMoment a σ := by
  classical
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ u : Fin m → A, ∑ σ : Equiv.Perm (Fin m), ∑ b : Fin m → K,
        (∏ l, (a (b l) : ℂ)) * (c σ *
          (if (fun l => (u l, b l)) = (fun l => (u (γ (σ l)), b (σ l))) then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_comm]
    _ = ∑ σ : Equiv.Perm (Fin m), ∑ u : Fin m → A, ∑ b : Fin m → K,
        (∏ l, (a (b l) : ℂ)) * (c σ *
          (if (fun l => (u l, b l)) = (fun l => (u (γ (σ l)), b (σ l))) then 1 else 0)) := by
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.sum_comm]
      have hfactor :
          (∑ b : Fin m → K, ∑ u : Fin m → A,
            (∏ l, (a (b l) : ℂ)) * (c σ *
              (if (fun l => (u l, b l)) = (fun l => (u (γ (σ l)), b (σ l))) then 1 else 0))) =
          c σ * ∑ b : Fin m → K, (∏ l, (a (b l) : ℂ)) *
            (∑ u : Fin m → A,
              if (fun l => (u l, b l)) = (fun l => (u (γ (σ l)), b (σ l))) then (1 : ℂ) else 0) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro u _
        ring
      rw [hfactor]
      simp_rw [sum_pair_matching]
      simp only [weightedCycleMoment, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- The standard finite permutation formula for all Haar projection compression
trace moments.  The coefficients and both dimension powers are explicit; the
only remaining finite color sum is independent of the input dimension. -/
theorem integral_projection_compression_trace_cycles (m : ℕ)
    (e : Fin (m+1) ↪ A×K) {P : Matrix (A×K) (A×K) ℂ}
    (hP : P.IsHermitian) (hp : P * P = P) (a : K → ℝ) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      Matrix.trace ((blockCompression (diagonalBlock (HaarMoment.orbit P U)) a) ^ (m+1))
        ∂HaarProjection.unitaryHaar) =
      ∑ σ : Equiv.Perm (Fin (m+1)),
        projectionMomentCoefficients (A×K) (m+1) P.rank σ *
          (Fintype.card A : ℂ) ^ cycleCount (finRotate (m+1) * σ) *
          weightedCycleMoment a σ := by
  simp_rw [trace_pow_tensorCycle, tensorPower]
  rw [integral_finset_sum _ (fun u _ =>
    integrable_compression_entry_product P a (m+1) u
      (fun l => u (finRotate (m+1) l)))]
  change (∑ u : Fin (m+1) → A, ∫ U : Matrix.unitaryGroup (A×K) ℂ,
    (∏ l, blockCompression (diagonalBlock (HaarMoment.orbit P U)) a
      (u l) (u (finRotate (m+1) l))) ∂HaarProjection.unitaryHaar) = _
  simp_rw [integral_compression_entry_product (m+1) e P a,
    permutationContractions_tensorPower_projection hP hp]
  exact compression_cycle_sum (finRotate (m+1)) a
    (projectionMomentCoefficients (A×K) (m+1) P.rank)

end ProjectionChannels.TensorHaar

#print axioms ProjectionChannels.TensorHaar.integral_projection_compression_trace_cycles
