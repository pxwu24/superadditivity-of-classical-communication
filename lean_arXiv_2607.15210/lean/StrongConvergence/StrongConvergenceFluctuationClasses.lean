import StrongConvergence.StrongConvergenceFluctuationFinite
import StrongConvergence.StrongConvergenceFourthCoefficients

/-! Explicit fourth-order Haar fluctuations for the canonical ensemble. -/

open Matrix MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {K : Type*} [Fintype K] [DecidableEq K]

theorem secondTrace_square_cycle_sum (n : ℂ) (c : Fin 5 → ℂ) (a : K → ℝ) :
    (∑ σ : Equiv.Perm (Fin 4), c (fourthClass σ) *
      n ^ cycleCount (twoTwoCycle * σ) * weightedCycleMoment a σ) =
      fourthGramRow n (fun j => c j * fourthWeight a j) 2 := by
  simp_rw [weightedCycleMoment_fourth, cycleCount_fourth,
    twoTwoCycle_fourthCycleNumber]
  have h := fourthGramRow_eq_sum n (fun j => c j * fourthWeight a j) twoTwoCycle
  simp_rw [cycleCount_fourth, twoTwoCycle_fourthClass] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro σ _
  ring

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The expected square of the second compression trace is a closed rational
expression in ambient dimension, rank, input dimension, and four power sums. -/
theorem integral_projection_compression_secondTrace_square_explicit
    (e : Fin 4 ↪ A×K) {P : Matrix (A×K) (A×K) ℂ}
    (hP : P.IsHermitian) (hp : P * P = P) (a : K → ℝ) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      (Matrix.trace ((blockCompression (diagonalBlock (HaarMoment.orbit P U)) a)^2))^2
        ∂HaarProjection.unitaryHaar) =
      fourthGramRow (Fintype.card A : ℂ)
        (fun j => fourthCoefficient (Fintype.card (A×K) : ℂ) (P.rank : ℂ) j *
          fourthWeight a j) 2 := by
  rw [integral_projection_compression_secondTrace_square e hP hp a,
    projectionMomentCoefficients_fourth e]
  exact secondTrace_square_cycle_sum _ _ a

end ProjectionChannels.TensorHaar

namespace ProjectionChannels.Canonical
open TensorHaar

theorem integral_compression_secondTrace_square_explicit {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) (hn : 3 ≤ n) (a : Fin k → ℝ) :
    (∫ ω, (Matrix.trace
      ((blockCompression (diagonalBlock (projection k t ω n)) a)^2))^2
        ∂probability k) =
      fourthGramRow ((n:ℂ)+1)
        (fun j => fourthCoefficient ((k:ℂ)*((n:ℂ)+1)) (rankSequence k t n : ℂ) j *
          fourthWeight a j) 2 := by
  let e : Fin 4 ↪ Index k n :=
    { toFun := fun i => (Fin.castLE (by omega) i, ⟨0,hk⟩)
      inj' := by
        intro i j h
        apply Fin.ext
        exact congrArg (fun z : Index k n => z.1.val) h }
  rw [integral_compression_secondTrace_square hk ht0 ht1 n hn a,
    projectionMomentCoefficients_fourth e,
    secondTrace_square_cycle_sum]
  simp only [Index, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  congr 2
  funext j
  congr 2
  ring

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.TensorHaar.weightedCycleMoment_fourth
#print axioms ProjectionChannels.TensorHaar.integral_projection_compression_secondTrace_square_explicit
