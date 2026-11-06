import StrongConvergence.StrongConvergenceTensorCanonical

/-!
# Finite two-trace Haar moments for compression fluctuations

The existing single-trace formula extends to an arbitrary permutation of the
tensor positions. In particular, two disjoint two-cycles compute the square
of the second trace, the fourth-order input needed for its variance. These
are exact finite-dimensional identities, not concentration assumptions.
-/

open Matrix MeasureTheory
open scoped BigOperators
noncomputable section

namespace ProjectionChannels.TensorHaar

variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A] [DecidableEq K]

/-- Tensor contraction associated with an arbitrary permutation of positions.
One cycle gives one trace; disjoint cycles give a product of traces. -/
def permutationTrace {m : ℕ} (M : Matrix A A ℂ) (γ : Equiv.Perm (Fin m)) : ℂ :=
  ∑ u : Fin m → A, ∏ l, M (u l) (u (γ l))

lemma permutationTrace_finRotate (M : Matrix A A ℂ) (m : ℕ) :
    permutationTrace M (finRotate (m+1)) = Matrix.trace (M ^ (m+1)) := by
  exact (trace_pow_tensorCycle M m).symm

/-- An arbitrary trace contraction of a Haar projection compression has an
exact permutation-cycle formula. The permutation need not be one cycle. -/
theorem integral_projection_compression_permutationTrace (m : ℕ)
    (e : Fin m ↪ A×K) {P : Matrix (A×K) (A×K) ℂ}
    (hP : P.IsHermitian) (hp : P * P = P) (a : K → ℝ)
    (γ : Equiv.Perm (Fin m)) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      permutationTrace (blockCompression (diagonalBlock (HaarMoment.orbit P U)) a) γ
        ∂HaarProjection.unitaryHaar) =
      ∑ σ : Equiv.Perm (Fin m),
        projectionMomentCoefficients (A×K) m P.rank σ *
          (Fintype.card A : ℂ) ^ cycleCount (γ * σ) *
          weightedCycleMoment a σ := by
  simp only [permutationTrace]
  rw [integral_finset_sum _ (fun u _ =>
    integrable_compression_entry_product P a m u (fun l => u (γ l)))]
  simp_rw [integral_compression_entry_product m e P a,
    permutationContractions_tensorPower_projection hP hp]
  exact compression_cycle_sum γ a (projectionMomentCoefficients (A×K) m P.rank)

/-- The permutation with cycles `(0 1)` and `(2 3)`. -/
def twoTwoCycle : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

lemma permutationTrace_twoTwoCycle (M : Matrix A A ℂ) :
    permutationTrace M twoTwoCycle = (Matrix.trace (M^2))^2 := by
  simp only [permutationTrace]
  rw [sum_fin_cons]
  simp_rw [sum_fin_cons]
  simp [Fin.prod_univ_succ, Fin.cons, Fin.cons_zero, Fin.cons_succ, twoTwoCycle,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, pow_two, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change M i j * (M j i * (M k l * M l k)) =
    M k l * (M l k * (M i j * M j i))
  ring

/-- Exact fourth-order Haar formula for the square of the second trace. -/
theorem integral_projection_compression_secondTrace_square
    (e : Fin 4 ↪ A×K) {P : Matrix (A×K) (A×K) ℂ}
    (hP : P.IsHermitian) (hp : P * P = P) (a : K → ℝ) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      (Matrix.trace ((blockCompression (diagonalBlock (HaarMoment.orbit P U)) a)^2))^2
        ∂HaarProjection.unitaryHaar) =
      ∑ σ : Equiv.Perm (Fin 4),
        projectionMomentCoefficients (A×K) 4 P.rank σ *
          (Fintype.card A : ℂ) ^ cycleCount (twoTwoCycle * σ) *
          weightedCycleMoment a σ := by
  simp_rw [← permutationTrace_twoTwoCycle]
  exact integral_projection_compression_permutationTrace 4 e hP hp a twoTwoCycle

end ProjectionChannels.TensorHaar

namespace ProjectionChannels.Canonical
open TensorHaar

/-- Fourth-order second-trace-square formula for the actual product Haar
probability space, with the dimension condition supplied explicitly. -/
theorem integral_compression_secondTrace_square {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) (hn : 3 ≤ n) (a : Fin k → ℝ) :
    (∫ ω, (Matrix.trace
      ((blockCompression (diagonalBlock (projection k t ω n)) a)^2))^2
        ∂probability k) =
      ∑ σ : Equiv.Perm (Fin 4),
        projectionMomentCoefficients (Index k n) 4 (rankSequence k t n) σ *
          ((n+1 : ℕ) : ℂ) ^ cycleCount (twoTwoCycle * σ) *
          weightedCycleMoment a σ := by
  let e : Fin 4 ↪ Index k n :=
    { toFun := fun i => (Fin.castLE (by omega) i, ⟨0,hk⟩)
      inj' := by
        intro i j h
        apply Fin.ext
        exact congrArg (fun z : Index k n => z.1.val) h }
  change (∫ ω, (Matrix.trace ((blockCompression (diagonalBlock
    (HaarMoment.orbit (baseProjection k t n) (evaluation k n ω))) a)^2))^2
      ∂probability k) = _
  rw [integral_evaluation_continuous k n _
    ((continuous_compression_trace_power (baseProjection k t n) a 1).pow 2),
    TensorHaar.integral_projection_compression_secondTrace_square e
      (baseProjection_isHermitian k t n) (baseProjection_idempotent k t n) a,
    baseProjection_rank ht0 ht1]
  simp only [Fintype.card_fin]

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.TensorHaar.integral_projection_compression_permutationTrace
#print axioms ProjectionChannels.TensorHaar.integral_projection_compression_secondTrace_square
#print axioms ProjectionChannels.Canonical.integral_compression_secondTrace_square
