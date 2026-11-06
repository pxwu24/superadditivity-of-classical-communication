import RandomCompression.CompressionExtension
import HaarProjections.HaarMeasure

/-!
# Original random-compression target

The proposition below is retained unchanged for comparison with the original
verification target. It is now proved by
`ProjectionChannels.randomCompressionStatement_verified` in
`StrongConvergence.StrongConvergenceHaarPaperCorollaries`.
-/

open Filter Matrix MeasureTheory
open scoped Topology

namespace ProjectionChannels
universe u

/-- Original target: the random compression lemma for every fixed output dimension.
The index m uses input dimension m+1, which is the usual positive-dimension sequence. -/
def randomCompressionStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 0 < k) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (d : ℕ → ℕ)
    (P₀ : (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ)
    (P : Ω → (m : ℕ) → Matrix (Fin (m+1) × Fin k) (Fin (m+1) × Fin k) ℂ)
    (hP₀ : ∀ m, (P₀ m).IsHermitian ∧ P₀ m * P₀ m = P₀ m ∧ (P₀ m).rank = d m)
    (hH : ∀ ω m, (P ω m).IsHermitian)
    (hId : ∀ ω m, P ω m * P ω m = P ω m)
    (hMeas : ∀ m, Measurable (fun ω => P ω m))
    (hLaw : ∀ m, μ.map (fun ω => P ω m) = HaarProjection.haarProjectionLaw (P₀ m))
    (hRatio : Tendsto (fun m => (d m : ℝ) / ((m+1 : ℕ) * k : ℕ)) atTop (𝓝 t)),
    ∀ᵐ ω ∂μ, ∀ a : Fin k → ℝ,
      Tendsto (fun m => largestEigenvalue
        (blockCompression_isHermitian (diagonalBlock (P ω m))
          (fun i => (projection_diagonalBlock_contraction (P ω m) (hH ω m) (hId ω m) i).1.1) a))
        atTop (𝓝 (bernoulliSupport t (k : ℝ) a))

end ProjectionChannels

