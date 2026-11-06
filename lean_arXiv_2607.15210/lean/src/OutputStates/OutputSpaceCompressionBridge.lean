import OutputStates.OutputSpaceMatrix
import Entropy.OutputSpaceBody

/-!
# From compression spectral limits to locally normalized spectral limits

The matrices genuinely grow: term N acts on `Fin (N+1)`. The random
compression limit is an explicit input on a fixed sample path. The normalized
threshold equivalence, feasible-body geometry and limit passage are proved by
the imported modules; none of those conclusions is assumed here.
-/

open Filter Matrix
open scoped Topology BigOperators ComplexOrder

namespace ProjectionChannels
open OutputSpaceVerification
noncomputable section

/-- The deterministic sample-path consequence of the random compression
formula used for diagonal output support functions. -/
theorem normalized_compression_convergence
    {k : ℕ} {t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hthreshold : 1 < (k : ℝ) ^ 2 * t)
    (P : (N : ℕ) → Fin k → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hP : ∀ N i, (P N i).IsHermitian)
    (hA : ∀ N, (blockCompression (P N) (fun _ => 1)).PosDef)
    (hconv : ∀ c : Fin k → ℝ,
      Tendsto (fun N => largestEigenvalue (blockCompression_isHermitian (P N) (hP N) c))
        atTop (𝓝 (bodySupport k t c)))
    (a : Fin k → ℝ) :
    Tendsto (fun N => largestEigenvalue
      (hermitian_sandwich (blockCompression_isHermitian (P N) (hP N) a)
        (hA N).posSemidef.posSemidef_sqrt.isHermitian.inv))
      atTop (𝓝 (normalizedBodySupport k t a)) := by
  apply concrete_normalized_support_tendsto hk ht ht1 hthreshold a
    (fun N z => largestEigenvalue
      (blockCompression_isHermitian (P N) (hP N) (fun i => a i - z)))
  · intro N z
    exact normalized_blockCompression_threshold (P N) (hP N) (hA N) a z
  · intro z
    exact hconv (fun i => a i - z)

end
end ProjectionChannels
