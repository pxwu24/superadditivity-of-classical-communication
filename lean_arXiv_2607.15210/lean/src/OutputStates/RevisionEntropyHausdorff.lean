import Entropy.OutputSpace

/-! Continuous entropy minimization ignores a finite prefix of output sets.
This version only requires the outputs to be density matrices eventually,
as is necessary for locally normalized random projections. -/

open Set Filter
open scoped Topology
noncomputable section
namespace OutputSpaceVerification

/-- Hausdorff convergence transports the actual infimum of a uniformly
continuous objective when the domain containment holds eventually. -/
theorem minimum_value_tendsto_of_hausdorff_eventually
    {X : Type*} [PseudoMetricSpace X] (D K : Set X) (C : ℕ → Set X)
    (F : X → ℝ)
    (hK : IsCompact K) (hneK : K.Nonempty)
    (hC : ∀ n, IsCompact (C n)) (hneC : ∀ n, (C n).Nonempty)
    (hKD : K ⊆ D) (hCD : ∀ᶠ n in atTop, C n ⊆ D)
    (hF : UniformContinuousOn F D)
    (hhaus : Tendsto (fun n => Metric.hausdorffDist (C n) K) atTop (𝓝 0)) :
    Tendsto (fun n => sInf (F '' C n)) atTop (𝓝 (sInf (F '' K))) := by
  classical
  let C' : ℕ → Set X := fun n => if C n ⊆ D then C n else K
  have heq : C' =ᶠ[atTop] C := by
    filter_upwards [hCD] with n hn
    simp only [C',if_pos hn]
  have hC' : ∀ n, IsCompact (C' n) := by
    intro n
    dsimp [C']
    split_ifs
    · exact hC n
    · exact hK
  have hneC' : ∀ n, (C' n).Nonempty := by
    intro n
    dsimp [C']
    split_ifs
    · exact hneC n
    · exact hneK
  have hC'D : ∀ n, C' n ⊆ D := by
    intro n
    dsimp [C']
    split_ifs with hn
    · exact hn
    · exact hKD
  have hhaus' : Tendsto (fun n => Metric.hausdorffDist (C' n) K) atTop (𝓝 0) := by
    apply hhaus.congr'
    filter_upwards [heq] with n hn
    rw [hn]
  have hm := minimum_value_tendsto_of_hausdorff D K C' F hK hneK hC' hneC'
    hKD hC'D hF hhaus'
  apply hm.congr'
  filter_upwards [heq] with n hn
  rw [hn]

end OutputSpaceVerification
