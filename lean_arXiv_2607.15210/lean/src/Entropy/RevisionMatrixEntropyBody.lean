import Entropy.RevisionMatrixEntropy
import OutputStates.RevisionOutputContinuousMinimum
import Dimension182.RevisionLemmaC1

/-! Spectral and actual-matrix entropy minima agree. In particular, the
Appendix C certificate applies to every genuine matrix in the limiting body,
and the minimum output entropy of the actual normalized channels converges. -/

open MeasureTheory Filter Set Matrix Metric PreliminariesMatrix ProjectionChannels
open scoped Topology BigOperators ComplexOrder
namespace RevisionMatrixEntropy
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma matrixRenyiEntropy_unitary_conjugate_diagonal {k : ℕ}
    (p : ℝ) (hp : 0<p) (U : Matrix.unitaryGroup (Fin k) ℂ) (v : Fin k → ℝ) :
    matrixRenyiEntropy p ((U : Matrix (Fin k) (Fin k) ℂ)*Matrix.diagonal (fun i => (v i:ℂ))*
      (U : Matrix (Fin k) (Fin k) ℂ).conjTranspose) =
      AppendixB.renyi p Finset.univ (fun _ : Fin k=>1) v :=
  matrixRenyiEntropy_unitaryDiagonal p hp U v

/-- Entropy images of the actual unitarily invariant matrix body and its
spectral body coincide, for every positive finite Rényi order. -/
theorem spectralBody_entropy_image (k : ℕ) (t p : ℝ) (hp : 0<p) :
    matrixRenyiEntropy p '' RevisionOutput.spectralBody k t =
      (AppendixB.renyi p Finset.univ (fun _ : Fin k=>1)) '' AppendixB.Lam k t := by
  ext a
  constructor
  · rintro ⟨M,⟨v,hv,U,rfl⟩,rfl⟩
    refine ⟨v,hv,?_⟩
    exact (matrixRenyiEntropy_unitary_conjugate_diagonal p hp U v).symm
  · rintro ⟨v,hv,rfl⟩
    refine ⟨unitaryDiagonal (1 : Matrix.unitaryGroup (Fin k) ℂ) v,?_,?_⟩
    · exact ⟨v,hv,1,rfl⟩
    · exact matrixRenyiEntropy_unitaryDiagonal p hp 1 v

lemma spectralBody_shannon_image (k : ℕ) (t : ℝ) :
    matrixRenyiEntropy 1 '' RevisionOutput.spectralBody k t =
      finiteShannon '' AppendixB.Lam k t := by
  rw [spectralBody_entropy_image k t 1 (by norm_num)]
  congr 1
  funext v
  simp [AppendixB.renyi,finiteShannon]

/-- Corollary III.1: actual minimum output Rényi entropy tends to the
minimum over the body, with spectral identification proved internally. -/
theorem actual_minimum_output_entropy_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} [NeZero k] {t : ℝ} (hk : 0 < k) (ht : 0 < t) (ht1 : t < 1)
    (hkt : 1 < (k : ℝ)^2*t)
    (P : Ω → (N : ℕ) → Matrix (Fin (N+1) × Fin k) (Fin (N+1) × Fin k) ℂ)
    (hH : ∀ ω N, (P ω N).IsHermitian) (hId : ∀ ω N, P ω N * P ω N = P ω N)
    (hStrong : FullBlockModifiedStrongInput μ k t P hH)
    (p : ℝ) (hp : 0<p) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => sInf (matrixRenyiEntropy p ''
      (RevisionOutput.normalizedOutput (P ω N)
        (RevisionOutput.marginalNormalizer (P ω N)
          (HaarProjection.projection_posSemidef _ (hH ω N) (hId ω N))) ''
            RevisionOutput.densityMatrices (Fin (N+1))))) atTop
        (𝓝 (sInf ((AppendixB.renyi p Finset.univ (fun _ : Fin k=>1)) '' AppendixB.Lam k t))) := by
  have h := RevisionOutput.output_continuous_minimum_limit μ hk ht ht1 hkt P hH hId hStrong
    (matrixRenyiEntropy p) (matrixRenyiEntropy_continuousOn p hp)
  simpa only [spectralBody_entropy_image k t p hp] using h

lemma normalizedFeasible_eq_Lam_182 : K182.normalizedFeasible=AppendixB.Lam 182 K182.t := by
  ext v
  constructor
  · rintro ⟨u,hu0,hu1,hc,hv⟩
    exact ⟨u,⟨fun i=>⟨hu0 i,hu1 i⟩,hc⟩,hv⟩
  · rintro ⟨u,hu,hv⟩
    exact ⟨u,fun i=>(hu.1 i).1,fun i=>(hu.1 i).2,hu.2,hv⟩

/-- The exact Appendix C certificate bounds every matrix in the actual
limiting output body. No spectral-minimizer premise remains. -/
theorem matrix_entropy_gap_182
    {M : Matrix (Fin 182) (Fin 182) ℂ} (hM : M ∈ RevisionOutput.spectralBody 182 K182.t) :
    (477:ℝ)/1000000 < 2*matrixRenyiEntropy 1 M-K182.bellEntropy := by
  have h : matrixRenyiEntropy 1 M ∈ finiteShannon '' AppendixB.Lam 182 K182.t := by
    rw [← spectralBody_shannon_image]
    exact ⟨M,hM,rfl⟩
  obtain ⟨v,hv,heq⟩ := h
  rw [← heq]
  apply ProjectionChannels.RevisionK182.certified_entropy_gap_182
  rwa [normalizedFeasible_eq_Lam_182]

/-- Proposition VI.1, written for the actual matrix-body minimum. Its
infimum is attained by compactness and matrix entropy continuity. -/
theorem proposition_VI_1_body :
    (477:ℝ)/1000000 < 2*sInf (matrixRenyiEntropy 1 '' RevisionOutput.spectralBody 182 K182.t)
      - K182.bellEntropy := by
  have hK := RevisionOutput.isCompact_spectralBody (k:=182) (t:=K182.t)
    (by norm_num) (by norm_num [K182.t]) (by norm_num [K182.t])
  have hKD := RevisionOutput.spectralBody_subset_densityMatrices (k:=182) (t:=K182.t)
    (by norm_num) (by norm_num [K182.t]) (by norm_num [K182.t])
  have hne := RevisionOutput.spectralBody_nonempty (k:=182) (t:=K182.t)
    (by norm_num) (by norm_num [K182.t]) (by norm_num [K182.t])
  have hleast := (hK.image_of_continuousOn
    ((matrixRenyiEntropy_continuousOn 1 (by norm_num)).mono hKD)).isLeast_sInf
      (hne.image (matrixRenyiEntropy 1))
  obtain ⟨M,hM,heq⟩ := hleast.1
  rw [← heq]
  exact matrix_entropy_gap_182 hM

#print axioms actual_minimum_output_entropy_limit
#print axioms matrix_entropy_gap_182
#print axioms proposition_VI_1_body
end
end RevisionMatrixEntropy
