import BellOutput.RevisionBellNormalizedChoi
import Preliminaries.CompletePositivity

/-! Positivity and trace preservation of the genuine tensor product of
channels, including the Bell input used in Theorem IV.1 and VI.1. -/

open Matrix PreliminariesMatrix ProjectionChannels ProjectionChannelsCP
open scoped BigOperators ComplexOrder
noncomputable section
namespace RevisionBell
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

lemma linearMap_entry_expansion
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (X : Matrix A A ℂ) (i j : B) :
    Φ X i j = ∑ a, ∑ b, X a b * Φ (matrixUnit a b) i j := by
  have h := congrArg (fun Z => Φ Z i j) (matrixUnit_expansion X)
  simpa only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using h.symm

lemma tensorMap_eq_amplify_swap
    (Φ Ψ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (X : Matrix (A×A) (A×A) ℂ) :
    tensorMap Φ Ψ X =
      (amplify Φ ((amplify Ψ X).submatrix Prod.swap Prod.swap)).submatrix Prod.swap Prod.swap := by
  ext ⟨i,p⟩ ⟨j,q⟩
  change (∑ a, ∑ b, ∑ c, ∑ d,
    X (a,c) (b,d)*Φ (matrixUnit a b) i j*Ψ (matrixUnit c d) p q) =
      Φ (fun a b => Ψ (fun c d => X (a,c) (b,d)) p q) i j
  conv_rhs => rw [linearMap_entry_expansion]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  conv_rhs => rw [linearMap_entry_expansion]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Positivity of the tensor product follows from the two amplifications
and exact index permutations. -/
theorem tensorMap_posSemidef
    (Φ Ψ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ)
    {X : Matrix (A×A) (A×A) ℂ} (hX : X.PosSemidef) :
    (tensorMap Φ Ψ X).PosSemidef := by
  rw [tensorMap_eq_amplify_swap]
  exact (hΦ B _ ((hΨ A X hX).submatrix Prod.swap)).submatrix Prod.swap

lemma trace_amplify
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (hΦ : TracePreserving Φ)
    (X : Matrix (C×A) (C×A) ℂ) : Matrix.trace (amplify Φ X)=Matrix.trace X := by
  simp only [Matrix.trace,Matrix.diag,Fintype.sum_prod_type,amplify]
  apply Finset.sum_congr rfl
  intro c _
  exact hΦ (fun a b=>X (c,a) (c,b))

lemma trace_submatrix_swap (X : Matrix (A×B) (A×B) ℂ) :
    Matrix.trace (X.submatrix Prod.swap Prod.swap)=Matrix.trace X := by
  simp only [Matrix.trace,Matrix.diag,Matrix.submatrix_apply,Fintype.sum_prod_type,Prod.swap_prod_mk]
  exact Finset.sum_comm

/-- The tensor product of trace-preserving maps is trace preserving. -/
theorem tensorMap_trace
    (Φ Ψ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hΦ : TracePreserving Φ) (hΨ : TracePreserving Ψ)
    (X : Matrix (A×A) (A×A) ℂ) : Matrix.trace (tensorMap Φ Ψ X)=Matrix.trace X := by
  rw [tensorMap_eq_amplify_swap,trace_submatrix_swap,trace_amplify Φ hΦ,
    trace_submatrix_swap,trace_amplify Ψ hΨ]

lemma channel_entrywiseConjugate (J : Matrix (A×B) (A×B) ℂ) :
    channel (entrywiseConjugate J)=conjugateMap (channel J) := by
  funext X
  ext i j
  simp [channel,conjugateMap,entrywiseConjugate,map_sum,map_mul,mul_comm]

lemma entrywiseConjugate_posSemidef {J : Matrix A A ℂ} (hJ : J.PosSemidef) :
    (entrywiseConjugate J).PosSemidef := by
  have heq : entrywiseConjugate J=J.transpose := by
    ext a b
    exact hJ.isHermitian.apply b a
  rw [heq]
  exact hJ.transpose

lemma traceB_entrywiseConjugate (J : Matrix (A×B) (A×B) ℂ) :
    traceB (entrywiseConjugate J)=entrywiseConjugate (traceB J) := by
  ext a b
  simp [traceB,entrywiseConjugate]

lemma choiChannel_CP_TP {J : Matrix (A×B) (A×B) ℂ}
    (hJ : J.PosSemidef) (hT : traceB J=1) :
    CompletelyPositive (choiChannel J) ∧ TracePreserving (choiChannel J) := by
  rw [quantumChannel_iff_choi,choiInput_choiChannel]
  exact ⟨hJ,hT⟩

lemma bellState_eq_scaled_column :
    bellState A=(1/(Fintype.card A : ℂ)) •
      (bellColumn (A:=A)*(bellColumn (A:=A)).conjTranspose) := by
  ext ⟨a,c⟩ ⟨b,d⟩
  simp [bellState,bellColumn,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.smul_apply,smul_eq_mul,ite_and]
  split_ifs <;> rfl

lemma bellState_posSemidef : (bellState A).PosSemidef := by
  rw [bellState_eq_scaled_column]
  have hs : (1/(Fintype.card A : ℂ))=((1/(Fintype.card A : ℝ) : ℝ) : ℂ) := by simp
  rw [hs]
  exact posSemidef_real_smul _ (Matrix.posSemidef_self_mul_conjTranspose _)
    (1/(Fintype.card A : ℝ)) (by positivity)

lemma bellState_trace [Nonempty A] : Matrix.trace (bellState A)=1 := by
  have hcard : (Fintype.card A : ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp [Matrix.trace,Matrix.diag,bellState,Fintype.sum_prod_type,hcard]

/-- The actual normalized Bell matrix is a density matrix. -/
theorem bellState_mem_densityMatrices [Nonempty A] :
    bellState A ∈ RevisionOutput.densityMatrices (A×A) := by
  exact ⟨bellState_posSemidef,bellState_trace⟩

/-- A positive normalized Choi operator sends every product input density
matrix to a product-channel output density matrix. -/
theorem tensor_choi_conjugate_mem_densityMatrices
    {J : Matrix (A×B) (A×B) ℂ} (hJ : J.PosSemidef) (hT : traceB J=1)
    {X : Matrix (A×A) (A×A) ℂ} (hX : X ∈ RevisionOutput.densityMatrices (A×A)) :
    tensorMap (channel J) (conjugateMap (channel J)) X ∈
      RevisionOutput.densityMatrices (B×B) := by
  have hc := choiChannel_CP_TP hJ hT
  have hTc : traceB (entrywiseConjugate J)=1 := by
    rw [traceB_entrywiseConjugate,hT]
    ext a b
    simp [entrywiseConjugate,Matrix.one_apply]
  have hcc := choiChannel_CP_TP (entrywiseConjugate_posSemidef hJ) hTc
  rw [← channel_entrywiseConjugate]
  exact ⟨tensorMap_posSemidef (choiChannel J) (choiChannel (entrywiseConjugate J)) hc.1 hcc.1 hX.1,
    (tensorMap_trace (choiChannel J) (choiChannel (entrywiseConjugate J)) hc.2 hcc.2 X).trans hX.2⟩

/-- Density of the Bell output in the paper, with all positivity and trace
properties proved from the actual matrix formula. -/
theorem normalizedOutput_bell_mem_densityMatrices [Nonempty A] [Nonempty B]
    {P : Matrix (A×B) (A×B) ℂ} (hP : P.PosSemidef)
    (D : Matrix A A ℂ) (hD : D.IsHermitian) (hn : D*traceB P*D=1) :
    tensorMap (RevisionOutput.normalizedOutput P D)
      (conjugateMap (RevisionOutput.normalizedOutput P D)) (bellState A) ∈
        RevisionOutput.densityMatrices (B×B) := by
  rw [normalizedOutput_bell_eq]
  exact tensor_choi_conjugate_mem_densityMatrices
    (normalizedChoi_posSemidef hP D hD hn) (normalized_choi D P hD hP hn).2
    bellState_mem_densityMatrices

end RevisionBell
