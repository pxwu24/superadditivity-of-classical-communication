import Antisymmetric.RevisionPostprocessingTransport
import Preliminaries.RevisionTensorComposition

/-! Exact tensor-product transport through complex-linear postprocessing.
These identities hold for all input matrices, independently of positivity. -/
open Matrix PreliminariesMatrix ProjectionChannels RevisionOutput RevisionBell
open AntisymmetricVerification
noncomputable section
namespace RevisionMain
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Product-conjugate channels commute with postprocessing composition. -/
theorem tensor_conjugate_comp
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (E : Matrix B B ℂ →ₗ[ℂ] Matrix C C ℂ)
    (X : Matrix (A×A) (A×A) ℂ) :
    tensorMap (E.comp Φ) (conjugateMap (E.comp Φ)) X =
      tensorMap E (conjugateMap E) (tensorMap Φ (conjugateMap Φ) X) := by
  have hcomp : conjugateLinearMap (E.comp Φ) =
      (conjugateLinearMap E).comp (conjugateLinearMap Φ) := by
    apply LinearMap.ext
    intro Y
    exact congrFun (conjugateMap_comp Φ E) Y
  change tensorMap (E.comp Φ) (conjugateLinearMap (E.comp Φ)) X =
    tensorMap E (conjugateLinearMap E) (tensorMap Φ (conjugateLinearMap Φ) X)
  rw [hcomp, tensorMap_comp]

/-- The same identity for the paper's explicitly locally normalized channel. -/
theorem tensor_conjugate_normalizedChannel_comp [Nonempty A] [Nonempty B]
    (P : Matrix (A×B) (A×B) ℂ) (D : Matrix A A ℂ)
    (E : Matrix B B ℂ →ₗ[ℂ] Matrix C C ℂ)
    (X : Matrix (A×A) (A×A) ℂ) :
    tensorMap (E.comp (normalizedChannel P D))
      (conjugateMap (E.comp (normalizedChannel P D))) X =
      tensorMap E (conjugateMap E)
        (tensorMap (normalizedOutput P D) (conjugateMap (normalizedOutput P D)) X) := by
  rw [tensor_conjugate_comp]
  have h : (normalizedChannel P D : Matrix A A ℂ → Matrix B B ℂ) =
      normalizedOutput P D := funext (normalizedChannel_apply P D)
  rw [h]

/-- At the Bell input, the inner tensor-channel output is exactly the normalized
Choi contraction used in Section IV. -/
theorem postprocessed_normalizedChannel_bell [Nonempty A] [Nonempty B]
    (P : Matrix (A×B) (A×B) ℂ) (D : Matrix A A ℂ)
    (E : Matrix B B ℂ →ₗ[ℂ] Matrix C C ℂ) :
    tensorMap (E.comp (normalizedChannel P D))
      (conjugateMap (E.comp (normalizedChannel P D))) (bellState A) =
      tensorMap E (conjugateMap E) (bellOutput (normalizedChoi P D)) := by
  rw [tensor_conjugate_normalizedChannel_comp, normalizedOutput_bell_eq]

#print axioms tensor_conjugate_comp
#print axioms tensor_conjugate_normalizedChannel_comp
#print axioms postprocessed_normalizedChannel_bell
end RevisionMain
