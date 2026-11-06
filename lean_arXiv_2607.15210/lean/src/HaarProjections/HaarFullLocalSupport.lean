import HaarProjections.HaarLocalSupport
import HaarProjections.GaussianMatrixLaw

open scoped BigOperators ComplexOrder
open Matrix MeasureTheory PreliminariesMatrix GaussianRank

namespace HaarProjection
noncomputable section

variable {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq D]

/-- Full local rank of a Haar-random projection. All distributional inputs are
proved using an explicit normalized Gaussian law, including unitary invariance,
generic matrix rank, whitening, and uniqueness of the Haar orbit law. -/
theorem ae_haar_projection_partialTrace_rank
    (hd : Fintype.card D ≤ Fintype.card A * Fintype.card B)
    (P₀ : Matrix (A × B) (A × B) ℂ) (hP₀ : P₀.IsHermitian)
    (hp₀ : P₀ * P₀ = P₀) (hr₀ : P₀.rank = Fintype.card D) :
    ∀ᵐ U : Matrix.unitaryGroup (A × B) ℂ ∂(unitaryHaar (E := A × B)),
      (traceB ((U : Matrix (A × B) (A × B) ℂ) * P₀ *
        (U : Matrix (A × B) (A × B) ℂ).conjTranspose)).rank =
          min (Fintype.card A) (Fintype.card B * Fintype.card D) := by
  have hg := ae_matrixGaussian_whitening_rank_inputs A B D hd
  exact haar_local_rank_from_invariant_matrix_law (matrixGaussian (A × B) D)
    (matrixGaussian_unitary_invariant (A × B) D)
    (hg.mono fun _ h => h.1) (hg.mono fun _ h => h.2) P₀ hP₀ hp₀ hr₀

/-- The full local support dimension criterion holds on a probability-one event. -/
theorem ae_haar_projection_partialTrace_posDef_iff
    (hd : Fintype.card D ≤ Fintype.card A * Fintype.card B)
    (P₀ : Matrix (A × B) (A × B) ℂ) (hP₀ : P₀.IsHermitian)
    (hp₀ : P₀ * P₀ = P₀) (hr₀ : P₀.rank = Fintype.card D) :
    ∀ᵐ U : Matrix.unitaryGroup (A × B) ℂ ∂(unitaryHaar (E := A × B)),
      (traceB ((U : Matrix (A × B) (A × B) ℂ) * P₀ *
        (U : Matrix (A × B) (A × B) ℂ).conjTranspose)).PosDef ↔
          Fintype.card A ≤ Fintype.card B * Fintype.card D := by
  have hg := ae_matrixGaussian_whitening_rank_inputs A B D hd
  exact haar_local_support_from_invariant_matrix_law (matrixGaussian (A × B) D)
    (matrixGaussian_unitary_invariant (A × B) D)
    (hg.mono fun _ h => h.1) (hg.mono fun _ h => h.2) P₀ hP₀ hp₀ hr₀

/-- Exact almost-sure strict positivity equivalence as stated in the manuscript. -/
theorem haar_projection_full_local_support_iff
    (hd : Fintype.card D ≤ Fintype.card A * Fintype.card B)
    (P₀ : Matrix (A × B) (A × B) ℂ) (hP₀ : P₀.IsHermitian)
    (hp₀ : P₀ * P₀ = P₀) (hr₀ : P₀.rank = Fintype.card D) :
    (∀ᵐ U : Matrix.unitaryGroup (A × B) ℂ ∂(unitaryHaar (E := A × B)),
      (traceB ((U : Matrix (A × B) (A × B) ℂ) * P₀ *
        (U : Matrix (A × B) (A × B) ℂ).conjTranspose)).PosDef) ↔
          Fintype.card A ≤ Fintype.card B * Fintype.card D := by
  have ha := ae_haar_projection_partialTrace_posDef_iff hd P₀ hP₀ hp₀ hr₀
  constructor
  · intro hp
    obtain ⟨U, hU, hiff⟩ := (hp.and ha).exists
    exact hiff.mp hU
  · intro hn
    exact ha.mono fun _ h => h.mpr hn

/-- Numeric-dimension form of the rank formula in the preliminaries. -/
theorem haar_projection_partialTrace_rank_fin {n k d : ℕ} (hd : d ≤ n * k)
    (P₀ : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
    (hP₀ : P₀.IsHermitian) (hp₀ : P₀ * P₀ = P₀) (hr₀ : P₀.rank = d) :
    ∀ᵐ U : Matrix.unitaryGroup (Fin n × Fin k) ℂ ∂(unitaryHaar (E := Fin n × Fin k)),
      (traceB ((U : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) * P₀ *
        (U : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ).conjTranspose)).rank =
          min n (k * d) := by
  simpa only [Fintype.card_fin] using
    ae_haar_projection_partialTrace_rank (A := Fin n) (B := Fin k) (D := Fin d)
      (by simpa only [Fintype.card_fin] using hd) P₀ hP₀ hp₀
      (by simpa only [Fintype.card_fin] using hr₀)

/-- Numeric-dimension strict positivity criterion in the preliminaries. -/
theorem haar_projection_full_local_support_iff_fin {n k d : ℕ} (hd : d ≤ n * k)
    (P₀ : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
    (hP₀ : P₀.IsHermitian) (hp₀ : P₀ * P₀ = P₀) (hr₀ : P₀.rank = d) :
    (∀ᵐ U : Matrix.unitaryGroup (Fin n × Fin k) ℂ ∂(unitaryHaar (E := Fin n × Fin k)),
      (traceB ((U : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) * P₀ *
        (U : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ).conjTranspose)).PosDef) ↔ n ≤ k * d := by
  simpa only [Fintype.card_fin] using
    haar_projection_full_local_support_iff (A := Fin n) (B := Fin k) (D := Fin d)
      (by simpa only [Fintype.card_fin] using hd) P₀ hP₀ hp₀
      (by simpa only [Fintype.card_fin] using hr₀)

end
end HaarProjection

