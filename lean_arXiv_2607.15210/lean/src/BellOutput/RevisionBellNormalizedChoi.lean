import BellOutput.RevisionBellFiniteMoments

/-! Exact bridges between the paper's locally normalized map, its full Choi
matrix, and the block map used in the Bell mixed-moment proof. -/

open Finset PreliminariesMatrix ProjectionChannels RevisionOutput
open scoped BigOperators Matrix.L2OpNorm ComplexOrder
noncomputable section
namespace RevisionBell

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]

def normalizedChoi (P : Matrix (A × B) (A × B) ℂ) (D : Matrix A A ℂ) :=
  Matrix.kronecker D (1 : Matrix B B ℂ) * P * Matrix.kronecker D (1 : Matrix B B ℂ)

theorem normalizedChoi_block (P : Matrix (A × B) (A × B) ℂ)
    (D : Matrix A A ℂ) (i j : B) :
    BellLimitVerification.choiBlock (normalizedChoi P D) i j =
      D*BellLimitVerification.choiBlock P i j*D := by
  ext a b
  simp [normalizedChoi, BellLimitVerification.choiBlock, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
    Finset.sum_mul, Finset.mul_sum]

theorem choiAdjoint_eq_contraction (P : Matrix (A × B) (A × B) ℂ)
    (H : Matrix B B ℂ) : choiAdjoint P H=contraction P H := by
  ext a b
  simp [choiAdjoint, contraction_entry, mul_comm]

theorem contraction_eq_block_sum (P : Matrix (A × B) (A × B) ℂ)
    (H : Matrix B B ℂ) :
    contraction P H=∑ i, ∑ j, H j i • BellLimitVerification.choiBlock P i j := by
  ext a b
  simp [contraction_entry, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    BellLimitVerification.choiBlock, mul_comm]

theorem contraction_normalizedChoi (P : Matrix (A × B) (A × B) ℂ)
    (D : Matrix A A ℂ) (H : Matrix B B ℂ) :
    contraction (normalizedChoi P D) H=D*contraction P H*D := by
  rw [contraction_eq_block_sum, contraction_eq_block_sum]
  simp_rw [normalizedChoi_block]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem choiAdjoint_normalizedChoi (P : Matrix (A × B) (A × B) ℂ)
    (D : Matrix A A ℂ) (H : Matrix B B ℂ) :
    choiAdjoint (normalizedChoi P D) H=D*contraction P H*D := by
  rw [choiAdjoint_eq_contraction, contraction_normalizedChoi]

/-- The map in Eq.(20) is exactly the map reconstructed from the full locally
normalized Choi matrix; this fixes all transpose conventions. -/
theorem channel_normalizedChoi (P : Matrix (A × B) (A × B) ℂ)
    (D : Matrix A A ℂ) (ρ : Matrix A A ℂ) :
    channel (normalizedChoi P D) ρ=normalizedOutput P D ρ := by
  have hpair (H : Matrix B B ℂ) :
      Matrix.trace (H*channel (normalizedChoi P D) ρ)=
        Matrix.trace (H*normalizedOutput P D ρ) := by
    rw [← choi_inversion (normalizedChoi P D) ρ,
      trace_partialTrace_pairing, contraction_normalizedChoi, normalizedOutput_pairing]
  ext i j
  have h := hpair (matrixUnit j i)
  simpa [Matrix.trace, Matrix.diag, Matrix.mul_apply, matrixUnit, ite_and] using h

theorem normalizedChoi_posSemidef
    {P : Matrix (A × B) (A × B) ℂ} (hP : P.PosSemidef)
    (D : Matrix A A ℂ) (hD : D.IsHermitian) (hn : D*traceB P*D=1) :
    (normalizedChoi P D).PosSemidef :=
  (normalized_choi D P hD hP hn).1

/-- Bell evaluation for exactly the locally normalized channel used in the
paper, now identified with the ordinary tensor product of the two maps. -/
theorem normalizedOutput_bell_eq
    (P : Matrix (A × B) (A × B) ℂ) (D : Matrix A A ℂ) :
    tensorMap (normalizedOutput P D)
      (ProjectionChannels.conjugateMap (normalizedOutput P D)) (bellState A)=
      bellOutput (normalizedChoi P D) := by
  have heq : normalizedOutput P D=channel (normalizedChoi P D) :=
    funext fun ρ => (channel_normalizedChoi P D ρ).symm
  rw [heq]
  rfl

end RevisionBell
