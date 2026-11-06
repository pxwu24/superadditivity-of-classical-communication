import StrongConvergence.StrongConvergenceTensorCycles
import StrongConvergence.StrongConvergenceTensorHaarTrace
import HaarProjections.ProjectionOrbit

/-! All-order finite Haar moments of an orthogonal projection, with coefficients
depending only on its rank and the ambient dimension. -/
open Matrix MeasureTheory
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.TensorHaar

variable {E : Type*} [Fintype E] [DecidableEq E] {m : ℕ}

lemma permutation_trace_tensorPower_orbit (P : Matrix E E ℂ)
    (U : Matrix.unitaryGroup E ℂ) (σ : Equiv.Perm (Fin m)) :
    Matrix.trace (permutationTensor (E := E) σ * tensorPower m (HaarMoment.orbit P U)) =
      Matrix.trace (permutationTensor (E := E) σ * tensorPower m P) := by
  rw [tensorPower_orbit]
  calc
    _ = Matrix.trace (tensorPower m (U : Matrix E E ℂ) *
        (permutationTensor (E := E) σ * tensorPower m P) *
        (tensorPower m (U : Matrix E E ℂ)).conjTranspose) := by
      congr 1
      simp only [← Matrix.mul_assoc]
      rw [permutationTensor_commutes_tensorPower]
    _ = _ := by rw [Matrix.trace_mul_cycle,tensorPower_unitary_left,Matrix.one_mul]

/-- A basis-free orthogonal projection contributes one factor of its rank per cycle. -/
theorem permutation_trace_tensorPower_projection {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hp : P*P=P) (σ : Equiv.Perm (Fin m)) :
    Matrix.trace (permutationTensor (E := E) σ * tensorPower m P) =
      (P.rank : ℂ)^cycleCount σ := by
  classical
  let S : Finset E := Finset.univ.filter (fun i => hP.eigenvalues i ≠ 0)
  let D : Matrix E E ℂ := Matrix.diagonal (fun i => if i∈S then (1:ℂ) else 0)
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues) = D := by
    apply congrArg Matrix.diagonal
    funext i
    rcases ProjectionOrbit.eigenvalues_zero_or_one hP hp i with hi | hi
    · simp [D,S,hi]
    · simp [D,S,hi]
  have hdecomp : HaarMoment.orbit D hP.eigenvectorUnitary = P := by
    have hs := hP.spectral_theorem
    rw [hd] at hs
    exact hs.symm
  have hcard : S.card = P.rank := by
    rw [hP.rank_eq_card_non_zero_eigs]
    simp [S,Fintype.card_subtype]
  calc
    _ = Matrix.trace (permutationTensor (E := E) σ * tensorPower m D) := by
      rw [← hdecomp,permutation_trace_tensorPower_orbit]
    _ = (S.card : ℂ)^cycleCount σ := permutation_trace_tensor_diagonal_projection S σ
    _ = _ := by rw [hcard]

/-- The complete contraction vector for a rank-d orthogonal projection. -/
theorem permutationContractions_tensorPower_projection {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hp : P*P=P) :
    permutationContractions (tensorPower m P) =
      fun σ : Equiv.Perm (Fin m) => (P.rank : ℂ)^cycleCount σ.symm := by
  funext σ
  rw [permutationContractions,permutationTensor_conjTranspose]
  exact permutation_trace_tensorPower_projection hP hp σ.symm

#print axioms permutation_trace_tensorPower_projection
#print axioms permutationContractions_tensorPower_projection

end ProjectionChannels.TensorHaar
