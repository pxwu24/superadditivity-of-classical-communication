import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Notation

/-! Finite kernel-checked certificates for the fourth permutation Gram matrix. -/

namespace ProjectionChannels.TensorHaar

/-- Conjugacy classes of `S₄`, ordered as `1, (12), (12)(34), (123), (1234)`. -/
def fourthClass (σ : Equiv.Perm (Fin 4)) : Fin 5 :=
  if σ = 1 then 0 else
  if σ * σ = 1 then (if ∃ i, σ i = i then 1 else 2)
  else (if ∃ i, σ i = i then 3 else 4)

def fourthCycleNumber (σ : Equiv.Perm (Fin 4)) : Fin 5 :=
  ![4, 3, 2, 2, 1] (fourthClass σ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fourthCycleNumber_certificate :
    ∀ σ : Equiv.Perm (Fin 4),
      (Finset.univ.filter (fun x : Fin 4 → Fin 2 => x = fun i => x (σ i))).card =
        2 ^ (fourthCycleNumber σ).val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fourthClass_symm : ∀ σ : Equiv.Perm (Fin 4),
    fourthClass σ.symm = fourthClass σ := by decide

/-- Finite class/cycle histogram for each row of the fourth Gram matrix. -/
def fourthGramHistogram : Fin 5 → Fin 5 → Fin 5 → ℕ :=
  ![![![0, 0, 0, 0, 1], ![0, 0, 0, 6, 0], ![0, 0, 3, 0, 0], ![0, 0, 8, 0, 0], ![0, 6, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 5, 0, 1], ![0, 2, 0, 1, 0], ![0, 4, 0, 4, 0], ![0, 0, 6, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 4, 0, 2, 0], ![0, 0, 2, 0, 1], ![0, 0, 8, 0, 0], ![0, 2, 0, 4, 0]], ![![0, 0, 1, 0, 0], ![0, 3, 0, 3, 0], ![0, 0, 3, 0, 0], ![0, 0, 7, 0, 1], ![0, 3, 0, 3, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 6, 0, 0], ![0, 1, 0, 2, 0], ![0, 4, 0, 4, 0], ![0, 0, 5, 0, 1]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fourthGramHistogram_certificate :
    ∀ (σ : Equiv.Perm (Fin 4)) (v : Fin 5 × Fin 5),
      (Finset.univ.filter (fun τ : Equiv.Perm (Fin 4) =>
        (fourthClass τ, fourthCycleNumber (τ * σ.symm)) = v)).card =
          fourthGramHistogram (fourthClass σ) v.1 v.2 := by
  decide

end ProjectionChannels.TensorHaar
