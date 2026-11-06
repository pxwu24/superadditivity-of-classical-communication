import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open Real Finset
noncomputable section
namespace AppendixB


/-- Rényi entropy of the spectrum in which the value `ν j` has multiplicity `d j`. -/
def renyi (p : ℝ) {ι : Type*} (s : Finset ι) (d ν : ι → ℝ) : ℝ :=
  if p = 1 then -∑ j ∈ s, d j * (ν j * Real.log (ν j))
  else Real.log (∑ j ∈ s, d j * ν j ^ p) / (1 - p)

/-- `ψ_p` of (app-psi-F). -/
def psi (p y : ℝ) : ℝ :=
  if p = 1 then (1 + y) * Real.log (1 + y) - y else (1 + y) ^ p - 1 - p * y

/-- `F_p` of (app-psi-F). -/
def Fp (p x : ℝ) : ℝ := if p = 1 then -x else Real.log (1 + x) / (1 - p)

/-- `κ_p = ψ_p''(0)/2`. -/
def kappa (p : ℝ) : ℝ := if p = 1 then 1 / 2 else p * (p - 1) / 2

/-- `c_p = F_p'(0)`. -/
def cp (p : ℝ) : ℝ := if p = 1 then -1 else 1 / (1 - p)

/-- `c_t(u)` of (set-D). -/
def ct (t u : ℝ) : ℝ := (Real.sqrt (t * (1 - u)) - Real.sqrt ((1 - t) * u)) ^ 2

/-- `𝒟_{k,t}` of (set-D). -/
def Dset (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  {u | (∀ i, 0 ≤ u i ∧ u i ≤ 1) ∧ ∑ i, ct t (u i) ≤ 1 / (k : ℝ)}

/-- `Λ_{k,t}` of (def-Lambda-kt): the spectra of the states in `𝒦_{k,t}`. -/
def Lam (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  {q | ∃ u ∈ Dset k t, q = fun i => u i / ∑ j, u j}

/-- The `r`-subsets of `[k]`. -/
def subsets (k r : ℕ) : Finset (Finset (Fin k)) := (Finset.univ : Finset (Fin k)).powersetCard r

/-- Spectrum of `𝓔_{k,r}(ρ)` when `ρ` has spectrum `q` (eigenvalue shuffling). -/
def shuffle (k r : ℕ) (q : Fin k → ℝ) (I : Finset (Fin k)) : ℝ :=
  (∑ i ∈ I, q i) / (Nat.choose (k - 1) (r - 1) : ℝ)

/-- `r_{k,t}` of (app-rkt). -/
def rkt (k : ℕ) (t : ℝ) : ℝ :=
  (k : ℝ) ^ 2 * (1 - t) / ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1)

/-- The two values of `λ^Bell_{k,t}` (multiplicities `1` and `k² - 1`). -/
def alphaB (k : ℕ) (t : ℝ) : ℝ := rkt k t + (1 - rkt k t) / (k : ℝ) ^ 2
def betaB (k : ℕ) (t : ℝ) : ℝ := (1 - rkt k t) / (k : ℝ) ^ 2

/-- Multiplicity `d_m = C(k,m)² - C(k,m-1)²` of Prop. app-spectrum-G. -/
def dm (k m : ℕ) : ℝ :=
  (Nat.choose k m : ℝ) ^ 2 - (if m = 0 then 0 else (Nat.choose k (m - 1) : ℝ) ^ 2)

/-- Eigenvalue `w_m` of `W_{k,r}` (Prop. app-spectrum-W). -/
def wm (k r m : ℕ) : ℝ :=
  ((r : ℝ) - m) * ((k : ℝ) - r - m + 1) / ((k : ℝ) * (Nat.choose (k - 1) (r - 1) : ℝ) ^ 2)

/-- Eigenvalue `ν_m` of `ω_{k,r,t}` (Step 1 of the Bell proof). -/
def bellNu (k r : ℕ) (t : ℝ) (m : ℕ) : ℝ :=
  rkt k t * wm k r m + (1 - rkt k t) / (Nat.choose k r : ℝ) ^ 2

/-- `A_p(t)` of Prop. app-bell-entropy-asymptotics. -/
def Ap (p t : ℝ) : ℝ :=
  if p = 1 then t⁻¹ * Real.log t⁻¹ - t⁻¹ + 1 else (t ^ (-p) - 1 - p * (t⁻¹ - 1)) / (p - 1)

/-- `B_{p,r}(γ)` of Prop. app-antisymmetric-bell-entropy-asymptotics. -/
def Bpr (p r γ : ℝ) : ℝ :=
  if p = 1 then (r ^ 2 + γ) * Real.log (1 + γ / r ^ 2) - γ
  else (p * γ - r ^ 2 * ((1 + γ / r ^ 2) ^ p - 1)) / (1 - p)

end AppendixB
end
