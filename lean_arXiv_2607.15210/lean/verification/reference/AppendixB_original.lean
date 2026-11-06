/-
  AppendixB.lean — Lean 4 / Mathlib formalization of Appendix B ("Entropy asymptotics").

  STATUS: written without access to a Lean toolchain; NOT YET COMPILED.
  Please run `lake env lean AppendixB.lean` in a Mathlib project and report the first error.

  SCOPE.  Every proposition of Appendix B is formalized at the level of spectra, which is
  where all four large-k estimates live.  The two operator-level inputs, namely eigenvalue
  shuffling (Prop. eigenvalue-shuffling) and the spectrum of W_{k,r}
  (Props. app-one-body-twirl, app-lift-reduce, app-spectrum-G, app-spectrum-W), are proved
  in the LaTeX only; here they enter through the explicit spectra `shuffle` and `bellNu`.
  The combinatorial facts behind them are formalized (`trace_identity`, `mult_sum`,
  `eig_recursion`, `quadratic_form`, `sum_over_subsets`).

    Appendix B                                    Lean
    --------------------------------------------  -------------------------------------
    (app-cp-kappa)                                `cp_mul_kappa`
    Prop. app-exact-expansion                     `exact_expansion`
    Prop. app-local-bounds (i), (ii), (iii)       `psi_local`, `Fp_local`, `psi_lip`, `psi_bdd`
    Prop. app-uniform-expansion                   `uniform_expansion`
    Prop. app-shuffled-spectrum                   `shuffle_repr`, `sum_over_subsets`,
                                                  `quadratic_form`
    Prop. app-localization, (app-ct-bound)        `ct_bound`, `localization`, `two_spike`
    Prop. app-single-entropy-asymptotics   (26)   `single_output_r1`
    Prop. app-antisymmetric-single-...     (65)   `single_output`
    Prop. app-bell-entropy-asymptotics     (44)   `bell_output_r1`
    Prop. app-antisymmetric-bell-...       (68)   `bell_output`
    (app-B-identity), B_{p,1}(γ) = A_p(t)         `B_identity`, `B_one_eq_A`
    Prop. app-spectrum-G (arithmetic step)        `eig_recursion`
    Prop. app-spectrum-W (trace and dimension)    `trace_identity`, `mult_sum`

  Conventions.  `k : ℕ` is the dimension and every estimate is stated as
  "∃ C k₀, ∀ k ≥ k₀, ...", which is the O(·) statement of the appendix.  A spectrum is a
  finite family of values `ν j` with multiplicities `d j`.
-/
import Mathlib

open Real Finset

noncomputable section

namespace AppendixB

/-! ## 1. Definitions -/

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

lemma renyi_congr (p : ℝ) {ι : Type*} (s : Finset ι) (d ν ν' : ι → ℝ)
    (h : ∀ j ∈ s, ν j = ν' j) : renyi p s d ν = renyi p s d ν' := by
  unfold renyi
  split_ifs
  · rw [Finset.sum_congr rfl (fun j hj => by rw [h j hj])]
  · rw [Finset.sum_congr rfl (fun j hj => by rw [h j hj])]

/-! ## 2. Algebraic identities -/

/-- (app-cp-kappa). -/
lemma cp_mul_kappa (p : ℝ) : cp p * kappa p = -p / 2 := by
  unfold cp kappa
  split_ifs with h
  · subst h; norm_num
  · have h1 : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    field_simp <;> ring

/-- (app-B-identity): `c_p r² ψ_p(γ/r²) = -B_{p,r}(γ)`. -/
lemma B_identity (p r γ : ℝ) (hr : r ≠ 0) :
    cp p * (r ^ 2 * psi p (γ / r ^ 2)) = -Bpr p r γ := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  unfold cp psi Bpr
  split_ifs with h
  · set L := Real.log (1 + γ / r ^ 2)
    have e : r ^ 2 * ((1 + γ / r ^ 2) * L - γ / r ^ 2) = (r ^ 2 + γ) * L - γ := by
      field_simp <;> ring
    rw [e]
    ring
  · set P := (1 + γ / r ^ 2) ^ p
    have h1 : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    field_simp <;> ring

/-- `B_{p,1}((1-t)/t) = A_p(t)`. -/
lemma B_one_eq_A (p t : ℝ) (ht : 0 < t) : Bpr p 1 ((1 - t) / t) = Ap p t := by
  have h1 : (1 : ℝ) + (1 - t) / t / 1 ^ 2 = t⁻¹ := by
    field_simp
  have hinv : (t⁻¹) ^ p = t ^ (-p) := by
    rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le]
  unfold Bpr Ap
  split_ifs with h
  · rw [h1]
    have ht0 : t ≠ 0 := ht.ne'
    have e : (1 - t) / t = t⁻¹ - 1 := by field_simp
    rw [e]
    ring
  · rw [h1, hinv]
    have ht0 : t ≠ 0 := ht.ne'
    have hp1 : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hp2 : p - 1 ≠ 0 := sub_ne_zero.mpr h
    have e : (1 - t) / t = t⁻¹ - 1 := by field_simp
    rw [e]
    field_simp <;> ring

/-- The arithmetic step of Prop. app-spectrum-G. -/
lemma eig_recursion (k r m : ℝ) :
    (r - 1 - m) * (k - r - m + 2) + (k - 2 * r + 2) = (r - m) * (k - r - m + 1) := by
  ring

/-! ## 3. Proposition app-exact-expansion -/

theorem exact_expansion (p : ℝ) {ι : Type*} (s : Finset ι) (d y : ι → ℝ) (M : ℝ)
    (hM : 0 < M) (hd : ∀ j ∈ s, 0 ≤ d j) (hdM : ∑ j ∈ s, d j = M)
    (hy : ∀ j ∈ s, -1 < y j) (hdy : ∑ j ∈ s, d j * y j = 0) :
    renyi p s d (fun j => (1 + y j) / M)
      = Real.log M + Fp p ((∑ j ∈ s, d j * psi p (y j)) / M) := by
  have hM0 : M ≠ 0 := hM.ne'
  by_cases hp : p = 1
  · subst hp
    simp only [renyi, Fp, psi, eq_self_iff_true, if_true]
    have hlog : ∀ j ∈ s, Real.log ((1 + y j) / M) = Real.log (1 + y j) - Real.log M :=
      fun j hj => Real.log_div (by linarith [hy j hj]) hM0
    have hterm : ∀ j ∈ s, d j * ((1 + y j) / M * Real.log ((1 + y j) / M))
        = (d j * ((1 + y j) * Real.log (1 + y j) - y j)) / M + (d j * y j) / M
          - (d j + d j * y j) * Real.log M / M := by
      intro j hj
      rw [hlog j hj]
      field_simp <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_mul,
      Finset.sum_add_distrib, hdM, hdy]
    field_simp <;> ring
  · simp only [renyi, Fp, psi, if_neg hp]
    have hpos : ∀ j ∈ s, 0 < 1 + y j := fun j hj => by linarith [hy j hj]
    have h1 : ∑ j ∈ s, d j * ((1 + y j) / M) ^ p
        = (∑ j ∈ s, d j * (1 + y j) ^ p) / M ^ p := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Real.div_rpow (hpos j hj).le hM.le]
      ring
    have h2 : ∑ j ∈ s, d j * (1 + y j) ^ p
        = M + ∑ j ∈ s, d j * ((1 + y j) ^ p - 1 - p * y j) := by
      have : ∀ j ∈ s, d j * (1 + y j) ^ p
          = d j + p * (d j * y j) + d j * ((1 + y j) ^ p - 1 - p * y j) := by
        intro j _
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hdM, hdy]
      ring
    have hex : ∃ j ∈ s, 0 < d j := by
      by_contra hcon
      push_neg at hcon
      have := Finset.sum_nonpos hcon
      linarith
    have hpos2 : 0 < ∑ j ∈ s, d j * (1 + y j) ^ p := by
      obtain ⟨j, hj, hdj⟩ := hex
      exact Finset.sum_pos'
        (fun i hi => mul_nonneg (hd i hi) (Real.rpow_nonneg (hpos i hi).le _))
        ⟨j, hj, mul_pos hdj (Real.rpow_pos_of_pos (hpos j hj) _)⟩
    rw [h1]
    rw [h2] at hpos2 ⊢
    set G := ∑ j ∈ s, d j * ((1 + y j) ^ p - 1 - p * y j) with hG
    have h1p : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
    have hMG : M + G = M * (1 + G / M) := by
      field_simp
    have h3 : 0 < 1 + G / M := by
      have e : 1 + G / M = (M + G) / M := by field_simp
      rw [e]
      exact div_pos hpos2 hM
    rw [Real.log_div hpos2.ne' (Real.rpow_pos_of_pos hM p).ne', Real.log_rpow hM, hMG,
      Real.log_mul hM0 h3.ne']
    field_simp <;> ring

/-! ## 4. Proposition app-local-bounds -/

/-- `|log(1+x) - x| ≤ 2x²` for `|x| ≤ 1/2`. -/
lemma log_bound1 {x : ℝ} (hx : |x| ≤ 1 / 2) : |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  have e : (∑ i ∈ Finset.range 1, (-x) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -x)
      = Real.log (1 + x) - x := by
    simp only [Finset.sum_range_one, sub_neg_eq_add]
    push_cast
    ring
  rw [e, abs_neg] at h
  have h1 : 0 < 1 - |x| := by linarith
  refine le_trans h ?_
  rw [div_le_iff₀ h1]
  have hx2 : |x| ^ (1 + 1) = x ^ 2 := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, sq_abs]
  rw [hx2]
  nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * |x|)]

/-- `|log(1+y) - (y - y²/2)| ≤ 2|y|³` for `|y| ≤ 1/2`. -/
lemma log_bound2 {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |Real.log (1 + y) - (y - y ^ 2 / 2)| ≤ 2 * |y| ^ 3 := by
  have hx : |(-y)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  have e : (∑ i ∈ Finset.range 2, (-y) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -y)
      = Real.log (1 + y) - (y - y ^ 2 / 2) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add]
    push_cast
    ring
  rw [e, abs_neg] at h
  have h1 : 0 < 1 - |y| := by linarith
  refine le_trans h ?_
  rw [div_le_iff₀ h1]
  have e3 : |y| ^ (2 + 1) = |y| ^ 3 := by norm_num
  rw [e3]
  have h0 : 0 ≤ |y| ^ 3 := by positivity
  nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - 2 * |y|)]

/-- `|e^z - 1 - z - z²/2| ≤ |z|³` for `|z| ≤ 1`. -/
lemma exp_bound2 {z : ℝ} (hz : |z| ≤ 1) : |Real.exp z - (1 + z + z ^ 2 / 2)| ≤ |z| ^ 3 := by
  have h := Real.exp_bound hz (show 0 < 3 by norm_num)
  have e : ∑ i ∈ Finset.range 3, z ^ i / (Nat.factorial i : ℝ) = 1 + z + z ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
      Nat.factorial_one, Nat.factorial_two]
    push_cast
    ring
  rw [e] at h
  refine le_trans h ?_
  have h0 : 0 ≤ |z| ^ 3 := by positivity
  have hc : ((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * ((3 : ℕ) : ℝ)) ≤ 1 := by
    norm_num [Nat.factorial]
  calc |z| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * ((3 : ℕ) : ℝ)))
      ≤ |z| ^ 3 * 1 := mul_le_mul_of_nonneg_left hc h0
    _ = |z| ^ 3 := mul_one _

/-- Prop. app-local-bounds (i), case `p ≠ 1`, with explicit constants. -/
lemma rpow_bound {p y : ℝ} (hp : 0 < p) (hy : |y| ≤ 1 / 2) (hyp : 4 * p * |y| ≤ 1) :
    |(1 + y) ^ p - 1 - p * y - p * (p - 1) / 2 * y ^ 2|
      ≤ (8 * p ^ 3 + 3 * p ^ 2 + 2 * p) * |y| ^ 3 := by
  have hpos : 0 < 1 + y := by have := neg_abs_le y; linarith
  have ha := abs_nonneg y
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have h3 : |y| ^ 3 ≤ |y| ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hy (pow_nonneg ha 2)
    nlinarith [this]
  have h4 : |y| ^ 2 ≤ |y| / 2 := by
    have := mul_le_mul_of_nonneg_right hy ha
    nlinarith [this]
  have hb1 : |Real.log (1 + y) - (y - y ^ 2 / 2)| ≤ 2 * |y| ^ 3 := log_bound2 hy
  set L := Real.log (1 + y) with hL
  set e1 := L - (y - y ^ 2 / 2) with he1
  have hy2' : 0 ≤ y ^ 2 / 2 := by positivity
  have hLb : |L| ≤ 2 * |y| := by
    have hL' : L = y - y ^ 2 / 2 + e1 := by rw [he1]; ring
    have h1 : |y - y ^ 2 / 2 + e1| ≤ |y| + y ^ 2 / 2 + |e1| := by
      calc |y - y ^ 2 / 2 + e1| ≤ |y - y ^ 2 / 2| + |e1| := abs_add _ _
        _ ≤ |y| + |y ^ 2 / 2| + |e1| := by
            have := abs_sub y (y ^ 2 / 2)
            linarith
        _ = |y| + y ^ 2 / 2 + |e1| := by rw [abs_of_nonneg hy2']
    rw [hL']
    linarith [h1, hb1, h3, h4, hy2]
  set u := L * p with hu
  have hub : |u| ≤ 2 * p * |y| := by
    rw [hu, abs_mul, abs_of_pos hp]
    nlinarith [hLb]
  have hu1 : |u| ≤ 1 := by nlinarith [hub, hyp]
  have hexp := exp_bound2 hu1
  set E2 := Real.exp u - (1 + u + u ^ 2 / 2) with hE2
  have hrp : (1 + y) ^ p = Real.exp u := by
    rw [Real.rpow_def_of_pos hpos]
  have key : (1 + y) ^ p - 1 - p * y - p * (p - 1) / 2 * y ^ 2
      = E2 + p * e1 + p ^ 2 / 2 * ((e1 - y ^ 2 / 2) * (2 * y - y ^ 2 / 2 + e1)) := by
    rw [hrp, hE2, he1, hu]
    ring
  have hE2b : |E2| ≤ 8 * p ^ 3 * |y| ^ 3 := by
    calc |E2| ≤ |u| ^ 3 := hexp
      _ ≤ (2 * p * |y|) ^ 3 := pow_le_pow_left (abs_nonneg u) hub 3
      _ = 8 * p ^ 3 * |y| ^ 3 := by ring
  have he1b : |p * e1| ≤ 2 * p * |y| ^ 3 := by
    rw [abs_mul, abs_of_pos hp]
    nlinarith [hb1]
  have hA : |e1 - y ^ 2 / 2| ≤ 3 / 2 * |y| ^ 2 := by
    have := abs_sub e1 (y ^ 2 / 2)
    rw [abs_of_nonneg hy2'] at this
    linarith [hb1, hy2, h3]
  have hB : |2 * y - y ^ 2 / 2 + e1| ≤ 3 * |y| := by
    have h1 : |2 * y - y ^ 2 / 2 + e1| ≤ 2 * |y| + y ^ 2 / 2 + |e1| := by
      calc |2 * y - y ^ 2 / 2 + e1| ≤ |2 * y - y ^ 2 / 2| + |e1| := abs_add _ _
        _ ≤ |2 * y| + |y ^ 2 / 2| + |e1| := by
            have := abs_sub (2 * y) (y ^ 2 / 2)
            linarith
        _ = 2 * |y| + y ^ 2 / 2 + |e1| := by
            rw [abs_mul, abs_two, abs_of_nonneg hy2']
    linarith [h1, hb1, hy2, h3, h4]
  have hC : |p ^ 2 / 2 * ((e1 - y ^ 2 / 2) * (2 * y - y ^ 2 / 2 + e1))|
      ≤ 3 * p ^ 2 * |y| ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < p ^ 2 / 2)]
    have h5 := mul_le_mul hA hB (abs_nonneg _) (by positivity)
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ p ^ 2 / 2)
    have h7 : 0 ≤ p ^ 2 * |y| ^ 3 := by positivity
    nlinarith [h6, h7]
  rw [key]
  calc |E2 + p * e1 + p ^ 2 / 2 * ((e1 - y ^ 2 / 2) * (2 * y - y ^ 2 / 2 + e1))|
      ≤ |E2| + |p * e1| + |p ^ 2 / 2 * ((e1 - y ^ 2 / 2) * (2 * y - y ^ 2 / 2 + e1))| :=
        abs_add_three _ _ _
    _ ≤ 8 * p ^ 3 * |y| ^ 3 + 2 * p * |y| ^ 3 + 3 * p ^ 2 * |y| ^ 3 := by
        linarith [hE2b, he1b, hC]
    _ = (8 * p ^ 3 + 3 * p ^ 2 + 2 * p) * |y| ^ 3 := by ring

/-- Prop. app-local-bounds (i), case `p = 1`. -/
lemma xlogx_bound {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |(1 + y) * Real.log (1 + y) - y - y ^ 2 / 2| ≤ 4 * |y| ^ 3 := by
  have hb := log_bound2 hy
  set e1 := Real.log (1 + y) - (y - y ^ 2 / 2) with he1
  have key : (1 + y) * Real.log (1 + y) - y - y ^ 2 / 2 = -(y ^ 3 / 2) + (1 + y) * e1 := by
    rw [he1]; ring
  rw [key]
  have h1 : |-(y ^ 3 / 2)| = |y| ^ 3 / 2 := by
    rw [abs_neg, abs_div, abs_pow, abs_two]
  have h2 : |(1 + y) * e1| ≤ 3 / 2 * (2 * |y| ^ 3) := by
    rw [abs_mul]
    have h3 : |1 + y| ≤ 3 / 2 := by
      have := abs_add (1 : ℝ) y
      rw [abs_one] at this
      linarith
    exact mul_le_mul h3 hb (abs_nonneg _) (by norm_num)
  calc |-(y ^ 3 / 2) + (1 + y) * e1| ≤ |-(y ^ 3 / 2)| + |(1 + y) * e1| := abs_add _ _
    _ ≤ |y| ^ 3 / 2 + 3 / 2 * (2 * |y| ^ 3) := by rw [h1]; linarith
    _ ≤ 4 * |y| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg y) 3]

/-- Prop. app-local-bounds (i). -/
lemma psi_local {p : ℝ} (hp : 0 < p) :
    ∃ η C : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ 0 ≤ C ∧
      ∀ y, |y| ≤ η → |psi p y - kappa p * y ^ 2| ≤ C * |y| ^ 3 := by
  by_cases h : p = 1
  · refine ⟨1 / 2, 4, by norm_num, le_rfl, by norm_num, fun y hy => ?_⟩
    have := xlogx_bound hy
    simp only [psi, kappa, if_pos h]
    convert this using 2 <;> ring
  · refine ⟨min (1 / 2) (1 / (4 * p)), 8 * p ^ 3 + 3 * p ^ 2 + 2 * p,
      lt_min (by norm_num) (by positivity), min_le_left _ _, by positivity, fun y hy => ?_⟩
    have hy1 : |y| ≤ 1 / 2 := le_trans hy (min_le_left _ _)
    have hy2 : 4 * p * |y| ≤ 1 := by
      have := le_trans hy (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith [this]
    have := rpow_bound hp hy1 hy2
    simp only [psi, kappa, if_neg h]
    convert this using 2 <;> ring

/-- Prop. app-local-bounds (ii). -/
lemma Fp_local (p : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |x| ≤ 1 / 2 → |Fp p x - cp p * x| ≤ C * x ^ 2 := by
  by_cases h : p = 1
  · refine ⟨0, le_rfl, fun x _ => ?_⟩
    simp [Fp, cp, h]
  · have h1 : 0 < |1 - p| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
    refine ⟨2 / |1 - p|, by positivity, fun x hx => ?_⟩
    simp only [Fp, cp, if_neg h]
    have hb := log_bound1 hx
    have e : Real.log (1 + x) / (1 - p) - 1 / (1 - p) * x = (Real.log (1 + x) - x) / (1 - p) := by
      ring
    rw [e, abs_div, div_le_iff₀ h1]
    calc |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := hb
      _ = 2 / |1 - p| * x ^ 2 * |1 - p| := by field_simp

/-- `|ψ_p(δ)| ≤ (|κ_p| + C)|δ|` near `0`. -/
lemma psi_small {p η C : ℝ} (hη' : η ≤ 1 / 2) (hC : 0 ≤ C)
    (hloc : ∀ y, |y| ≤ η → |psi p y - kappa p * y ^ 2| ≤ C * |y| ^ 3) :
    ∀ δ, |δ| ≤ η → |psi p δ| ≤ (|kappa p| + C) * |δ| := by
  intro δ hδ
  have h1 := hloc δ hδ
  have hd0 := abs_nonneg δ
  have hd1 : |δ| ≤ 1 := by linarith
  have h2 : |kappa p * δ ^ 2| ≤ |kappa p| * |δ| := by
    rw [abs_mul, abs_pow]
    have : |δ| ^ 2 ≤ |δ| := by nlinarith
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have h3 : C * |δ| ^ 3 ≤ C * |δ| := by
    have : |δ| ^ 3 ≤ |δ| := by nlinarith [pow_nonneg hd0 2]
    exact mul_le_mul_of_nonneg_left this hC
  have h4 : |psi p δ| ≤ |psi p δ - kappa p * δ ^ 2| + |kappa p * δ ^ 2| := by
    calc |psi p δ| = |(psi p δ - kappa p * δ ^ 2) + kappa p * δ ^ 2| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add _ _
  nlinarith [h1, h2, h3, h4]

/-- Prop. app-local-bounds (iii), Lipschitz part, near a fixed point `ys > -1`. -/
lemma psi_lip {p : ℝ} (hp : 0 < p) {ys : ℝ} (hys : -1 < ys) :
    ∃ L η : ℝ, 0 < η ∧ 0 ≤ L ∧
      ∀ y, |y - ys| ≤ η → |psi p y - psi p ys| ≤ L * |y - ys| := by
  obtain ⟨η₀, C, hη₀, hη₀', hC, hloc⟩ := psi_local hp
  have hsmall := psi_small hη₀' hC hloc
  have hs : 0 < 1 + ys := by linarith
  have hδ : ∀ y, |y - ys| ≤ η₀ * (1 + ys) → |(y - ys) / (1 + ys)| ≤ η₀ := by
    intro y hy
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact hy
  by_cases h1 : p = 1
  · refine ⟨|Real.log (1 + ys)| + |kappa p| + C, η₀ * (1 + ys), by positivity, by positivity,
      fun y hy => ?_⟩
    set δ := (y - ys) / (1 + ys) with hδdef
    have hδb := hδ y hy
    have hδ1 : 0 < 1 + δ := by have := neg_abs_le δ; linarith
    have hyd : y = ys + (1 + ys) * δ := by
      rw [hδdef]; field_simp
    have hfac : 1 + y = (1 + ys) * (1 + δ) := by rw [hyd]; ring
    have hdiff : psi p y - psi p ys = (1 + ys) * (δ * Real.log (1 + ys) + psi p δ) := by
      simp only [psi, if_pos h1]
      rw [hfac, Real.log_mul hs.ne' hδ1.ne']
      set A := Real.log (1 + ys)
      set B := Real.log (1 + δ)
      rw [hyd]
      ring
    have hδy : (1 + ys) * |δ| = |y - ys| := by
      rw [hδdef, abs_div, abs_of_pos hs]
      field_simp
    rw [hdiff, abs_mul, abs_of_pos hs]
    have hψ := hsmall δ hδb
    have hin : |δ * Real.log (1 + ys) + psi p δ|
        ≤ |δ| * |Real.log (1 + ys)| + (|kappa p| + C) * |δ| := by
      calc |δ * Real.log (1 + ys) + psi p δ| ≤ |δ * Real.log (1 + ys)| + |psi p δ| :=
            abs_add _ _
        _ ≤ |δ| * |Real.log (1 + ys)| + (|kappa p| + C) * |δ| := by
            rw [abs_mul]; linarith
    calc (1 + ys) * |δ * Real.log (1 + ys) + psi p δ|
        ≤ (1 + ys) * (|δ| * |Real.log (1 + ys)| + (|kappa p| + C) * |δ|) :=
          mul_le_mul_of_nonneg_left hin hs.le
      _ = (|Real.log (1 + ys)| + |kappa p| + C) * ((1 + ys) * |δ|) := by ring
      _ = (|Real.log (1 + ys)| + |kappa p| + C) * |y - ys| := by rw [hδy]
  · have hQ : 0 < (1 + ys) ^ p := Real.rpow_pos_of_pos hs p
    refine ⟨((1 + ys) ^ p * (p + |kappa p| + C) + p * (1 + ys)) / (1 + ys), η₀ * (1 + ys),
      by positivity, by positivity, fun y hy => ?_⟩
    set δ := (y - ys) / (1 + ys) with hδdef
    have hδb := hδ y hy
    have hδ1 : 0 < 1 + δ := by have := neg_abs_le δ; linarith
    have hyd : y = ys + (1 + ys) * δ := by
      rw [hδdef]; field_simp
    have hpow : (1 + y) ^ p = (1 + ys) ^ p * (1 + δ) ^ p := by
      rw [← Real.mul_rpow hs.le hδ1.le]
      congr 1
      rw [hyd]; ring
    have hdiff : psi p y - psi p ys
        = (1 + ys) ^ p * (p * δ + psi p δ) - p * ((1 + ys) * δ) := by
      simp only [psi, if_neg h1]
      rw [hpow]
      set P := (1 + δ) ^ p
      set Q := (1 + ys) ^ p
      rw [hyd]
      ring
    have hδy : |δ| = |y - ys| / (1 + ys) := by
      rw [hδdef, abs_div, abs_of_pos hs]
    have hψ := hsmall δ hδb
    have hin : |p * δ + psi p δ| ≤ p * |δ| + (|kappa p| + C) * |δ| := by
      calc |p * δ + psi p δ| ≤ |p * δ| + |psi p δ| := abs_add _ _
        _ ≤ p * |δ| + (|kappa p| + C) * |δ| := by
            rw [abs_mul, abs_of_pos hp]; linarith
    have h2 : |(1 + ys) ^ p * (p * δ + psi p δ) - p * ((1 + ys) * δ)|
        ≤ ((1 + ys) ^ p * (p + |kappa p| + C) + p * (1 + ys)) * |δ| := by
      calc |(1 + ys) ^ p * (p * δ + psi p δ) - p * ((1 + ys) * δ)|
          ≤ |(1 + ys) ^ p * (p * δ + psi p δ)| + |p * ((1 + ys) * δ)| := abs_sub _ _
        _ = (1 + ys) ^ p * |p * δ + psi p δ| + p * ((1 + ys) * |δ|) := by
            rw [abs_mul, abs_of_pos hQ, abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hs]
        _ ≤ (1 + ys) ^ p * (p * |δ| + (|kappa p| + C) * |δ|) + p * ((1 + ys) * |δ|) := by
            have := mul_le_mul_of_nonneg_left hin hQ.le
            linarith
        _ = ((1 + ys) ^ p * (p + |kappa p| + C) + p * (1 + ys)) * |δ| := by ring
    rw [hdiff]
    rw [hδy] at h2
    calc _ ≤ _ := h2
      _ = ((1 + ys) ^ p * (p + |kappa p| + C) + p * (1 + ys)) / (1 + ys) * |y - ys| := by
          ring

/-- Prop. app-local-bounds (iii), boundedness part, on `[-1/2, Y]`. -/
lemma psi_bdd {p : ℝ} (hp : 0 < p) (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ B : ℝ, ∀ y, -1 / 2 ≤ y → y ≤ Y → |psi p y| ≤ B := by
  by_cases h1 : p = 1
  · refine ⟨(1 + Y) * (Y + 1) + (Y + 1), fun y hy0 hy1 => ?_⟩
    simp only [psi, if_pos h1]
    have hpos : 0 < 1 + y := by linarith
    have hl1 : Real.log (1 + y) ≤ Y := by
      have := Real.log_le_sub_one_of_pos hpos; linarith
    have hl2 : -1 ≤ Real.log (1 + y) := by
      have h3 := Real.one_sub_inv_le_log_of_pos hpos
      have h4 : (1 + y)⁻¹ ≤ 2 := by
        rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith
      linarith
    have habs : |Real.log (1 + y)| ≤ Y + 1 := by
      rw [abs_le]; constructor <;> linarith
    have hy2 : |y| ≤ Y + 1 := by
      rw [abs_le]; constructor <;> linarith
    calc |(1 + y) * Real.log (1 + y) - y| ≤ |(1 + y) * Real.log (1 + y)| + |y| := abs_sub _ _
      _ = (1 + y) * |Real.log (1 + y)| + |y| := by rw [abs_mul, abs_of_pos hpos]
      _ ≤ (1 + Y) * (Y + 1) + (Y + 1) := by
          have := mul_le_mul (by linarith : 1 + y ≤ 1 + Y) habs (abs_nonneg _) (by linarith)
          linarith
  · refine ⟨(1 + Y) ^ p + 1 + p * (Y + 1), fun y hy0 hy1 => ?_⟩
    simp only [psi, if_neg h1]
    have hpos : 0 < 1 + y := by linarith
    have hr : (1 + y) ^ p ≤ (1 + Y) ^ p := Real.rpow_le_rpow hpos.le (by linarith) hp.le
    have hr0 : 0 ≤ (1 + y) ^ p := Real.rpow_nonneg hpos.le _
    have hy2 : |y| ≤ Y + 1 := by
      rw [abs_le]; constructor <;> linarith
    have e1 : |(1 + y) ^ p - 1| ≤ (1 + y) ^ p + 1 := by
      rw [abs_le]; constructor <;> linarith
    have e2 : |p * y| ≤ p * (Y + 1) := by
      rw [abs_mul, abs_of_pos hp]; exact mul_le_mul_of_nonneg_left hy2 hp.le
    calc |(1 + y) ^ p - 1 - p * y| ≤ |(1 + y) ^ p - 1| + |p * y| := abs_sub _ _
      _ ≤ (1 + Y) ^ p + 1 + p * (Y + 1) := by linarith

/-! ## 5. Proposition app-uniform-expansion -/

theorem uniform_expansion {p : ℝ} (hp : 0 < p) :
    ∃ η C : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ 0 ≤ C ∧
      ∀ {ι : Type} (s : Finset ι) (d y : ι → ℝ) (M e : ℝ),
        0 < M → (∀ j ∈ s, 0 ≤ d j) → ∑ j ∈ s, d j = M → ∑ j ∈ s, d j * y j = 0 →
        (∀ j ∈ s, |y j| ≤ e) → e ≤ η →
        |renyi p s d (fun j => (1 + y j) / M) - Real.log M
            + p / 2 * ((∑ j ∈ s, d j * y j ^ 2) / M)|
          ≤ C * (e + (∑ j ∈ s, d j * y j ^ 2) / M) * ((∑ j ∈ s, d j * y j ^ 2) / M) := by
  obtain ⟨η₁, C₁, hη₁, hη₁', hC₁, hloc⟩ := psi_local hp
  obtain ⟨C₂, hC₂, hF⟩ := Fp_local p
  set K := |kappa p| + C₁ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨min η₁ (1 / (2 * (K + 1))), C₂ * K ^ 2 + |cp p| * C₁,
    lt_min hη₁ (by positivity), le_trans (min_le_left _ _) hη₁', by positivity, ?_⟩
  intro ι s d y M e hM hd hdM hdy hye heη
  have he1 : e ≤ η₁ := le_trans heη (min_le_left _ _)
  have he2 : e ≤ 1 / (2 * (K + 1)) := le_trans heη (min_le_right _ _)
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hdM
    linarith
  obtain ⟨j0, hj0⟩ := hsne
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) (hye j0 hj0)
  have hy1 : ∀ j ∈ s, -1 < y j := fun j hj => by
    have h1 := hye j hj
    have h2 := neg_abs_le (y j)
    linarith
  have hexp := exact_expansion p s d y M hM hd hdM hy1 hdy
  rw [hexp]
  set Q := (∑ j ∈ s, d j * y j ^ 2) / M with hQ
  set X := (∑ j ∈ s, d j * psi p (y j)) / M with hX
  have hQ0 : 0 ≤ Q :=
    div_nonneg (Finset.sum_nonneg (fun j hj => mul_nonneg (hd j hj) (sq_nonneg _))) hM.le
  have hQM : Q * M = ∑ j ∈ s, d j * y j ^ 2 := by
    rw [hQ]; field_simp
  have hXQ : |X - kappa p * Q| ≤ C₁ * e * Q := by
    have hsum : ∑ j ∈ s, d j * (psi p (y j) - kappa p * y j ^ 2)
        = ∑ j ∈ s, d j * psi p (y j) - kappa p * ∑ j ∈ s, d j * y j ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have e' : X - kappa p * Q = (∑ j ∈ s, d j * (psi p (y j) - kappa p * y j ^ 2)) / M := by
      rw [hsum, hX, hQ]; ring
    rw [e', abs_div, abs_of_pos hM, div_le_iff₀ hM]
    calc |∑ j ∈ s, d j * (psi p (y j) - kappa p * y j ^ 2)|
        ≤ ∑ j ∈ s, |d j * (psi p (y j) - kappa p * y j ^ 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, d j * (C₁ * e * y j ^ 2) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [abs_mul, abs_of_nonneg (hd j hj)]
          refine mul_le_mul_of_nonneg_left ?_ (hd j hj)
          have h1 := hloc (y j) (le_trans (hye j hj) he1)
          have h2 : |y j| ^ 3 ≤ e * y j ^ 2 := by
            calc |y j| ^ 3 = |y j| * |y j| ^ 2 := by ring
              _ = |y j| * y j ^ 2 := by rw [sq_abs]
              _ ≤ e * y j ^ 2 := mul_le_mul_of_nonneg_right (hye j hj) (sq_nonneg _)
          calc |psi p (y j) - kappa p * y j ^ 2| ≤ C₁ * |y j| ^ 3 := h1
            _ ≤ C₁ * (e * y j ^ 2) := mul_le_mul_of_nonneg_left h2 hC₁
            _ = C₁ * e * y j ^ 2 := by ring
      _ = C₁ * e * (Q * M) := by
          rw [hQM, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = C₁ * e * Q * M := by ring
  have hQe : Q ≤ e ^ 2 := by
    rw [hQ, div_le_iff₀ hM, ← hdM, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have : y j ^ 2 ≤ e ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left (abs_nonneg _) (hye j hj) 2
    nlinarith [hd j hj]
  have hXb : |X| ≤ K * Q := by
    have h1 : |X| ≤ |X - kappa p * Q| + |kappa p * Q| := by
      calc |X| = |(X - kappa p * Q) + kappa p * Q| := by rw [sub_add_cancel]
        _ ≤ _ := abs_add _ _
    rw [abs_mul, abs_of_nonneg hQ0] at h1
    have h2 : C₁ * e * Q ≤ C₁ * Q := by
      have he' : e ≤ 1 := by linarith
      have := mul_le_mul_of_nonneg_left he' (mul_nonneg hC₁ hQ0)
      nlinarith [this]
    rw [hK]
    nlinarith [hXQ, h1, h2]
  have hX12 : |X| ≤ 1 / 2 := by
    have h1 : K * Q ≤ K * e ^ 2 := mul_le_mul_of_nonneg_left hQe hK0
    have h2 : e * (2 * (K + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at he2; linarith
    have h3 : K * e ≤ 1 / 2 := by nlinarith [h2, he0]
    have h4 : K * e * e ≤ 1 / 2 * e := mul_le_mul_of_nonneg_right h3 he0
    nlinarith [h1, h4, hXb]
  have hF' := hF X hX12
  have hc := cp_mul_kappa p
  have key : Real.log M + Fp p X - Real.log M + p / 2 * Q
      = (Fp p X - cp p * X) + cp p * (X - kappa p * Q) := by
    have : p / 2 = -(cp p * kappa p) := by rw [hc]; ring
    rw [this]; ring
  rw [key]
  have hX2 : X ^ 2 ≤ (K * Q) ^ 2 := by
    rw [← sq_abs X]; exact pow_le_pow_left (abs_nonneg _) hXb 2
  calc |(Fp p X - cp p * X) + cp p * (X - kappa p * Q)|
      ≤ |Fp p X - cp p * X| + |cp p * (X - kappa p * Q)| := abs_add _ _
    _ ≤ C₂ * X ^ 2 + |cp p| * (C₁ * e * Q) := by
        rw [abs_mul]
        exact add_le_add hF' (mul_le_mul_of_nonneg_left hXQ (abs_nonneg _))
    _ ≤ C₂ * (K * Q) ^ 2 + |cp p| * (C₁ * e * Q) := by
        have := mul_le_mul_of_nonneg_left hX2 hC₂
        linarith
    _ ≤ (C₂ * K ^ 2 + |cp p| * C₁) * (e + Q) * Q := by
        have h1 : 0 ≤ C₂ * K ^ 2 * (e * Q) := by positivity
        have h2 : 0 ≤ |cp p| * C₁ * (Q * Q) := by positivity
        nlinarith [h1, h2]

/-! ## 6. Binomial identities, `Tr W_{k,r} = 1`, and `∑_m d_m = D²` -/

/-- `k C(k-1, r-1) = r C(k, r)`, i.e. `kN = rD` of (DN). -/
lemma choose_mul_left {k r : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (k : ℝ) * (Nat.choose (k - 1) (r - 1) : ℝ) = r * (Nat.choose k r : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  have h := Nat.succ_mul_choose_eq n j
  have h' : ((n + 1 : ℕ) : ℝ) * (Nat.choose n j : ℝ)
      = (Nat.choose (n + 1) (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  simp only [Nat.add_sub_cancel]
  rw [h']
  ring

/-- `k C(k-1, r) = (k - r) C(k, r)`. -/
lemma choose_mul_right {k r : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (k : ℝ) * (Nat.choose (k - 1) r : ℝ) = ((k : ℝ) - r) * (Nat.choose k r : ℝ) := by
  have h1 := choose_mul_left hr hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  have hp : (Nat.choose (n + 1) (j + 1) : ℝ) = Nat.choose n j + Nat.choose n (j + 1) := by
    exact_mod_cast Nat.choose_succ_succ n j
  simp only [Nat.add_sub_cancel] at h1 ⊢
  rw [hp] at h1 ⊢
  push_cast at h1 ⊢
  linear_combination -h1

/-- `C(k, j+1)(j+1) = C(k, j)(k - j)`. -/
lemma choose_succ_ratio {k j : ℕ} (hj : j ≤ k) :
    (Nat.choose k (j + 1) : ℝ) * ((j : ℝ) + 1) = (Nat.choose k j : ℝ) * ((k : ℝ) - j) := by
  have h := Nat.choose_succ_right_eq k j
  have h' : ((Nat.choose k (j + 1) * (j + 1) : ℕ) : ℝ) = ((Nat.choose k j * (k - j) : ℕ) : ℝ) := by
    rw [h]
  push_cast [Nat.cast_sub hj] at h'
  linarith

/-- `C(k, j) ≤ (2r/k) C(k, j+1)` for `j < r ≤ k/2`. -/
lemma choose_le_ratio {k r j : ℕ} (hjr : j + 1 ≤ r) (hk : 2 * r ≤ k) :
    (Nat.choose k j : ℝ) ≤ (2 * r / k) * (Nat.choose k (j + 1) : ℝ) := by
  have hjk : j ≤ k := by omega
  have h := choose_succ_ratio hjk
  have hkj : (k : ℝ) - j ≥ (k : ℝ) / 2 := by
    have : (2 * r : ℝ) ≤ k := by exact_mod_cast hk
    have : (j : ℝ) + 1 ≤ r := by exact_mod_cast hjr
    linarith
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by
      have : (2 * 1 : ℕ) ≤ k := le_trans (by omega) hk
      exact_mod_cast this
    linarith
  have hC0 : (0 : ℝ) ≤ Nat.choose k j := Nat.cast_nonneg _
  have hC1 : (0 : ℝ) ≤ Nat.choose k (j + 1) := Nat.cast_nonneg _
  have hjr' : (j : ℝ) + 1 ≤ r := by exact_mod_cast hjr
  rw [div_mul_eq_mul_div, le_div_iff₀ hk0]
  -- C(k,j) * k ≤ 2 r C(k,j+1), from C(k,j)(k-j) = C(k,j+1)(j+1) and k - j ≥ k/2
  nlinarith [mul_le_mul_of_nonneg_left hkj hC0, mul_le_mul_of_nonneg_left hjr' hC1]

/-- `C(k, r - n) ≤ (2r/k)^n C(k, r)` for `n ≤ r ≤ k/2`. -/
lemma choose_le_pow {k r : ℕ} (hk : 2 * r ≤ k) :
    ∀ n, n ≤ r → (Nat.choose k (r - n) : ℝ) ≤ (2 * r / k) ^ n * (Nat.choose k r : ℝ) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := choose_le_ratio (j := r - (n + 1)) (by omega) hk
    have h2 : r - (n + 1) + 1 = r - n := by omega
    rw [h2] at h1
    have hq : (0 : ℝ) ≤ 2 * r / k := by positivity
    calc (Nat.choose k (r - (n + 1)) : ℝ) ≤ (2 * r / k) * (Nat.choose k (r - n) : ℝ) := h1
      _ ≤ (2 * r / k) * ((2 * r / k) ^ n * (Nat.choose k r : ℝ)) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hq
      _ = (2 * r / k) ^ (n + 1) * (Nat.choose k r : ℝ) := by ring

/-- `∑_{m<r} (k - 2m) C(k,m)² = k C(k-1,r-1)²` for `1 ≤ r ≤ k`. -/
lemma weighted_choose_sq {k : ℕ} :
    ∀ r, 1 ≤ r → r ≤ k →
      ∑ m ∈ Finset.range r, ((k : ℝ) - 2 * m) * (Nat.choose k m : ℝ) ^ 2
        = k * (Nat.choose (k - 1) (r - 1) : ℝ) ^ 2 := by
  intro r hr hrk
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hk : 1 ≤ k := by omega
    have h1 := choose_mul_left hn hk
    have h2 := choose_mul_right hn hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      exact this.ne'
    simp only [Nat.add_sub_cancel]
    apply mul_left_cancel₀ hk0
    linear_combination
      ((k : ℝ) * (Nat.choose (k - 1) (n - 1) : ℝ) + (n : ℝ) * (Nat.choose k n : ℝ)) * h1
      - ((k : ℝ) * (Nat.choose (k - 1) n : ℝ) + ((k : ℝ) - n) * (Nat.choose k n : ℝ)) * h2

/-- Summation by parts with `a_{-1} := 0`. -/
lemma sum_by_parts (a f : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (a m - (if m = 0 then 0 else a (m - 1))) * f m
      = a n * f n + ∑ m ∈ Finset.range n, a m * (f m - f (m + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, if_neg (Nat.add_one_ne_zero n),
      Nat.add_sub_cancel]
    ring

/-- `∑_{m ≤ r} d_m = C(k,r)²`: the multiplicities of Prop. app-spectrum-G fill `B(𝒜_r)`. -/
lemma mult_sum (k r : ℕ) : ∑ m ∈ Finset.range (r + 1), dm k m = (Nat.choose k r : ℝ) ^ 2 := by
  induction r with
  | zero => simp [dm]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [dm, if_neg (Nat.add_one_ne_zero n), Nat.add_sub_cancel]
    ring

/-- `Tr W_{k,r} = ∑_m d_m w_m = 1` (consistency of Prop. app-spectrum-W). -/
lemma trace_identity {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    ∑ m ∈ Finset.range (r + 1), dm k m * wm k r m = 1 := by
  have hk : 1 ≤ k := le_trans hr hrk
  have hN : (0 : ℝ) < (Nat.choose (k - 1) (r - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set f : ℕ → ℝ := fun m => ((r : ℝ) - m) * ((k : ℝ) - r - m + 1) with hf
  have hpart := sum_by_parts (fun m => (Nat.choose k m : ℝ) ^ 2) f r
  beta_reduce at hpart
  have hfr : f r = 0 := by rw [hf]; ring
  have hdiff : ∀ m, f m - f (m + 1) = (k : ℝ) - 2 * m := by
    intro m; rw [hf]; push_cast; ring
  have hsum : ∑ m ∈ Finset.range (r + 1), dm k m * f m
      = k * (Nat.choose (k - 1) (r - 1) : ℝ) ^ 2 := by
    have e : ∑ m ∈ Finset.range (r + 1), dm k m * f m
        = ∑ m ∈ Finset.range (r + 1),
            ((Nat.choose k m : ℝ) ^ 2 - (if m = 0 then 0 else (Nat.choose k (m - 1) : ℝ) ^ 2)) * f m := by
      rfl
    rw [e, hpart, hfr, mul_zero, zero_add, ← weighted_choose_sq r hr hrk]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hdiff m]
    ring
  have e2 : ∑ m ∈ Finset.range (r + 1), dm k m * wm k r m
      = (∑ m ∈ Finset.range (r + 1), dm k m * f m)
          / ((k : ℝ) * (Nat.choose (k - 1) (r - 1) : ℝ) ^ 2) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [wm, hf]
    ring
  rw [e2, hsum, div_self (mul_pos hk0 (pow_pos hN 2)).ne']

/-! ## 7. Counting `r`-subsets, and Prop. app-shuffled-spectrum -/

lemma card_subsets (k r : ℕ) : (subsets k r).card = Nat.choose k r := by
  rw [subsets, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- `#{I ⊆ s : |I| = n+1, x ∈ I} = C(|s| - 1, n)`. -/
lemma card_filter_mem_powersetCard {α : Type*} [DecidableEq α] (s : Finset α) {x : α}
    (hx : x ∈ s) (n : ℕ) :
    ((s.powersetCard (n + 1)).filter (fun I => x ∈ I)).card = (s.card - 1).choose n := by
  have hbij : ((s.powersetCard (n + 1)).filter (fun I => x ∈ I)).card
      = ((s.erase x).powersetCard n).card := by
    refine Finset.card_nbij' (fun I => I.erase x) (fun J => insert x J) ?_ ?_ ?_ ?_
    · intro I hI
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hI
      obtain ⟨⟨hIs, hIc⟩, hxI⟩ := hI
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.erase_subset_erase x hIs, ?_⟩
      rw [Finset.card_erase_of_mem hxI, hIc, Nat.add_sub_cancel]
    · intro J hJ
      rw [Finset.mem_powersetCard] at hJ
      obtain ⟨hJs, hJc⟩ := hJ
      have hxJ : x ∉ J := fun h => (Finset.not_mem_erase x s) (hJs h)
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self x J⟩
      · exact Finset.insert_subset hx (le_trans hJs (Finset.erase_subset x s))
      · rw [Finset.card_insert_of_not_mem hxJ, hJc]
    · intro I hI
      rw [Finset.mem_filter] at hI
      exact Finset.insert_erase hI.2
    · intro J hJ
      rw [Finset.mem_powersetCard] at hJ
      have hxJ : x ∉ J := fun h => (Finset.not_mem_erase x s) (hJ.1 h)
      exact Finset.erase_insert hxJ
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem hx]

/-- `#{I : |I| = r+1, i ∈ I} = C(k-1, r)`. -/
lemma card_in {k : ℕ} (r : ℕ) (i : Fin k) :
    ((subsets k (r + 1)).filter (fun I => i ∈ I)).card = (k - 1).choose r := by
  rw [subsets, card_filter_mem_powersetCard _ (Finset.mem_univ i) r, Finset.card_univ,
    Fintype.card_fin]

/-- `#{I : |I| = r+1, i ∈ I, j ∉ I} = C(k-2, r)` for `i ≠ j`. -/
lemma card_in_out {k : ℕ} (r : ℕ) {i j : Fin k} (hij : i ≠ j) :
    ((subsets k (r + 1)).filter (fun I => i ∈ I ∧ j ∉ I)).card = (k - 2).choose r := by
  have hset : (subsets k (r + 1)).filter (fun I => i ∈ I ∧ j ∉ I)
      = ((Finset.univ.erase j).powersetCard (r + 1)).filter (fun I => i ∈ I) := by
    ext I
    simp only [subsets, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hc⟩, hi, hj⟩
      refine ⟨⟨fun a ha => Finset.mem_erase.mpr ⟨fun h => hj (h ▸ ha), Finset.mem_univ a⟩, hc⟩, hi⟩
    · rintro ⟨⟨hsub, hc⟩, hi⟩
      exact ⟨⟨Finset.subset_univ I, hc⟩, hi, fun hj => (Finset.mem_erase.mp (hsub hj)).1 rfl⟩
  rw [hset, card_filter_mem_powersetCard _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) r,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

lemma sum_mem_eq_ite {k : ℕ} (I : Finset (Fin k)) (f : Fin k → ℝ) :
    ∑ i ∈ I, f i = ∑ i, if i ∈ I then f i else 0 := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- `∑_I ∑_{i∈I} f_i = C(k-1, r) ∑_i f_i` over the `(r+1)`-subsets. -/
lemma sum_over_subsets {k : ℕ} (r : ℕ) (f : Fin k → ℝ) :
    ∑ I ∈ subsets k (r + 1), ∑ i ∈ I, f i = ((k - 1).choose r : ℝ) * ∑ i, f i := by
  simp only [sum_mem_eq_ite]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← card_in r i, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun I _ => ?_)
  split_ifs <;> simp

/-- (app-quadratic-form), in the form `∑_I ε_I² = C(k-2, r) ‖ε‖²` for `(r+1)`-subsets. -/
lemma quadratic_form {k : ℕ} (r : ℕ) (ε : Fin k → ℝ) (hε : ∑ i, ε i = 0) :
    ∑ I ∈ subsets k (r + 1), (∑ i ∈ I, ε i) ^ 2 = ((k - 2).choose r : ℝ) * ∑ i, ε i ^ 2 := by
  set c : ℝ := ((k - 2).choose r : ℝ) with hc
  -- `ε_I = -∑_{j ∉ I} ε_j`
  have hsq : ∀ I : Finset (Fin k), (∑ i ∈ I, ε i) ^ 2
      = -∑ i, ∑ j, (if i ∈ I ∧ j ∉ I then ε i * ε j else 0) := by
    intro I
    have h1 : ∑ i ∈ I, ε i = -∑ j, (if j ∉ I then ε j else 0) := by
      have e : ∑ j, (if j ∉ I then ε j else 0)
          = ∑ j, ε j - ∑ j, (if j ∈ I then ε j else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : j ∈ I <;> simp [hj]
      rw [e, hε, sum_mem_eq_ite I ε]
      ring
    rw [sq]
    nth_rewrite 2 [h1]
    rw [sum_mem_eq_ite I ε, mul_neg, Finset.sum_mul_sum, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hi : i ∈ I <;> by_cases hj : j ∈ I <;> simp [hi, hj]
  have hswap : ∑ I ∈ subsets k (r + 1), ∑ i, ∑ j, (if i ∈ I ∧ j ∉ I then ε i * ε j else 0)
      = ∑ i, ∑ j, ε i * ε j *
          ((((subsets k (r + 1)).filter (fun I => i ∈ I ∧ j ∉ I)).card : ℕ) : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    split_ifs <;> simp
  have hcount : ∀ i j : Fin k,
      ((((subsets k (r + 1)).filter (fun I => i ∈ I ∧ j ∉ I)).card : ℕ) : ℝ)
        = if i = j then 0 else c := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, card_in_out r hij]
  have hrow : ∀ i : Fin k, ∑ j, ε i * ε j * (if i = j then 0 else c)
      = c * (ε i * ∑ j, ε j) - c * ε i ^ 2 := by
    intro i
    have e : ∀ j, ε i * ε j * (if i = j then 0 else c)
        = c * (ε i * ε j) - (if i = j then c * (ε i * ε j) else 0) := by
      intro j; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i), ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  calc ∑ I ∈ subsets k (r + 1), (∑ i ∈ I, ε i) ^ 2
      = -∑ I ∈ subsets k (r + 1), ∑ i, ∑ j, (if i ∈ I ∧ j ∉ I then ε i * ε j else 0) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun I _ => hsq I)
    _ = -∑ i, ∑ j, ε i * ε j * (if i = j then 0 else c) := by
        rw [hswap]
        simp only [hcount]
    _ = c * ∑ i, ε i ^ 2 := by
        rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_sub_distrib]
        simp only [hε, mul_zero, Finset.sum_const_zero, zero_sub, neg_neg, ← Finset.mul_sum]

/-- Prop. app-shuffled-spectrum: `μ_I = (1 + δ_I)/D` with `δ_I = (1/r) ∑_{i∈I} ε_i`. -/
lemma shuffle_repr {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (q : Fin k → ℝ)
    (I : Finset (Fin k)) (hI : I.card = r) :
    shuffle k r q I
      = (1 + (∑ i ∈ I, ((k : ℝ) * q i - 1)) / r) / (Nat.choose k r : ℝ) := by
  have hk : 1 ≤ k := le_trans hr hrk
  have h1 := choose_mul_left hr hk
  have hN : (0 : ℝ) < (Nat.choose (k - 1) (r - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hD : (0 : ℝ) < (Nat.choose k r : ℝ) := by exact_mod_cast Nat.choose_pos hrk
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : ∑ i ∈ I, ((k : ℝ) * q i - 1) = k * ∑ i ∈ I, q i - r := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hI, nsmul_eq_mul, mul_one]
  simp only [shuffle]
  rw [hsum]
  have e : 1 + ((k : ℝ) * ∑ i ∈ I, q i - r) / r = (k : ℝ) * (∑ i ∈ I, q i) / r := by
    field_simp <;> ring
  rw [e, div_div, ← h1]
  field_simp <;> ring

/-! ## 8. The localization bound (app-ct-bound) -/

/-- (app-ct-bound), squared: `(u-t)² ≤ c_t(u) (2√(t(1-t)) + √(2 c_t(u)))²`. -/
lemma ct_bound {t u : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u - t) ^ 2 ≤ ct t u * (2 * Real.sqrt (t * (1 - t)) + Real.sqrt (2 * ct t u)) ^ 2 := by
  have h1t : 0 ≤ 1 - t := by linarith
  have h1u : 0 ≤ 1 - u := by linarith
  have hc : ct t u = (Real.sqrt t * Real.sqrt (1 - u) - Real.sqrt (1 - t) * Real.sqrt u) ^ 2 := by
    simp only [ct]
    rw [Real.sqrt_mul ht0.le, Real.sqrt_mul h1t]
  have hab : Real.sqrt (t * (1 - t)) = Real.sqrt t * Real.sqrt (1 - t) := Real.sqrt_mul ht0.le _
  rw [hc, hab]
  set a := Real.sqrt t with ha_def
  set b := Real.sqrt (1 - t) with hb_def
  set x := Real.sqrt u with hx_def
  set y := Real.sqrt (1 - u) with hy_def
  have ha : a ^ 2 = t := Real.sq_sqrt ht0.le
  have hb : b ^ 2 = 1 - t := Real.sq_sqrt h1t
  have hx : x ^ 2 = u := Real.sq_sqrt hu0
  have hy : y ^ 2 = 1 - u := Real.sq_sqrt h1u
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hut : u - t = (b * x - a * y) * (b * x + a * y) := by
    linear_combination (-x ^ 2) * hb + (-(1 - t)) * hx + y ^ 2 * ha + t * hy
  have hlag : (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 = 1 := by
    linear_combination (x ^ 2 + y ^ 2) * ha + (x ^ 2 + y ^ 2) * hb + hx + hy
  have hs0 : 0 ≤ a * x + b * y := by positivity
  have hs1 : a * x + b * y ≤ 1 := by nlinarith [sq_nonneg (a * y - b * x)]
  have hdist : (x - a) ^ 2 + (y - b) ^ 2 = 2 - 2 * (a * x + b * y) := by
    linear_combination hx + hy + ha + hb
  have hdist2 : (x - a) ^ 2 + (y - b) ^ 2 ≤ 2 * (a * y - b * x) ^ 2 := by
    rw [hdist]
    nlinarith [hlag, mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 - (a * x + b * y))]
  have hab1 : a ^ 2 + b ^ 2 = 1 := by rw [ha, hb]; ring
  have hlag2 : (b * (x - a) + a * (y - b)) ^ 2 + (b * (y - b) - a * (x - a)) ^ 2
      = (a ^ 2 + b ^ 2) * ((x - a) ^ 2 + (y - b) ^ 2) := by ring
  rw [hab1, one_mul] at hlag2
  have hcs : (b * x + a * y - 2 * (a * b)) ^ 2 ≤ 2 * (a * y - b * x) ^ 2 := by
    have e : b * x + a * y - 2 * (a * b) = b * (x - a) + a * (y - b) := by ring
    rw [e]
    nlinarith [sq_nonneg (b * (y - b) - a * (x - a)), hlag2, hdist2]
  have hsq : |b * x + a * y - 2 * (a * b)| ≤ Real.sqrt (2 * (a * y - b * x) ^ 2) :=
    Real.abs_le_sqrt hcs
  have hbxay : b * x + a * y ≤ 2 * (a * b) + Real.sqrt (2 * (a * y - b * x) ^ 2) := by
    have := le_abs_self (b * x + a * y - 2 * (a * b))
    linarith
  have hpos : 0 ≤ b * x + a * y := by positivity
  rw [hut]
  calc ((b * x - a * y) * (b * x + a * y)) ^ 2
      = (a * y - b * x) ^ 2 * (b * x + a * y) ^ 2 := by ring
    _ ≤ (a * y - b * x) ^ 2 * (2 * (a * b) + Real.sqrt (2 * (a * y - b * x) ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left hpos hbxay 2) (sq_nonneg _)

/-- The sum of `f` over `(u₊, u₋, t, …, t)`. -/
lemma sum_cons2 (n : ℕ) (a b c : ℝ) (f : ℝ → ℝ) :
    ∑ i : Fin (n + 2),
        f ((Fin.cons a (Fin.cons b (fun _ : Fin n => c) : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ) i)
      = f a + f b + n * f c := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- For `q = u / ∑u`: `∑ (k q_i - 1)² = (k² ∑ w_i² - k (∑ w_i)²) / (∑ u)²`, `w = u - t`. -/
lemma eps_sq_sum {k : ℕ} (t : ℝ) (u : Fin k → ℝ) (hS : ∑ j, u j ≠ 0) :
    ∑ i, ((k : ℝ) * (u i / ∑ j, u j) - 1) ^ 2
      = ((k : ℝ) ^ 2 * ∑ i, (u i - t) ^ 2 - k * (∑ i, (u i - t)) ^ 2) / (∑ j, u j) ^ 2 := by
  set S := ∑ j, u j with hS_def
  set W := ∑ i, (u i - t) with hW
  have hSW : S = k * t + W := by
    rw [hW, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have e : ∀ i, (k : ℝ) * (u i / S) - 1 = ((k : ℝ) * (u i - t) - W) / S := by
    intro i
    field_simp
    rw [hSW]
    ring
  simp only [e, div_pow]
  rw [← Finset.sum_div]
  congr 1
  have e2 : ∀ i, ((k : ℝ) * (u i - t) - W) ^ 2
      = (k : ℝ) ^ 2 * (u i - t) ^ 2 - 2 * k * W * (u i - t) + W ^ 2 := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← hW]
  ring

/-! ## 9. Proposition app-localization -/

lemma sqrt_tt_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : Real.sqrt (t * (1 - t)) ≤ 1 / 2 := by
  calc Real.sqrt (t * (1 - t)) ≤ Real.sqrt ((1 / 2) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (t - 1 / 2)])
    _ = 1 / 2 := Real.sqrt_sq (by norm_num)

/-- Pure arithmetic: the last step of Prop. app-localization (i), with `k = s²`. -/
lemma loc_final {t s B : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : 4 ≤ s) (hkt : 16 ≤ s ^ 2 * t)
    (hB : B ^ 2 ≤ 4 * (t * (1 - t)) + 6 / s) :
    s ^ 2 * B ^ 2 / (s ^ 2 * t - 2) ^ 2
      ≤ 4 * ((1 - t) / t) / s ^ 2 + 200 / t ^ 3 / (s ^ 2 * s) := by
  have hs0 : 0 < s := by linarith
  have hs0' := hs0.ne'
  have ht0' := ht0.ne'
  set x := s ^ 2 * t with hx
  have hx0 : 0 < x := by linarith
  have hx2 : 0 < x - 2 := by linarith
  have hx0' := hx0.ne'
  have h1 : s ^ 2 / (x - 2) ^ 2 ≤ (1 + 8 / x) / (t ^ 2 * s ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : s ^ 2 * (t ^ 2 * s ^ 2) = x ^ 2 := by rw [hx]; ring
    rw [e]
    have e2 : (1 + 8 / x) * (x - 2) ^ 2 = (x + 8) * (x - 2) ^ 2 / x := by
      field_simp
    rw [e2, le_div_iff₀ hx0]
    nlinarith [mul_le_mul_of_nonneg_left hkt hx0.le]
  have h8 : 8 / x ≤ 1 / 2 := by rw [div_le_iff₀ hx0]; linarith
  have h80 : 0 ≤ 8 / x := by positivity
  have h2 : B ^ 2 * (1 + 8 / x) ≤ 4 * (t * (1 - t)) + 17 / s := by
    have hB' : B ^ 2 * (1 + 8 / x) ≤ (4 * (t * (1 - t)) + 6 / s) * (1 + 8 / x) :=
      mul_le_mul_of_nonneg_right hB (by linarith)
    have e : 4 * (t * (1 - t)) * (8 / x) = 32 * (1 - t) / s ^ 2 := by
      rw [hx]; field_simp <;> ring
    have h3 : 32 * (1 - t) / s ^ 2 ≤ 8 / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      nlinarith [mul_nonneg hs0.le (by linarith : (0 : ℝ) ≤ s - 4 * (1 - t))]
    have h4 : 6 / s * (1 + 8 / x) ≤ 9 / s := by
      have h5 : 6 / s * (1 + 8 / x) ≤ 6 / s * (3 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h6 : 6 / s * (3 / 2) = 9 / s := by ring
      linarith
    have e2 : (4 * (t * (1 - t)) + 6 / s) * (1 + 8 / x)
        = 4 * (t * (1 - t)) + 4 * (t * (1 - t)) * (8 / x) + 6 / s * (1 + 8 / x) := by ring
    linarith [hB', e2, e, h3, h4]
  calc s ^ 2 * B ^ 2 / (x - 2) ^ 2 = B ^ 2 * (s ^ 2 / (x - 2) ^ 2) := by ring
    _ ≤ B ^ 2 * ((1 + 8 / x) / (t ^ 2 * s ^ 2)) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = B ^ 2 * (1 + 8 / x) / (t ^ 2 * s ^ 2) := by ring
    _ ≤ (4 * (t * (1 - t)) + 17 / s) / (t ^ 2 * s ^ 2) :=
        div_le_div_of_nonneg_right h2 (by positivity)
    _ = 4 * ((1 - t) / t) / s ^ 2 + 17 / (t ^ 2 * (s ^ 2 * s)) := by
        field_simp <;> ring
    _ ≤ 4 * ((1 - t) / t) / s ^ 2 + 200 / t ^ 3 / (s ^ 2 * s) := by
        have h7 : 17 / (t ^ 2 * (s ^ 2 * s)) ≤ 200 / t ^ 3 / (s ^ 2 * s) := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h9 : 0 ≤ t ^ 2 * (s ^ 2 * s) := by positivity
          nlinarith [mul_nonneg h9 (by linarith : (0 : ℝ) ≤ 200 - 17 * t)]
        linarith

/-- Prop. app-localization (i). -/
lemma localization {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ C k₀ : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ (k : ℝ) → ∀ q ∈ Lam k t,
      (∑ i, q i = 1) ∧ (∀ i, 0 ≤ q i) ∧
      (∀ i, |(k : ℝ) * q i - 1| ≤ C / Real.sqrt k) ∧
      ∑ i, ((k : ℝ) * q i - 1) ^ 2 ≤ 4 * ((1 - t) / t) / k + C / (k * Real.sqrt k) := by
  refine ⟨200 / t ^ 3, max 16 (16 / t), by positivity, fun k hk q hq => ?_⟩
  obtain ⟨u, ⟨hu01, hct⟩, rfl⟩ := hq
  beta_reduce
  have hk16 : (16 : ℝ) ≤ k := le_trans (le_max_left _ _) hk
  have hkt : 16 ≤ (k : ℝ) * t := by
    have := le_trans (le_max_right _ _) hk
    rw [div_le_iff₀ ht0] at this
    linarith
  have hkpos : (0 : ℝ) < k := by linarith
  have ht1' : t ^ 2 ≤ 1 := by nlinarith
  set s := Real.sqrt k with hs_def
  have hs2 : s ^ 2 = k := Real.sq_sqrt hkpos.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hkpos
  have hs4 : 4 ≤ s := by nlinarith
  have hc0 : ∀ i, 0 ≤ ct t (u i) := fun i => sq_nonneg _
  have hci : ∀ i, ct t (u i) ≤ 1 / k := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => hc0 j) (Finset.mem_univ i)) hct
  have hT := sqrt_tt_le ht0 ht1
  have hT0 : 0 ≤ Real.sqrt (t * (1 - t)) := Real.sqrt_nonneg _
  have hTsq : Real.sqrt (t * (1 - t)) ^ 2 = t * (1 - t) := Real.sq_sqrt (by nlinarith)
  have h2s : 0 < 2 / s := by positivity
  have h2s' : 2 / s ≤ 1 / 2 := by rw [div_le_iff₀ hs0]; linarith
  have hci2 : ∀ i, Real.sqrt (2 * ct t (u i)) ≤ 2 / s := by
    intro i
    calc Real.sqrt (2 * ct t (u i)) ≤ Real.sqrt ((2 / s) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_pow, hs2]
          have h1 := hci i
          calc 2 * ct t (u i) ≤ 2 * (1 / k) := by linarith
            _ ≤ 2 ^ 2 / k := by
                rw [mul_one_div]
                exact div_le_div_of_nonneg_right (by norm_num) hkpos.le
      _ = 2 / s := Real.sqrt_sq h2s.le
  set B := 2 * Real.sqrt (t * (1 - t)) + 2 / s with hB
  have hB0 : 0 ≤ B := by positivity
  have hB2 : B ≤ 2 := by rw [hB]; linarith
  have hBsq : B ^ 2 ≤ 4 * (t * (1 - t)) + 6 / s := by
    have h2 : (2 / s) ^ 2 ≤ 2 / s := by
      nlinarith [mul_nonneg h2s.le (by linarith : (0 : ℝ) ≤ 1 - 2 / s)]
    have e : B ^ 2 = 4 * Real.sqrt (t * (1 - t)) ^ 2
        + 4 * Real.sqrt (t * (1 - t)) * (2 / s) + (2 / s) ^ 2 := by rw [hB]; ring
    rw [e, hTsq]
    have h3 : 4 * Real.sqrt (t * (1 - t)) * (2 / s) ≤ 4 * (1 / 2) * (2 / s) := by
      have := mul_le_mul_of_nonneg_right hT h2s.le
      nlinarith [this]
    have h4 : 4 * (1 / 2) * (2 / s) = 4 / s := by ring
    have h5 : 4 / s + 2 / s = 6 / s := by ring
    linarith
  have hw2 : ∀ i, (u i - t) ^ 2 ≤ ct t (u i) * B ^ 2 := by
    intro i
    have h1 := ct_bound ht0 ht1 (hu01 i).1 (hu01 i).2
    have h3 : 0 ≤ 2 * Real.sqrt (t * (1 - t)) + Real.sqrt (2 * ct t (u i)) := by positivity
    have h2 : 2 * Real.sqrt (t * (1 - t)) + Real.sqrt (2 * ct t (u i)) ≤ B := by
      rw [hB]; linarith [hci2 i]
    calc (u i - t) ^ 2
        ≤ ct t (u i) * (2 * Real.sqrt (t * (1 - t)) + Real.sqrt (2 * ct t (u i))) ^ 2 := h1
      _ ≤ ct t (u i) * B ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left h3 h2 2) (hc0 i)
  have hWsq : ∑ i, (u i - t) ^ 2 ≤ B ^ 2 / k := by
    calc ∑ i, (u i - t) ^ 2 ≤ ∑ i, ct t (u i) * B ^ 2 := Finset.sum_le_sum (fun i _ => hw2 i)
      _ = (∑ i, ct t (u i)) * B ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (1 / k) * B ^ 2 := mul_le_mul_of_nonneg_right hct (sq_nonneg _)
      _ = B ^ 2 / k := by ring
  have hwi : ∀ i, |u i - t| ≤ 2 / s := by
    intro i
    have h1 : (u i - t) ^ 2 ≤ (2 / s) ^ 2 := by
      calc (u i - t) ^ 2 ≤ ct t (u i) * B ^ 2 := hw2 i
        _ ≤ (1 / k) * 2 ^ 2 :=
            mul_le_mul (hci i) (pow_le_pow_left hB0 hB2 2) (sq_nonneg _) (by positivity)
        _ = (2 / s) ^ 2 := by rw [div_pow, hs2]; ring
    have := sq_le_sq.mp h1
    rwa [abs_of_pos h2s] at this
  have hsumw : |∑ i, (u i - t)| ≤ 2 := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin k => (1 : ℝ))
      (fun i => u i - t)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h1
    have h2 : (k : ℝ) * ∑ i, (u i - t) ^ 2 ≤ 2 ^ 2 := by
      calc (k : ℝ) * ∑ i, (u i - t) ^ 2 ≤ k * (B ^ 2 / k) :=
            mul_le_mul_of_nonneg_left hWsq hkpos.le
        _ = B ^ 2 := by field_simp
        _ ≤ 2 ^ 2 := pow_le_pow_left hB0 hB2 2
    have h3 : (∑ i, (u i - t)) ^ 2 ≤ 2 ^ 2 := le_trans h1 h2
    have := sq_le_sq.mp h3
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
  have hSW : ∑ i, u i = k * t + ∑ i, (u i - t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hSlo : (k : ℝ) * t - 2 ≤ ∑ i, u i := by
    rw [hSW]; have := abs_le.mp hsumw; linarith
  have hS0 : 0 < ∑ i, u i := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hS0.ne']
  · intro i
    exact div_nonneg (hu01 i).1 hS0.le
  · intro i
    have e : (k : ℝ) * (u i / ∑ j, u j) - 1
        = ((k : ℝ) * (u i - t) - ∑ j, (u j - t)) / ∑ j, u j := by
      have := hS0.ne'
      field_simp
      rw [hSW]
      ring
    rw [e, abs_div, abs_of_pos hS0, div_le_iff₀ hS0]
    have h1 : |(k : ℝ) * (u i - t) - ∑ j, (u j - t)| ≤ k * (2 / s) + 2 := by
      calc |(k : ℝ) * (u i - t) - ∑ j, (u j - t)|
          ≤ |(k : ℝ) * (u i - t)| + |∑ j, (u j - t)| := abs_sub _ _
        _ = k * |u i - t| + |∑ j, (u j - t)| := by rw [abs_mul, abs_of_pos hkpos]
        _ ≤ k * (2 / s) + 2 := by
            have := mul_le_mul_of_nonneg_left (hwi i) hkpos.le
            linarith [hsumw]
    have h2 : (k : ℝ) * (2 / s) = 2 * s := by
      rw [← hs2]; field_simp <;> ring
    have h3 : (k : ℝ) * t / 2 ≤ ∑ j, u j := by linarith
    have h4 : 200 / t ^ 3 / s * ((k : ℝ) * t / 2) ≤ 200 / t ^ 3 / s * ∑ j, u j :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 2 * s + 2 ≤ 200 / t ^ 3 / s * ((k : ℝ) * t / 2) := by
      rw [← hs2]
      have e2 : 200 / t ^ 3 / s * (s ^ 2 * t / 2) = 100 * s / t ^ 2 := by
        have := hs0.ne'; have := ht0.ne'
        field_simp <;> ring
      rw [e2, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left ht1' (by linarith : (0 : ℝ) ≤ 2 * s + 2)]
    linarith [h1, h2, h4, h5]
  · rw [eps_sq_sum t u hS0.ne']
    have hnum : (k : ℝ) ^ 2 * ∑ i, (u i - t) ^ 2 - k * (∑ i, (u i - t)) ^ 2 ≤ k * B ^ 2 := by
      have h1 : (k : ℝ) ^ 2 * ∑ i, (u i - t) ^ 2 ≤ (k : ℝ) ^ 2 * (B ^ 2 / k) :=
        mul_le_mul_of_nonneg_left hWsq (by positivity)
      have h2 : (k : ℝ) ^ 2 * (B ^ 2 / k) = k * B ^ 2 := by field_simp <;> ring
      have h3 : 0 ≤ (k : ℝ) * (∑ i, (u i - t)) ^ 2 := by positivity
      linarith
    have hden0 : 0 < ((k : ℝ) * t - 2) ^ 2 := pow_pos (by linarith) 2
    have hden : ((k : ℝ) * t - 2) ^ 2 ≤ (∑ j, u j) ^ 2 := pow_le_pow_left (by linarith) hSlo 2
    have hfin := loc_final ht0 ht1 hs4 (by rw [hs2]; exact hkt) hBsq
    rw [hs2] at hfin
    calc ((k : ℝ) ^ 2 * ∑ i, (u i - t) ^ 2 - k * (∑ i, (u i - t)) ^ 2) / (∑ j, u j) ^ 2
        ≤ (k * B ^ 2) / (∑ j, u j) ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ (k * B ^ 2) / ((k : ℝ) * t - 2) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hden0 hden
      _ ≤ 4 * ((1 - t) / t) / k + 200 / t ^ 3 / (k * s) := hfin

/-- Pure arithmetic: the last step of Prop. app-localization (ii). -/
lemma spike_final {t K N S : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hK : 2 ≤ K)
    (hN0 : 0 ≤ 4 * t * (1 - t) * K - 1) (hN : 4 * t * (1 - t) * K - 1 ≤ N)
    (hS0 : 0 < S) (hS : S ≤ K * t + 1 / K) :
    4 * ((1 - t) / t) / K - 8 / t ^ 3 / K ^ 2 ≤ N / S ^ 2 := by
  have hK0 : 0 < K := by linarith
  have ht0' := ht0.ne'
  have hK0' := hK0.ne'
  set A := 4 * t * (1 - t) * K - 1 with hA
  set D := (K * t + 1 / K) ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hDlo : t ^ 2 * K ^ 2 ≤ D := by
    rw [hD]
    have h1 : 0 ≤ 1 / K := by positivity
    nlinarith [sq_nonneg (1 / K), mul_nonneg (mul_nonneg hK0.le ht0.le) h1]
  have hDhi : D - t ^ 2 * K ^ 2 ≤ 3 := by
    rw [hD]
    have e : (K * t + 1 / K) ^ 2 - t ^ 2 * K ^ 2 = 2 * t + 1 / K ^ 2 := by
      field_simp <;> ring
    rw [e]
    have : 1 / K ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hAhi : A ≤ 4 * t * K := by
    rw [hA]; nlinarith [mul_pos (mul_pos ht0 ht0) hK0]
  have hAD : A / D ≤ N / S ^ 2 := by
    calc A / D ≤ N / D := div_le_div_of_nonneg_right hN hD0.le
      _ ≤ N / S ^ 2 :=
          div_le_div_of_nonneg_left (le_trans hN0 hN) (by positivity) (pow_le_pow_left hS0.le hS 2)
  have key : 4 * ((1 - t) / t) / K - A / D ≤ 8 / t ^ 3 / K ^ 2 := by
    have e1 : 4 * ((1 - t) / t) / K = (A + 1) / (t ^ 2 * K ^ 2) := by
      rw [hA]; field_simp <;> ring
    rw [e1, div_sub_div _ _ (by positivity) hD0.ne', div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (A + 1) * D - t ^ 2 * K ^ 2 * A ≤ 3 * A + D := by
      nlinarith [mul_le_mul_of_nonneg_left hDhi hN0]
    have h2 : 0 ≤ t ^ 3 * K ^ 2 := by positivity
    have h3 : ((A + 1) * D - t ^ 2 * K ^ 2 * A) * (t ^ 3 * K ^ 2)
        ≤ (3 * A + D) * (t ^ 3 * K ^ 2) := mul_le_mul_of_nonneg_right h1 h2
    have h4 : (3 * A + D) * (t ^ 3 * K ^ 2) ≤ (12 * t * K + D) * (t ^ 3 * K ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    have h7 : 12 * t ^ 2 * K ≤ (8 - t) * D := by
      have i1 : (8 - t) * (t ^ 2 * K ^ 2) ≤ (8 - t) * D :=
        mul_le_mul_of_nonneg_left hDlo (by linarith)
      have i2 : 7 * (t ^ 2 * K ^ 2) ≤ (8 - t) * (t ^ 2 * K ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have i3 : t ^ 2 * K * 2 ≤ t ^ 2 * K * K :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      have i4 : 0 ≤ t ^ 2 * K := by positivity
      nlinarith [i1, i2, i3, i4]
    have h5 : (12 * t * K + D) * (t ^ 3 * K ^ 2) ≤ 8 * (t ^ 2 * K ^ 2 * D) := by
      have h6 : 0 ≤ t ^ 2 * K ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h7 h6]
    linarith [h3, h4, h5]
  linarith [hAD, key]

/-- Prop. app-localization (ii): the two-spike point `u* = (u₊, u₋, t, …, t)`. -/
lemma two_spike {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ C k₀ : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      ∃ q ∈ Lam k t, 4 * ((1 - t) / t) / k - C / k ^ 2 ≤ ∑ i, ((k : ℝ) * q i - 1) ^ 2 := by
  refine ⟨8 / t ^ 3, max 2 (max (1 / (2 * t)) (1 / (2 * (1 - t)))), by positivity,
    fun k hk => ?_⟩
  have hk2 : (2 : ℝ) ≤ k := le_trans (le_max_left _ _) hk
  have hka : 1 / (2 * t) ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkb : 1 / (2 * (1 - t)) ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hk2n : 2 ≤ k := by exact_mod_cast hk2
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  set K : ℝ := ((n + 2 : ℕ) : ℝ) with hK
  have hK0 : 0 < K := by linarith
  have hKa : 1 ≤ 2 * t * K := by
    rw [div_le_iff₀ (by positivity)] at hka; linarith
  have hKb : 1 ≤ 2 * (1 - t) * K := by
    rw [div_le_iff₀ (by have : 0 < 1 - t := by linarith; positivity)] at hkb; linarith
  have h1t : 0 < 1 - t := by linarith
  obtain ⟨a, ha_def⟩ : ∃ a, a = Real.sqrt t := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, b = Real.sqrt (1 - t) := ⟨_, rfl⟩
  obtain ⟨σ, hσ_def⟩ : ∃ σ, σ = Real.sqrt (1 / (2 * K)) := ⟨_, rfl⟩
  obtain ⟨cs, hcs_def⟩ : ∃ cs, cs = Real.sqrt (1 - 1 / (2 * K)) := ⟨_, rfl⟩
  have hσK : 1 / (2 * K) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have ha : a ^ 2 = t := by rw [ha_def]; exact Real.sq_sqrt ht0.le
  have hb : b ^ 2 = 1 - t := by rw [hb_def]; exact Real.sq_sqrt h1t.le
  have hσ : σ ^ 2 = 1 / (2 * K) := by rw [hσ_def]; exact Real.sq_sqrt (by positivity)
  have hcs : cs ^ 2 = 1 - 1 / (2 * K) := by
    rw [hcs_def]; exact Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ a := by rw [ha_def]; exact Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := by rw [hb_def]; exact Real.sqrt_nonneg _
  have hσ0 : 0 ≤ σ := by rw [hσ_def]; exact Real.sqrt_nonneg _
  have hcs0 : 0 ≤ cs := by rw [hcs_def]; exact Real.sqrt_nonneg _
  have hσt : 1 / (2 * K) ≤ t := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hσ1t : 1 / (2 * K) ≤ 1 - t := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hsum1 : a ^ 2 + b ^ 2 = 1 := by rw [ha, hb]; ring
  have hsum2 : cs ^ 2 + σ ^ 2 = 1 := by rw [hcs, hσ]; ring
  -- `b σ ≤ a cs` and `a σ ≤ b cs`
  have hle1 : b * σ ≤ a * cs := by
    have h1 : (b * σ) ^ 2 ≤ (a * cs) ^ 2 := by
      rw [mul_pow, mul_pow, ha, hb, hσ, hcs]; nlinarith [hσt]
    calc b * σ = Real.sqrt ((b * σ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((a * cs) ^ 2) := Real.sqrt_le_sqrt h1
      _ = a * cs := Real.sqrt_sq (by positivity)
  have hle2 : a * σ ≤ b * cs := by
    have h1 : (a * σ) ^ 2 ≤ (b * cs) ^ 2 := by
      rw [mul_pow, mul_pow, ha, hb, hσ, hcs]; nlinarith [hσ1t]
    calc a * σ = Real.sqrt ((a * σ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((b * cs) ^ 2) := Real.sqrt_le_sqrt h1
      _ = b * cs := Real.sqrt_sq (by positivity)
  set up := (a * cs + b * σ) ^ 2 with hup
  set um := (a * cs - b * σ) ^ 2 with hum
  have hup1 : 1 - up = (b * cs - a * σ) ^ 2 := by
    rw [hup]; linear_combination (-(cs ^ 2 + σ ^ 2)) * hsum1 - hsum2
  have hum1 : 1 - um = (b * cs + a * σ) ^ 2 := by
    rw [hum]; linear_combination (-(cs ^ 2 + σ ^ 2)) * hsum1 - hsum2
  have hctp : ct t up = σ ^ 2 := by
    unfold ct
    rw [hup1, Real.sqrt_mul ht0.le, Real.sqrt_mul h1t.le, ← ha_def, ← hb_def,
      Real.sqrt_sq (by linarith : 0 ≤ b * cs - a * σ), hup,
      Real.sqrt_sq (by positivity : 0 ≤ a * cs + b * σ)]
    linear_combination σ ^ 2 * (a ^ 2 + b ^ 2 + 1) * hsum1
  have hctm : ct t um = σ ^ 2 := by
    unfold ct
    rw [hum1, Real.sqrt_mul ht0.le, Real.sqrt_mul h1t.le, ← ha_def, ← hb_def,
      Real.sqrt_sq (by positivity : 0 ≤ b * cs + a * σ), hum,
      Real.sqrt_sq (by linarith : 0 ≤ a * cs - b * σ)]
    linear_combination σ ^ 2 * (a ^ 2 + b ^ 2 + 1) * hsum1
  have hctt : ct t t = 0 := by simp [ct, mul_comm]
  have hup01 : 0 ≤ up ∧ up ≤ 1 := ⟨by positivity, by nlinarith [hup1, sq_nonneg (b * cs - a * σ)]⟩
  have hum01 : 0 ≤ um ∧ um ≤ 1 := ⟨by positivity, by nlinarith [hum1, sq_nonneg (b * cs + a * σ)]⟩
  -- the point `u*`
  set ustar : Fin (n + 2) → ℝ :=
    (Fin.cons up (Fin.cons um (fun _ : Fin n => t) : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ)
    with hustar
  have hsum_ct : ∑ i, ct t (ustar i) = 1 / K := by
    rw [hustar, sum_cons2 n up um t (ct t), hctp, hctm, hctt, hσ]
    ring
  have hmem : ustar ∈ Dset (n + 2) t := by
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hustar] using hup01
      · refine Fin.cases ?_ (fun l => ?_) j
        · simpa [hustar] using hum01
        · simp only [hustar, Fin.cons_succ]
          exact ⟨ht0.le, ht1.le⟩
    · rw [hsum_ct]
  -- sums over `u*`
  have hw1 : up - t = (b ^ 2 - a ^ 2) * σ ^ 2 + 2 * a * b * cs * σ := by
    rw [hup]; linear_combination a ^ 2 * hsum2 + ha
  have hw2 : um - t = (b ^ 2 - a ^ 2) * σ ^ 2 - 2 * a * b * cs * σ := by
    rw [hum]; linear_combination a ^ 2 * hsum2 + ha
  have hSum : ∑ i, ustar i = up + um + n * t := by
    rw [hustar, sum_cons2 n up um t (fun x => x)]
  have hW : ∑ i, (ustar i - t) = (1 - 2 * t) / K := by
    rw [hustar, sum_cons2 n up um t (fun x => x - t), hw1, hw2, hσ, ha, hb]
    field_simp <;> ring
  have hW2 : ∑ i, (ustar i - t) ^ 2 ≥ 4 * t * (1 - t) * (1 - 1 / (2 * K)) / K := by
    rw [hustar, sum_cons2 n up um t (fun x => (x - t) ^ 2)]
    simp only [sub_self]
    rw [hw1, hw2]
    have e : ((b ^ 2 - a ^ 2) * σ ^ 2 + 2 * a * b * cs * σ) ^ 2
        + ((b ^ 2 - a ^ 2) * σ ^ 2 - 2 * a * b * cs * σ) ^ 2 + (n : ℝ) * 0 ^ 2
        = 2 * ((b ^ 2 - a ^ 2) * σ ^ 2) ^ 2 + 8 * (a ^ 2 * b ^ 2) * (cs ^ 2 * σ ^ 2) := by ring
    rw [e, ha, hb, hcs, hσ]
    have h1 : 0 ≤ 2 * (((1 - t) - t) * (1 / (2 * K))) ^ 2 := by positivity
    have e2 : 8 * (t * (1 - t)) * ((1 - 1 / (2 * K)) * (1 / (2 * K)))
        = 4 * t * (1 - t) * (1 - 1 / (2 * K)) / K := by
      field_simp <;> ring
    linarith [h1, e2]
  have hS0 : 0 < ∑ i, ustar i := by
    rw [hSum]; have := hup01.1; have := hum01.1; positivity
  have hSeq : ∑ i, ustar i = K * t + (1 - 2 * t) / K := by
    have h := hW
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    linarith
  refine ⟨fun i => ustar i / ∑ j, ustar j, ⟨ustar, hmem, rfl⟩, ?_⟩
  rw [eps_sq_sum t ustar hS0.ne']
  apply spike_final ht0 ht1 hk2
  · nlinarith [mul_le_mul_of_nonneg_left hKb (by linarith : (0 : ℝ) ≤ 2 * t),
      mul_le_mul_of_nonneg_left hKa (by linarith : (0 : ℝ) ≤ 2 * (1 - t))]
  · -- the numerator: `K² ∑ w² - K (∑ w)² ≥ 4 t (1-t) K - 1`
    rw [hW]
    have h1 : K ^ 2 * (4 * t * (1 - t) * (1 - 1 / (2 * K)) / K)
        ≤ K ^ 2 * ∑ i, (ustar i - t) ^ 2 := mul_le_mul_of_nonneg_left hW2 (by positivity)
    have e1 : K ^ 2 * (4 * t * (1 - t) * (1 - 1 / (2 * K)) / K)
        = 4 * t * (1 - t) * K - 2 * t * (1 - t) := by field_simp <;> ring
    have e2 : K * ((1 - 2 * t) / K) ^ 2 = (1 - 2 * t) ^ 2 / K := by field_simp <;> ring
    have h2 : (1 - 2 * t) ^ 2 / K ≤ 1 / 2 := by
      rw [div_le_iff₀ hK0]; nlinarith
    have h3 : 2 * t * (1 - t) ≤ 1 / 2 := by nlinarith [sq_nonneg (2 * t - 1)]
    linarith [h1, e1, e2, h2, h3]
  · exact hS0
  · rw [hSeq]
    have : (1 - 2 * t) / K ≤ 1 / K := div_le_div_of_nonneg_right (by linarith) hK0.le
    linarith

/-! ## 10. Propositions app-single-entropy-asymptotics (26) and
    app-antisymmetric-single-entropy-asymptotics (65) -/

/-- `k C(k-1, r) = (k - r) C(k, r)` for all `r` (the case `r = 0` included). -/
lemma choose_mul_right' {k r : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * (Nat.choose (k - 1) r : ℝ) = ((k : ℝ) - r) * (Nat.choose k r : ℝ) := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp
  · exact choose_mul_right h hk

/-- The coefficient in (app-quadratic-form): `C(k-2, r-1) / (r² C(k,r)) = (k-r)/(r k (k-1))`. -/
lemma quad_coeff {k r' : ℕ} (hk : r' + 2 ≤ k) :
    ((k - 2).choose r' : ℝ) / (((r' + 1 : ℕ) : ℝ) ^ 2 * (Nat.choose k (r' + 1) : ℝ))
      = ((k : ℝ) - (r' + 1 : ℕ)) / (((r' + 1 : ℕ) : ℝ) * k * ((k : ℝ) - 1)) := by
  have hk1 : 1 ≤ k := by omega
  have hk1' : 1 ≤ k - 1 := by omega
  have h1 := choose_mul_left (k := k) (r := r' + 1) (by omega) hk1
  have h2 := choose_mul_right' (k := k - 1) (r := r') hk1'
  simp only [Nat.add_sub_cancel] at h1
  have e1 : k - 1 - 1 = k - 2 := by omega
  rw [e1] at h2
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by push_cast [Nat.cast_sub hk1]; ring
  rw [hc] at h2
  have hR : (0 : ℝ) < ((r' + 1 : ℕ) : ℝ) := by positivity
  have hD : (0 : ℝ) < (Nat.choose k (r' + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk10 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
    linarith
  rw [div_eq_div_iff (by positivity) (by positivity)]
  -- C(k-2,r') (R k (k-1)) = (k - R) R² D, from h1 : k C(k-1,r') = R D and
  -- h2 : (k-1) C(k-2,r') = ((k-1) - r') C(k-1,r')
  have hRc : ((r' + 1 : ℕ) : ℝ) = (r' : ℝ) + 1 := by push_cast; ring
  rw [hRc] at h1 ⊢
  linear_combination ((r' : ℝ) + 1) * (k : ℝ) * h2
    + ((r' : ℝ) + 1) * ((k : ℝ) - 1 - r') * h1

lemma renyi_r1 (p : ℝ) {k : ℕ} (q : Fin k → ℝ) :
    renyi p (subsets k 1) (fun _ => 1) (shuffle k 1 q) = renyi p Finset.univ (fun _ => 1) q := by
  have hsum : ∀ g : ℝ → ℝ, ∑ I ∈ subsets k 1, g (shuffle k 1 q I) = ∑ i, g (q i) := by
    intro g
    rw [subsets, Finset.powersetCard_one, Finset.sum_map]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [shuffle]
  unfold renyi
  beta_reduce
  split_ifs
  · have := hsum (fun x => 1 * (x * Real.log x))
    simp only at this
    rw [this]
  · have := hsum (fun x => 1 * x ^ p)
    simp only at this
    rw [this]

/-- Prop. app-antisymmetric-single-entropy-asymptotics, eq. (65), at the level of spectra:
    the minimum of `S_p(𝓔_{k,r}(ρ))` over `ρ ∈ 𝒦_{k,t}` is
    `log C(k,r) - 2p(1-t)/(t r k²) + O(k^{-5/2})`. -/
theorem single_output {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      (∀ q ∈ Lam k t,
        Real.log (Nat.choose k r) - 2 * p * (1 - t) / (t * r * k ^ 2) - C / (k ^ 2 * Real.sqrt k)
          ≤ renyi p (subsets k r) (fun _ => 1) (shuffle k r q)) ∧
      (∃ q ∈ Lam k t,
        renyi p (subsets k r) (fun _ => 1) (shuffle k r q)
          ≤ Real.log (Nat.choose k r) - 2 * p * (1 - t) / (t * r * k ^ 2)
            + C / (k ^ 2 * Real.sqrt k)) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨η, Cu, hη, hη', hCu, hunif⟩ := uniform_expansion hp
  obtain ⟨CL, kL, hCL, hloc⟩ := localization ht0 ht1
  obtain ⟨CT, kT, hCT, htwo⟩ := two_spike ht0 ht1
  set γ := (1 - t) / t with hγ
  have hγ0 : 0 < γ := div_pos (by linarith) ht0
  set R : ℝ := ((r' + 1 : ℕ) : ℝ) with hR
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast (by omega : 1 ≤ r' + 1)
  have hR0 : (0 : ℝ) < R := by linarith
  set C : ℝ := p * CL + Cu * (2 * CL + 4 * γ) * (4 * γ + CL) + p * (CT + 8 * R * γ) with hC
  refine ⟨C, max (max kL kT) (max (4 * R + 4) ((CL / η) ^ 2 + 1)), fun k hk => ?_⟩
  have hkL : kL ≤ (k : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hkT : kT ≤ (k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkR : 4 * R + 4 ≤ (k : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkη : (CL / η) ^ 2 + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkr : r' + 2 ≤ k := by
    have : ((r' + 2 : ℕ) : ℝ) ≤ k := by push_cast; rw [hR] at hkR; push_cast at hkR; linarith
    exact_mod_cast this
  set s := Real.sqrt k with hs_def
  have hs2 : s ^ 2 = k := Real.sq_sqrt hkpos.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hkpos
  have hs1 : 1 ≤ s := by nlinarith
  have hsk : s ≤ (k : ℝ) := by nlinarith
  set e := CL / s with he
  have heη : e ≤ η := by
    rw [he, div_le_iff₀ hs0]
    have h1 : CL / η < s := by
      have h2 : (CL / η) ^ 2 < s ^ 2 := by rw [hs2]; linarith
      exact lt_of_pow_lt_pow_left 2 hs0.le h2
    rw [div_lt_iff₀ hη] at h1
    linarith
  have he0 : 0 ≤ e := by positivity
  set D : ℝ := (Nat.choose k (r' + 1) : ℝ) with hD
  have hD0 : 0 < D := by rw [hD]; exact_mod_cast Nat.choose_pos (by omega)
  -- the uniform expansion applied to a point `q` of `Λ_{k,t}`
  have hgen : ∀ q, (∑ i, q i = 1) → (∀ i, |(k : ℝ) * q i - 1| ≤ e) →
      |renyi p (subsets k (r' + 1)) (fun _ => 1) (shuffle k (r' + 1) q) - Real.log D
          + p / 2 * (((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * ∑ i, ((k : ℝ) * q i - 1) ^ 2)|
        ≤ Cu * (e + ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * ∑ i, ((k : ℝ) * q i - 1) ^ 2)
            * (((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * ∑ i, ((k : ℝ) * q i - 1) ^ 2) := by
    intro q hq1 hqe
    set ε : Fin k → ℝ := fun i => (k : ℝ) * q i - 1 with hε
    have hεsum : ∑ i, ε i = 0 := by
      rw [hε]
      simp only
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hq1, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    set δ : Finset (Fin k) → ℝ := fun I => (∑ i ∈ I, ε i) / R with hδ
    have hrep : ∀ I ∈ subsets k (r' + 1), shuffle k (r' + 1) q I = (1 + δ I) / D := by
      intro I hI
      have hIc : I.card = r' + 1 := (Finset.mem_powersetCard.mp hI).2
      rw [shuffle_repr (by omega) (by omega) q I hIc]
    rw [renyi_congr p _ _ _ _ hrep]
    have hd : ∀ I ∈ subsets k (r' + 1), (0 : ℝ) ≤ (fun _ => (1 : ℝ)) I := fun _ _ => zero_le_one
    have hdM : ∑ I ∈ subsets k (r' + 1), (fun _ => (1 : ℝ)) I = D := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_subsets, hD]
    have hdy : ∑ I ∈ subsets k (r' + 1), (fun _ => (1 : ℝ)) I * δ I = 0 := by
      simp only [one_mul, hδ]
      rw [← Finset.sum_div, sum_over_subsets r' ε, hεsum, mul_zero, zero_div]
    have hye : ∀ I ∈ subsets k (r' + 1), |δ I| ≤ e := by
      intro I hI
      have hIc : I.card = r' + 1 := (Finset.mem_powersetCard.mp hI).2
      rw [hδ]
      simp only
      rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
      calc |∑ i ∈ I, ε i| ≤ ∑ i ∈ I, |ε i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ I, e := Finset.sum_le_sum (fun i _ => hqe i)
        _ = e * R := by
            rw [Finset.sum_const, hIc, nsmul_eq_mul, hR]; ring
    have hU := hunif (subsets k (r' + 1)) (fun _ => 1) δ D e hD0 hd hdM hdy hye heη
    have hQ : (∑ I ∈ subsets k (r' + 1), (fun _ => (1 : ℝ)) I * δ I ^ 2) / D
        = ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * ∑ i, ε i ^ 2 := by
      simp only [one_mul, hδ, div_pow]
      rw [← Finset.sum_div, quadratic_form r' ε hεsum, hD]
      rw [show ((k - 2).choose r' : ℝ) * (∑ i, ε i ^ 2) / R ^ 2 / (Nat.choose k (r' + 1) : ℝ)
          = ((k - 2).choose r' : ℝ) / (R ^ 2 * (Nat.choose k (r' + 1) : ℝ)) * ∑ i, ε i ^ 2 by
            field_simp]
      rw [hR, quad_coeff hkr]
    rw [hQ] at hU
    exact hU
  -- bounds on the coefficient `(k - R)/(R k (k-1))`
  have hcoef_hi : ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) ≤ 1 / (R * k) := by
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith [mul_pos hR0 hkpos]
  have hcoef_lo : 1 / (R * k) - 2 / k ^ 2 ≤ ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) := by
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have e1 : ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) ≥ ((k : ℝ) - R) / (R * k * k) := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      have : R * k * ((k : ℝ) - 1) ≤ R * k * k :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      exact this
    have e2 : ((k : ℝ) - R) / (R * k * k) = 1 / (R * k) - 1 / k ^ 2 := by
      field_simp <;> ring
    have e3 : (0 : ℝ) ≤ 1 / k ^ 2 := by positivity
    linarith
  have hcoef0 : 0 ≤ ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) := by
    apply div_nonneg (by linarith) (by nlinarith)
  -- the leading term
  have hlead : 2 * p * (1 - t) / (t * R * k ^ 2) = p / 2 * (4 * γ / (R * k ^ 2)) := by
    have := hR0.ne'; have := ht0.ne'; have := hkpos.ne'
    rw [hγ]; field_simp <;> ring
  rw [hlead]
  have hsk2 : (k : ℝ) ^ 2 * s = (k : ℝ) * (k * s) := by ring
  refine ⟨fun q hq => ?_, ?_⟩
  · -- lower bound
    obtain ⟨hq1, _, hqe, hq2⟩ := hloc k hkL q hq
    set S2 := ∑ i, ((k : ℝ) * q i - 1) ^ 2 with hS2
    set Q := ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * S2 with hQdef
    have hU := hgen q hq1 hqe
    have hS0' : 0 ≤ S2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hQ0 : 0 ≤ Q := mul_nonneg hcoef0 hS0'
    have hQhi : Q ≤ (4 * γ / k + CL / (k * s)) / (R * k) := by
      calc Q ≤ 1 / (R * k) * S2 := mul_le_mul_of_nonneg_right hcoef_hi hS0'
        _ ≤ 1 / (R * k) * (4 * γ / k + CL / (k * s)) :=
            mul_le_mul_of_nonneg_left hq2 (by positivity)
        _ = (4 * γ / k + CL / (k * s)) / (R * k) := by ring
    have hQhi2 : Q ≤ 4 * γ / (R * k ^ 2) + CL / (k ^ 2 * s) := by
      have e1 : (4 * γ / k + CL / (k * s)) / (R * k) = 4 * γ / (R * k ^ 2) + CL / (R * (k ^ 2 * s)) := by
        field_simp <;> ring
      have e2 : CL / (R * (k ^ 2 * s)) ≤ CL / (k ^ 2 * s) := by
        apply div_le_div_of_nonneg_left hCL (by positivity)
        nlinarith [mul_pos (pow_pos hkpos 2) hs0]
      linarith
    have hQhi3 : Q ≤ (4 * γ + CL) / s := by
      have h1 : 4 * γ / (R * k ^ 2) ≤ 4 * γ / s := by
        apply div_le_div_of_nonneg_left (by positivity) hs0
        nlinarith [mul_le_mul_of_nonneg_left hR1 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)]
      have h2 : CL / (k ^ 2 * s) ≤ CL / s := by
        apply div_le_div_of_nonneg_left hCL hs0
        nlinarith
      have e1 : 4 * γ / s + CL / s = (4 * γ + CL) / s := by ring
      linarith
    have hQhi4 : Q ≤ (4 * γ + CL) / k ^ 2 := by
      have h1 : 4 * γ / (R * k ^ 2) ≤ 4 * γ / k ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hR1 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)]
      have h2 : CL / (k ^ 2 * s) ≤ CL / k ^ 2 := by
        apply div_le_div_of_nonneg_left hCL (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)]
      have e1 : 4 * γ / k ^ 2 + CL / k ^ 2 = (4 * γ + CL) / k ^ 2 := by ring
      linarith
    have herr : Cu * (e + Q) * Q ≤ Cu * (2 * CL + 4 * γ) * (4 * γ + CL) / (k ^ 2 * s) := by
      have h1 : e + Q ≤ (2 * CL + 4 * γ) / s := by
        rw [he]
        have e1 : CL / s + (4 * γ + CL) / s = (2 * CL + 4 * γ) / s := by ring
        linarith
      calc Cu * (e + Q) * Q ≤ Cu * ((2 * CL + 4 * γ) / s) * ((4 * γ + CL) / k ^ 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hCu) hQhi4 hQ0 (by positivity)
        _ = Cu * (2 * CL + 4 * γ) * (4 * γ + CL) / (k ^ 2 * s) := by field_simp <;> ring
    have hU' := (abs_le.mp hU).1
    have hlin : p / 2 * Q ≤ p / 2 * (4 * γ / (R * k ^ 2)) + p * CL / (k ^ 2 * s) := by
      have := mul_le_mul_of_nonneg_left hQhi2 (by positivity : (0 : ℝ) ≤ p / 2)
      have e1 : p / 2 * (CL / (k ^ 2 * s)) ≤ p * CL / (k ^ 2 * s) := by
        rw [mul_div_assoc']
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_nonneg hp.le hCL]
      linarith
    have hCbig : p * CL / (k ^ 2 * s) + Cu * (2 * CL + 4 * γ) * (4 * γ + CL) / (k ^ 2 * s)
        ≤ C / (k ^ 2 * s) := by
      rw [div_add_div_same]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [hC]
      have : 0 ≤ p * (CT + 8 * R * γ) := by positivity
      linarith
    linarith [hU', herr, hlin, hCbig]
  · -- upper bound, at the two-spike point
    obtain ⟨q, hq, hq2lo⟩ := htwo k hkT
    obtain ⟨hq1, _, hqe, hq2⟩ := hloc k hkL q hq
    refine ⟨q, hq, ?_⟩
    set S2 := ∑ i, ((k : ℝ) * q i - 1) ^ 2 with hS2
    set Q := ((k : ℝ) - R) / (R * k * ((k : ℝ) - 1)) * S2 with hQdef
    have hU := hgen q hq1 hqe
    have hS0' : 0 ≤ S2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hQ0 : 0 ≤ Q := mul_nonneg hcoef0 hS0'
    have hQhi : Q ≤ (4 * γ + CL) / k ^ 2 := by
      calc Q ≤ 1 / (R * k) * S2 := mul_le_mul_of_nonneg_right hcoef_hi hS0'
        _ ≤ 1 / (R * k) * (4 * γ / k + CL / (k * s)) :=
            mul_le_mul_of_nonneg_left hq2 (by positivity)
        _ ≤ (4 * γ + CL) / k ^ 2 := by
            rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
            have h1 : CL / (k * s) ≤ CL / k := by
              apply div_le_div_of_nonneg_left hCL hkpos
              nlinarith
            have h2 : (4 * γ / k + CL / (k * s)) * k ≤ 4 * γ + CL := by
              have e1 : 4 * γ / k * k = 4 * γ := by field_simp
              have e2 : CL / k * k = CL := by field_simp
              nlinarith [mul_le_mul_of_nonneg_right h1 hkpos.le]
            nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (k : ℝ)),
              mul_pos hR0 hkpos]
    have hQlo : 4 * γ / (R * k ^ 2) - (CT + 8 * R * γ) / k ^ 3 ≤ Q := by
      have hpos : 0 ≤ 1 / (R * k) - 2 / k ^ 2 := by
        have e : 1 / (R * k) - 2 / k ^ 2 = ((k : ℝ) - 2 * R) / (R * k ^ 2) := by
          have := hR0.ne'; have := hkpos.ne'
          field_simp <;> ring
        rw [e]
        exact div_nonneg (by linarith) (by positivity)
      have h1 : (1 / (R * k) - 2 / k ^ 2) * (4 * γ / k - CT / k ^ 2) ≤ Q :=
        calc (1 / (R * k) - 2 / k ^ 2) * (4 * γ / k - CT / k ^ 2)
            ≤ (1 / (R * k) - 2 / k ^ 2) * S2 := mul_le_mul_of_nonneg_left hq2lo hpos
          _ ≤ Q := mul_le_mul_of_nonneg_right hcoef_lo hS0'
      have e1 : (1 / (R * k) - 2 / k ^ 2) * (4 * γ / k - CT / k ^ 2)
          = 4 * γ / (R * k ^ 2) - (CT / R + 8 * γ) / k ^ 3 + 2 * CT / k ^ 4 := by
        field_simp <;> ring
      have h2 : (CT / R + 8 * γ) / k ^ 3 ≤ (CT + 8 * R * γ) / k ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : CT / R ≤ CT := div_le_self hCT hR1
        nlinarith [hγ0]
      have h3 : 0 ≤ 2 * CT / k ^ 4 := by positivity
      linarith
    have herr : Cu * (e + Q) * Q ≤ Cu * (2 * CL + 4 * γ) * (4 * γ + CL) / (k ^ 2 * s) := by
      have h1 : e + Q ≤ (2 * CL + 4 * γ) / s := by
        have h2 : Q ≤ (4 * γ + CL) / s := by
          refine le_trans hQhi ?_
          apply div_le_div_of_nonneg_left (by positivity) hs0
          nlinarith
        rw [he]
        have e1 : CL / s + (4 * γ + CL) / s = (2 * CL + 4 * γ) / s := by ring
        linarith
      calc Cu * (e + Q) * Q ≤ Cu * ((2 * CL + 4 * γ) / s) * ((4 * γ + CL) / k ^ 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hCu) hQhi hQ0 (by positivity)
        _ = Cu * (2 * CL + 4 * γ) * (4 * γ + CL) / (k ^ 2 * s) := by field_simp <;> ring
    have hU' := (abs_le.mp hU).2
    have hlin : p / 2 * (4 * γ / (R * k ^ 2)) - p * (CT + 8 * R * γ) / (k ^ 2 * s) ≤ p / 2 * Q := by
      have h1 := mul_le_mul_of_nonneg_left hQlo (by positivity : (0 : ℝ) ≤ p / 2)
      have h2 : p / 2 * ((CT + 8 * R * γ) / k ^ 3) ≤ p * (CT + 8 * R * γ) / (k ^ 2 * s) := by
        have hX : 0 ≤ CT + 8 * R * γ := by positivity
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        have hk3 : (k : ℝ) ^ 2 * s ≤ (k : ℝ) ^ 3 := by
          have := mul_le_mul_of_nonneg_left hsk (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)
          nlinarith [this]
        have hY : 0 ≤ p * (CT + 8 * R * γ) := mul_nonneg hp.le hX
        nlinarith [mul_le_mul_of_nonneg_left hk3 hY, mul_nonneg hY (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2 * s)]
      linarith
    have hCbig : p * (CT + 8 * R * γ) / (k ^ 2 * s) + Cu * (2 * CL + 4 * γ) * (4 * γ + CL) / (k ^ 2 * s)
        ≤ C / (k ^ 2 * s) := by
      rw [div_add_div_same]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [hC]
      have : 0 ≤ p * CL := by positivity
      linarith
    linarith [hU', herr, hlin, hCbig]

/-- Prop. app-single-entropy-asymptotics, eq. (26), at the level of spectra:
    `min_{σ ∈ 𝒦_{k,t}} S_p(σ) = log k - 2p(1-t)/(t k²) + O(k^{-5/2})`. -/
theorem single_output_r1 {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      (∀ q ∈ Lam k t,
        Real.log k - 2 * p * (1 - t) / (t * k ^ 2) - C / (k ^ 2 * Real.sqrt k)
          ≤ renyi p Finset.univ (fun _ => 1) q) ∧
      (∃ q ∈ Lam k t,
        renyi p Finset.univ (fun _ => 1) q
          ≤ Real.log k - 2 * p * (1 - t) / (t * k ^ 2) + C / (k ^ 2 * Real.sqrt k)) := by
  obtain ⟨C, k₀, h⟩ := single_output ht0 ht1 hp 1 le_rfl
  refine ⟨C, k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := h k hk
  simp only [Nat.choose_one_right, Nat.cast_one, mul_one, renyi_r1] at h1 h2
  exact ⟨h1, h2⟩

/-! ## 11. Propositions app-bell-entropy-asymptotics (44) and
    app-antisymmetric-bell-entropy-asymptotics (68) -/

/-- `0 ≤ r_{k,t} ≤ 2γ/k²` and `|k² r_{k,t} - γ| ≤ 6γ/k²`, with `γ = (1-t)/t`. -/
lemma rkt_bounds {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {k : ℕ} (hk : 2 ≤ (k : ℝ))
    (hkt : 1 ≤ (k : ℝ) ^ 2 * t) :
    0 ≤ rkt k t ∧ rkt k t ≤ 2 * ((1 - t) / t) / (k : ℝ) ^ 2 ∧
      |(k : ℝ) ^ 2 * rkt k t - (1 - t) / t| ≤ 6 * ((1 - t) / t) / (k : ℝ) ^ 2 := by
  have h1t : 0 < 1 - t := by linarith
  have ht0' := ht0.ne'
  have hK0 : (0 : ℝ) < k := by linarith
  have hK0' := hK0.ne'
  have hK2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hden_lo : (k : ℝ) ^ 4 * t / 2 ≤ (k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1 := by
    have : 2 * (k : ℝ) ^ 2 * t ≤ (k : ℝ) ^ 4 * t / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hK2 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2 * t)]
    linarith
  have hden0 : 0 < (k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1 :=
    lt_of_lt_of_le (by positivity) hden_lo
  have hden0' := hden0.ne'
  unfold rkt
  refine ⟨div_nonneg (mul_nonneg (sq_nonneg _) h1t.le) hden0.le, ?_, ?_⟩
  · rw [div_le_div_iff₀ hden0 (by positivity)]
    calc (k : ℝ) ^ 2 * (1 - t) * (k : ℝ) ^ 2
        = 2 * ((1 - t) / t) * ((k : ℝ) ^ 4 * t / 2) := by field_simp <;> ring
      _ ≤ 2 * ((1 - t) / t) * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1) :=
          mul_le_mul_of_nonneg_left hden_lo (by positivity)
  · have e : (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (1 - t) / ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1))
          - (1 - t) / t
        = (1 - t) * (2 * (k : ℝ) ^ 2 * t - 1)
            / (t * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1)) := by
      field_simp <;> ring
    have hnum : 0 ≤ (1 - t) * (2 * (k : ℝ) ^ 2 * t - 1) := mul_nonneg h1t.le (by linarith)
    rw [e, abs_of_nonneg (div_nonneg hnum (mul_pos ht0 hden0).le),
      div_le_div_iff₀ (mul_pos ht0 hden0) (by positivity)]
    have h3 : (1 - t) * (2 * (k : ℝ) ^ 2 * t - 1) * (k : ℝ) ^ 2
        ≤ (1 - t) * (2 * (k : ℝ) ^ 2 * t) * (k : ℝ) ^ 2 := by
      nlinarith [mul_nonneg h1t.le (sq_nonneg (k : ℝ))]
    have h4 : (1 - t) * (2 * (k : ℝ) ^ 2 * t) * (k : ℝ) ^ 2
        ≤ 6 * ((1 - t) / t) * (t * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1)) := by
      have e2 : 6 * ((1 - t) / t) * (t * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1))
          = 6 * (1 - t) * ((k : ℝ) ^ 4 * t - 2 * (k : ℝ) ^ 2 * t + 1) := by
        field_simp <;> ring
      rw [e2]
      have := mul_le_mul_of_nonneg_left hden_lo (by positivity : (0 : ℝ) ≤ 6 * (1 - t))
      nlinarith [this, mul_nonneg (mul_nonneg h1t.le (pow_nonneg hK0.le 4)) ht0.le]
    linarith

/-- The last step shared by both Bell-output proofs:
    `F_p(X) - c_p Y = (F_p(X) - c_p X) + c_p (X - Y)`. -/
lemma final_step {p C₂ : ℝ} (hF : ∀ x, |x| ≤ 1 / 2 → |Fp p x - cp p * x| ≤ C₂ * x ^ 2)
    {X Y e : ℝ} (hXY : |X - Y| ≤ e) (hX : |X| ≤ 1 / 2) :
    |Fp p X - cp p * Y| ≤ C₂ * X ^ 2 + |cp p| * e := by
  have h1 := hF X hX
  calc |Fp p X - cp p * Y| = |(Fp p X - cp p * X) + cp p * (X - Y)| := by congr 1; ring
    _ ≤ |Fp p X - cp p * X| + |cp p * (X - Y)| := abs_add _ _
    _ ≤ C₂ * X ^ 2 + |cp p| * e := by
        rw [abs_mul]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left hXY (abs_nonneg _))

/-- `|ψ_p(y)| ≤ (|κ_p| + C) y²` near `0`. -/
lemma psi_quad {p η C : ℝ} (hη' : η ≤ 1 / 2) (hC : 0 ≤ C)
    (hloc : ∀ y, |y| ≤ η → |psi p y - kappa p * y ^ 2| ≤ C * |y| ^ 3) :
    ∀ y, |y| ≤ η → |psi p y| ≤ (|kappa p| + C) * y ^ 2 := by
  intro y hy
  have h1 := hloc y hy
  have hy0 := abs_nonneg y
  have h2 : |y| ^ 3 ≤ y ^ 2 := by
    rw [← sq_abs y]
    nlinarith [mul_nonneg (pow_nonneg hy0 2) (by linarith : (0 : ℝ) ≤ 1 - |y|)]
  have h3 : |kappa p * y ^ 2| = |kappa p| * y ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
  have h4 : |psi p y| ≤ |psi p y - kappa p * y ^ 2| + |kappa p * y ^ 2| := by
    calc |psi p y| = |(psi p y - kappa p * y ^ 2) + kappa p * y ^ 2| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add _ _
  nlinarith [mul_le_mul_of_nonneg_left h2 hC]

/-- `D² w_m = k (r - m)(k - r - m + 1)/r²`, from `kN = rD`. -/
lemma D2wm {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (m : ℕ) :
    (Nat.choose k r : ℝ) ^ 2 * wm k r m
      = (k : ℝ) * (((r : ℝ) - m) * ((k : ℝ) - r - m + 1)) / (r : ℝ) ^ 2 := by
  have hk : 1 ≤ k := le_trans hr hrk
  have h1 := choose_mul_left hr hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hD : (0 : ℝ) < (Nat.choose k r : ℝ) := by exact_mod_cast Nat.choose_pos hrk
  have hk0' := hk0.ne'
  have hr0' := hr0.ne'
  have hD' := hD.ne'
  have hNeq : (Nat.choose (k - 1) (r - 1) : ℝ) = r * (Nat.choose k r : ℝ) / k := by
    rw [eq_div_iff hk0']
    linarith [h1]
  unfold wm
  rw [hNeq]
  field_simp <;> ring

/-- `|d_m| ≤ 2 ((2r/k)² D)²` for `m ≤ r - 2`. -/
lemma dm_small {k r' m : ℕ} (hk : 2 * (r' + 1) ≤ k) (hm : m < r') :
    |dm k m| ≤ 2 * ((2 * ((r' + 1 : ℕ) : ℝ) / k) ^ 2 * (Nat.choose k (r' + 1) : ℝ)) ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hq0 : (0 : ℝ) ≤ 2 * ((r' + 1 : ℕ) : ℝ) / k := by positivity
  have hq1 : 2 * ((r' + 1 : ℕ) : ℝ) / k ≤ 1 := by
    rw [div_le_one hk0]; exact_mod_cast hk
  have hD0 : (0 : ℝ) ≤ Nat.choose k (r' + 1) := Nat.cast_nonneg _
  have hb : ∀ j, j ≤ m →
      (Nat.choose k j : ℝ) ≤ (2 * ((r' + 1 : ℕ) : ℝ) / k) ^ 2 * Nat.choose k (r' + 1) := by
    intro j hj
    have h := choose_le_pow (k := k) (r := r' + 1) hk ((r' + 1) - j) (by omega)
    have e : r' + 1 - (r' + 1 - j) = j := by omega
    rw [e] at h
    calc (Nat.choose k j : ℝ)
        ≤ (2 * ((r' + 1 : ℕ) : ℝ) / k) ^ (r' + 1 - j) * Nat.choose k (r' + 1) := h
      _ ≤ (2 * ((r' + 1 : ℕ) : ℝ) / k) ^ 2 * Nat.choose k (r' + 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 (by omega)) hD0
  have h1 := hb m le_rfl
  have hc0 : (0 : ℝ) ≤ Nat.choose k m := Nat.cast_nonneg _
  have h3 := pow_le_pow_left hc0 h1 2
  have hB0 : (0 : ℝ) ≤ ((2 * ((r' + 1 : ℕ) : ℝ) / k) ^ 2 * Nat.choose k (r' + 1)) ^ 2 :=
    sq_nonneg _
  unfold dm
  split_ifs with h0
  · rw [sub_zero, abs_of_nonneg (by positivity)]
    linarith
  · have h2 := hb (m - 1) (by omega)
    have hc1 : (0 : ℝ) ≤ Nat.choose k (m - 1) := Nat.cast_nonneg _
    have h4 := pow_le_pow_left hc1 h2 2
    rw [abs_le]
    constructor <;> nlinarith [h3, h4, sq_nonneg (Nat.choose k m : ℝ),
      sq_nonneg (Nat.choose k (m - 1) : ℝ)]

/-- Prop. app-bell-entropy-asymptotics, eq. (44):
    `S_p(λ^Bell_{k,t}) = 2 log k - A_p(t)/k² + O(k^{-4})`, where `λ^Bell_{k,t}` consists of
    `α_{k,t}` (multiplicity 1) and `β_{k,t}` (multiplicity `k² - 1`). -/
theorem bell_output_r1 {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      |renyi p (Finset.univ : Finset (Fin 2)) ![1, (k : ℝ) ^ 2 - 1] ![alphaB k t, betaB k t]
        - (2 * Real.log k - Ap p t / k ^ 2)| ≤ C / k ^ 4 := by
  obtain ⟨η₁, C₁, hη₁, hη₁', hC₁, hloc⟩ := psi_local hp
  obtain ⟨C₂, hC₂, hF⟩ := Fp_local p
  have hγ0 : 0 < (1 - t) / t := div_pos (by linarith) ht0
  obtain ⟨L, ηL, hηL, hL, hlip⟩ := psi_lip hp (show -1 < (1 - t) / t by linarith)
  set γ := (1 - t) / t with hγ
  set P0 := |psi p γ| with hP0
  set E := 8 * γ * L + (|kappa p| + C₁) * (2 * γ) ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨C₂ * (P0 + E) ^ 2 + |cp p| * E,
    max (max 2 (1 / t)) (max (8 * γ / ηL + 1) (max (2 * γ / η₁ + 1) (2 * (P0 + E) + 1))),
    fun k hk => ?_⟩
  have hk2 : (2 : ℝ) ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hkt : 1 / t ≤ (k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkL : 8 * γ / ηL + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkη : 2 * γ / η₁ + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hk
  have hkP : 2 * (P0 + E) + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk2t : 1 ≤ (k : ℝ) ^ 2 * t := by
    rw [div_le_iff₀ ht0] at hkt; nlinarith
  obtain ⟨hρ0, hρ1, hρ2⟩ := rkt_bounds ht0 ht1 hk2 hk2t
  rw [← hγ] at hρ1 hρ2
  set ρ := rkt k t with hρ
  have hρη : ρ ≤ η₁ := by
    have h1 : 2 * γ / (k : ℝ) ^ 2 ≤ 2 * γ / (k : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hkpos hkk
    have h2 : 2 * γ / (k : ℝ) ≤ η₁ := by
      rw [div_le_iff₀ hkpos]
      have h3 : 2 * γ / η₁ ≤ k := by linarith
      rw [div_le_iff₀ hη₁] at h3
      linarith
    linarith
  set y0 := ρ * ((k : ℝ) ^ 2 - 1) with hy0
  have hyγ : |y0 - γ| ≤ 8 * γ / (k : ℝ) ^ 2 := by
    have e : y0 - γ = ((k : ℝ) ^ 2 * ρ - γ) - ρ := by rw [hy0]; ring
    rw [e]
    calc |((k : ℝ) ^ 2 * ρ - γ) - ρ| ≤ |(k : ℝ) ^ 2 * ρ - γ| + |ρ| := abs_sub _ _
      _ ≤ 6 * γ / (k : ℝ) ^ 2 + 2 * γ / (k : ℝ) ^ 2 := by
          rw [abs_of_nonneg hρ0]; linarith [hρ2, hρ1]
      _ = 8 * γ / (k : ℝ) ^ 2 := by ring
  have hyL : |y0 - γ| ≤ ηL := by
    refine le_trans hyγ ?_
    have h1 : 8 * γ / (k : ℝ) ^ 2 ≤ 8 * γ / (k : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hkpos hkk
    have h2 : 8 * γ / (k : ℝ) ≤ ηL := by
      rw [div_le_iff₀ hkpos]
      have h3 : 8 * γ / ηL ≤ k := by linarith
      rw [div_le_iff₀ hηL] at h3
      linarith
    linarith
  have hψ1 := hlip y0 hyL
  have hψ2 := psi_quad hη₁' hC₁ hloc (-ρ) (by rw [abs_neg, abs_of_nonneg hρ0]; exact hρη)
  -- Step 1: the spectrum is `(1 + y_j)/k²` with `y = (y0, -ρ)`
  have hspec : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      (![alphaB k t, betaB k t] : Fin 2 → ℝ) j
        = (fun j => (1 + (![y0, -ρ] : Fin 2 → ℝ) j) / (k : ℝ) ^ 2) j := by
    intro j _
    fin_cases j <;> simp [alphaB, betaB, ← hρ, hy0] <;> field_simp <;> ring
  rw [renyi_congr p _ _ _ _ hspec]
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      0 ≤ (![1, (k : ℝ) ^ 2 - 1] : Fin 2 → ℝ) j := by
    intro j _
    fin_cases j <;> simp <;> nlinarith
  have hdM : ∑ j : Fin 2, (![1, (k : ℝ) ^ 2 - 1] : Fin 2 → ℝ) j = (k : ℝ) ^ 2 := by
    rw [Fin.sum_univ_two]; simp
  have hy : ∀ j ∈ (Finset.univ : Finset (Fin 2)), -1 < (![y0, -ρ] : Fin 2 → ℝ) j := by
    intro j _
    fin_cases j <;> simp [hy0] <;>
      nlinarith [mul_nonneg hρ0 (show (0 : ℝ) ≤ (k : ℝ) ^ 2 - 1 by nlinarith), hρη, hη₁']
  have hdy : ∑ j : Fin 2, (![1, (k : ℝ) ^ 2 - 1] : Fin 2 → ℝ) j * (![y0, -ρ] : Fin 2 → ℝ) j
      = 0 := by
    rw [Fin.sum_univ_two]; simp [hy0] <;> ring
  -- Step 2: exact expansion
  rw [exact_expansion p Finset.univ _ _ ((k : ℝ) ^ 2) (by positivity) hd hdM hy hdy]
  set X := (∑ j : Fin 2, (![1, (k : ℝ) ^ 2 - 1] : Fin 2 → ℝ) j
      * psi p ((![y0, -ρ] : Fin 2 → ℝ) j)) / (k : ℝ) ^ 2 with hX
  have hXval : X = (psi p y0 + ((k : ℝ) ^ 2 - 1) * psi p (-ρ)) / (k : ℝ) ^ 2 := by
    rw [hX, Fin.sum_univ_two]; simp
  -- Step 3: estimates
  have hXY : |X - psi p γ / (k : ℝ) ^ 2| ≤ E / (k : ℝ) ^ 4 := by
    rw [hXval]
    have e : (psi p y0 + ((k : ℝ) ^ 2 - 1) * psi p (-ρ)) / (k : ℝ) ^ 2 - psi p γ / (k : ℝ) ^ 2
        = (psi p y0 - psi p γ) / (k : ℝ) ^ 2
          + ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 * psi p (-ρ) := by ring
    rw [e]
    have h1 : |(psi p y0 - psi p γ) / (k : ℝ) ^ 2| ≤ 8 * γ * L / (k : ℝ) ^ 4 := by
      rw [abs_div, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
      calc |psi p y0 - psi p γ| ≤ L * |y0 - γ| := hψ1
        _ ≤ L * (8 * γ / (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hyγ hL
        _ = 8 * γ * L / (k : ℝ) ^ 4 * (k : ℝ) ^ 2 := by field_simp <;> ring
    have h2 : |((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 * psi p (-ρ)|
        ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by
      rw [abs_mul]
      have h3 : |((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2| ≤ 1 := by
        rw [abs_le]; constructor
        · have : 0 ≤ ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 :=
            div_nonneg (by nlinarith) (by positivity)
          linarith
        · rw [div_le_one (by positivity)]; linarith
      have h4 : |psi p (-ρ)| ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by
        refine le_trans hψ2 ?_
        rw [neg_sq]
        have h5 : ρ ^ 2 ≤ (2 * γ / (k : ℝ) ^ 2) ^ 2 := pow_le_pow_left hρ0 hρ1 2
        calc (|kappa p| + C₁) * ρ ^ 2 ≤ (|kappa p| + C₁) * (2 * γ / (k : ℝ) ^ 2) ^ 2 :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by field_simp <;> ring
      calc |((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2| * |psi p (-ρ)|
          ≤ 1 * ((|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4) :=
            mul_le_mul h3 h4 (abs_nonneg _) zero_le_one
        _ = (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 := one_mul _
    calc _ ≤ |(psi p y0 - psi p γ) / (k : ℝ) ^ 2|
          + |((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 * psi p (-ρ)| := abs_add _ _
      _ ≤ 8 * γ * L / (k : ℝ) ^ 4 + (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 4 :=
          add_le_add h1 h2
      _ = E / (k : ℝ) ^ 4 := by rw [hE]; ring
  have hXb : |X| ≤ (P0 + E) / (k : ℝ) ^ 2 := by
    have h1 : |X| ≤ |psi p γ / (k : ℝ) ^ 2| + E / (k : ℝ) ^ 4 := by
      have := abs_sub_abs_le_abs_sub X (psi p γ / (k : ℝ) ^ 2)
      linarith
    have h2 : |psi p γ / (k : ℝ) ^ 2| = P0 / (k : ℝ) ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
    have h3 : E / (k : ℝ) ^ 4 ≤ E / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hE0 (by positivity) (by nlinarith)
    have e : P0 / (k : ℝ) ^ 2 + E / (k : ℝ) ^ 2 = (P0 + E) / (k : ℝ) ^ 2 := by ring
    linarith
  have hX12 : |X| ≤ 1 / 2 := by
    refine le_trans hXb ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlog : Real.log ((k : ℝ) ^ 2) = 2 * Real.log k := by
    rw [Real.log_pow]; norm_num
  have hA : cp p * psi p γ = -Ap p t := by
    have h1 := B_identity p 1 γ one_ne_zero
    simp only [one_pow, div_one, one_mul] at h1
    rw [h1, hγ, B_one_eq_A p t ht0]
  have e : Real.log ((k : ℝ) ^ 2) + Fp p X - (2 * Real.log k - Ap p t / (k : ℝ) ^ 2)
      = Fp p X - cp p * (psi p γ / (k : ℝ) ^ 2) := by
    rw [hlog, mul_div_assoc', hA]; ring
  rw [e]
  calc |Fp p X - cp p * (psi p γ / (k : ℝ) ^ 2)|
      ≤ C₂ * X ^ 2 + |cp p| * (E / (k : ℝ) ^ 4) := final_step hF hXY hX12
    _ ≤ C₂ * ((P0 + E) / (k : ℝ) ^ 2) ^ 2 + |cp p| * (E / (k : ℝ) ^ 4) := by
        have h1 : X ^ 2 ≤ ((P0 + E) / (k : ℝ) ^ 2) ^ 2 := by
          rw [← sq_abs X]; exact pow_le_pow_left (abs_nonneg _) hXb 2
        have := mul_le_mul_of_nonneg_left h1 hC₂
        linarith
    _ = (C₂ * (P0 + E) ^ 2 + |cp p| * E) / (k : ℝ) ^ 4 := by
        rw [div_pow]; field_simp <;> ring

/-- Prop. app-antisymmetric-bell-entropy-asymptotics, eq. (68), at the level of spectra:
    `ω_{k,r,t}` has eigenvalues `ν_m` with multiplicities `d_m` (Prop. app-spectrum-W), and
    `S_p(ω_{k,r,t}) = 2 log C(k,r) - B_{p,r}(γ)/k² + O(k^{-3})`. -/
theorem bell_output {t p : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    ∃ C k₀ : ℝ, ∀ k : ℕ, k₀ ≤ (k : ℝ) →
      |renyi p (Finset.range (r + 1)) (dm k) (bellNu k r t)
        - (2 * Real.log (Nat.choose k r) - Bpr p r ((1 - t) / t) / k ^ 2)| ≤ C / k ^ 3 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨η₁, C₁, hη₁, hη₁', hC₁, hloc⟩ := psi_local hp
  obtain ⟨C₂, hC₂, hF⟩ := Fp_local p
  have hγ0 : 0 < (1 - t) / t := div_pos (by linarith) ht0
  set γ := (1 - t) / t with hγ
  set R : ℝ := ((r' + 1 : ℕ) : ℝ) with hR
  have hRr' : R = (r' : ℝ) + 1 := by rw [hR]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ R := by rw [hRr']; have := Nat.cast_nonneg (α := ℝ) r'; linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hg00 : 0 < γ / R ^ 2 := by positivity
  obtain ⟨L, ηL, hηL, hL, hlip⟩ := psi_lip hp (show -1 < γ / R ^ 2 by linarith)
  obtain ⟨Bψ, hBψ⟩ := psi_bdd hp (2 * γ) (by positivity)
  have hBψ0 : 0 ≤ Bψ := le_trans (abs_nonneg _) (hBψ 0 (by norm_num) (by positivity))
  set P0 := |psi p (γ / R ^ 2)| with hP0
  set E : ℝ := 2 * (|kappa p| + C₁) * (2 * γ) ^ 2 + (8 * R ^ 3 + 16 * R ^ 4) * Bψ
      + R ^ 2 * L * (12 * γ * R) + (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨C₂ * (R ^ 2 * P0 + E) ^ 2 + |cp p| * E,
    max (max (4 * R + 4) (1 / t + 3)) (max (12 * γ * R / ηL + 1)
      (max (2 * γ / η₁ + 1) (2 * (R ^ 2 * P0 + E) + 1))), fun k hk => ?_⟩
  have hkR : 4 * R + 4 ≤ (k : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hkt : 1 / t + 3 ≤ (k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkL : 12 * γ * R / ηL + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkη : 2 * γ / η₁ + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hk
  have hkX : 2 * (R ^ 2 * P0 + E) + 1 ≤ (k : ℝ) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hkk3 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by nlinarith
  have hkk4 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 4 := by nlinarith
  have hk2R : 2 * (r' + 1) ≤ k := by
    have h : ((2 * (r' + 1) : ℕ) : ℝ) ≤ k := by
      push_cast; rw [hRr'] at hkR; linarith
    exact_mod_cast h
  have hk2 : (2 : ℝ) ≤ k := by linarith
  have hk2t : 1 ≤ (k : ℝ) ^ 2 * t := by
    have h1 : 1 / t ≤ (k : ℝ) := by linarith
    rw [div_le_iff₀ ht0] at h1; nlinarith
  obtain ⟨hρ0, hρ1, hρ2⟩ := rkt_bounds ht0 ht1 hk2 hk2t
  rw [← hγ] at hρ1 hρ2
  set ρ := rkt k t with hρ
  set D : ℝ := (Nat.choose k (r' + 1) : ℝ) with hD
  have hD0 : 0 < D := by rw [hD]; exact_mod_cast Nat.choose_pos (by omega)
  have hD0' := hD0.ne'
  have hρη : ρ ≤ η₁ := by
    have h1 : 2 * γ / (k : ℝ) ^ 2 ≤ 2 * γ / (k : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hkpos hkk
    have h2 : 2 * γ / (k : ℝ) ≤ η₁ := by
      rw [div_le_iff₀ hkpos]
      have h3 : 2 * γ / η₁ ≤ k := by linarith
      rw [div_le_iff₀ hη₁] at h3
      linarith
    linarith
  have hρ12 : ρ ≤ 1 / 2 := le_trans hρη hη₁'
  have hρk : ρ * (k : ℝ) ^ 2 ≤ 2 * γ := by
    have h1 := (abs_le.mp hρ2).2
    have h2 : 6 * γ / (k : ℝ) ^ 2 ≤ γ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  -- Step 1: the spectrum is `(1 + y_m)/D²`
  set y : ℕ → ℝ := fun m => ρ * (D ^ 2 * wm k (r' + 1) m - 1) with hy
  have hD2wm : ∀ m, D ^ 2 * wm k (r' + 1) m
      = (k : ℝ) * ((R - m) * ((k : ℝ) - R - m + 1)) / R ^ 2 := by
    intro m
    have h := D2wm (k := k) (r := r' + 1) (by omega) (by omega) m
    rw [← hR, ← hD] at h
    exact h
  have hwm0 : ∀ m ∈ Finset.range (r' + 1 + 1), 0 ≤ wm k (r' + 1) m := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hm' : (m : ℝ) ≤ R := by
      rw [hRr']; exact_mod_cast (by omega : m ≤ r' + 1)
    have hnn1 : 0 ≤ R - m := by linarith
    have hnn2 : 0 ≤ (k : ℝ) - R - m + 1 := by linarith
    unfold wm
    rw [← hR]
    exact div_nonneg (mul_nonneg hnn1 hnn2) (by positivity)
  have hνy : ∀ m ∈ Finset.range (r' + 1 + 1), bellNu k (r' + 1) t m = (1 + y m) / D ^ 2 := by
    intro m _
    simp only [bellNu, hy]
    rw [← hρ, ← hD]
    field_simp <;> ring
  have hd : ∀ m ∈ Finset.range (r' + 1 + 1), 0 ≤ dm k m := by
    intro m hm
    rw [Finset.mem_range] at hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [dm]
    · have h1 := choose_le_ratio (k := k) (r := r' + 1) (j := m - 1) (by omega) hk2R
      rw [Nat.sub_add_cancel hpos] at h1
      have h2 : 2 * ((r' + 1 : ℕ) : ℝ) / k ≤ 1 := by
        rw [div_le_one hkpos]; exact_mod_cast hk2R
      have h4 : (0 : ℝ) ≤ Nat.choose k m := Nat.cast_nonneg _
      have h3 : (Nat.choose k (m - 1) : ℝ) ≤ Nat.choose k m := by
        nlinarith [mul_le_mul_of_nonneg_right h2 h4]
      simp only [dm, if_neg (Nat.pos_iff_ne_zero.mp hpos)]
      have h5 : (0 : ℝ) ≤ Nat.choose k (m - 1) := Nat.cast_nonneg _
      nlinarith [h3, h5]
  have hdM : ∑ m ∈ Finset.range (r' + 1 + 1), dm k m = D ^ 2 := mult_sum k (r' + 1)
  have hdy : ∑ m ∈ Finset.range (r' + 1 + 1), dm k m * y m = 0 := by
    simp only [hy]
    have h1 := trace_identity (k := k) (r := r' + 1) (by omega) (by omega)
    have e : ∀ m, dm k m * (ρ * (D ^ 2 * wm k (r' + 1) m - 1))
        = ρ * D ^ 2 * (dm k m * wm k (r' + 1) m) - ρ * dm k m := by
      intro m; ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, h1, hdM]
    ring
  have hy_lo : ∀ m ∈ Finset.range (r' + 1 + 1), -ρ ≤ y m := by
    intro m hm
    simp only [hy]
    have h2 : 0 ≤ D ^ 2 * wm k (r' + 1) m := mul_nonneg (sq_nonneg D) (hwm0 m hm)
    nlinarith [mul_nonneg hρ0 h2]
  have hy1 : ∀ m ∈ Finset.range (r' + 1 + 1), -1 < y m := fun m hm => by
    have := hy_lo m hm; linarith
  have hy_hi : ∀ m ∈ Finset.range (r' + 1 + 1), y m ≤ 2 * γ := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hm' : (m : ℝ) ≤ R := by
      rw [hRr']; exact_mod_cast (by omega : m ≤ r' + 1)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hfac : (k : ℝ) * ((R - m) * ((k : ℝ) - R - m + 1)) / R ^ 2 ≤ (k : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h2 : 0 ≤ (k : ℝ) - R - m + 1 := by linarith
      have h5 : (R - m) * ((k : ℝ) - R - m + 1) ≤ R * k :=
        mul_le_mul (by linarith) (by linarith) h2 hR0.le
      have h6 := mul_le_mul_of_nonneg_left h5 hkpos.le
      have h7 : (k : ℝ) * (R * k) ≤ (k : ℝ) ^ 2 * R ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hR1 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2 * R)]
      linarith
    simp only [hy]
    rw [hD2wm]
    nlinarith [mul_le_mul_of_nonneg_left hfac hρ0]
  have hψbdd : ∀ m ∈ Finset.range (r' + 1 + 1), |psi p (y m)| ≤ Bψ := fun m hm =>
    hBψ (y m) (by linarith [hy_lo m hm]) (hy_hi m hm)
  -- Step 2: exact expansion
  rw [renyi_congr p _ _ _ _ hνy,
    exact_expansion p (Finset.range (r' + 1 + 1)) (dm k) y (D ^ 2) (by positivity) hd hdM hy1 hdy]
  set X := (∑ m ∈ Finset.range (r' + 1 + 1), dm k m * psi p (y m)) / D ^ 2 with hX
  -- Step 3: estimates
  have hsplit : ∑ m ∈ Finset.range (r' + 1 + 1), dm k m * psi p (y m)
      = ∑ m ∈ Finset.range r', dm k m * psi p (y m) + dm k r' * psi p (y r')
        + dm k (r' + 1) * psi p (y (r' + 1)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hyR : y (r' + 1) = -ρ := by
    simp only [hy]
    rw [hD2wm, ← hR]
    simp
  -- the term m = r - 1: `y_{r-1}` is close to `γ/R²`
  have hyr : |y r' - γ / R ^ 2| ≤ 12 * γ * R / k := by
    have hRr : R - (r' : ℝ) = 1 := by rw [hRr']; ring
    have e : y r' - γ / R ^ 2
        = (ρ * (k : ℝ) ^ 2 - γ) / R ^ 2 - ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1) := by
      simp only [hy]
      rw [hD2wm]
      have e1 : (k : ℝ) - R - r' + 1 = (k : ℝ) - 2 * R + 2 := by linarith [hRr]
      rw [e1, hRr]
      have := hR0.ne'
      field_simp <;> ring
    rw [e]
    have h1 : |(ρ * (k : ℝ) ^ 2 - γ) / R ^ 2| ≤ 6 * γ / (k : ℝ) ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity)]
      have h2 : |ρ * (k : ℝ) ^ 2 - γ| ≤ 6 * γ / (k : ℝ) ^ 2 := by
        have := hρ2
        rwa [mul_comm ((k : ℝ) ^ 2) ρ] at this
      calc |ρ * (k : ℝ) ^ 2 - γ| / R ^ 2 ≤ |ρ * (k : ℝ) ^ 2 - γ| :=
            div_le_self (abs_nonneg _) (by nlinarith)
        _ ≤ 6 * γ / (k : ℝ) ^ 2 := h2
    have hfac0 : 0 ≤ (k : ℝ) * (2 * R - 2) / R ^ 2 :=
      div_nonneg (mul_nonneg hkpos.le (by linarith)) (by positivity)
    have h3 : 0 ≤ ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1) := mul_nonneg hρ0 (by linarith)
    have h4 : ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1) ≤ 6 * γ / k := by
      have h5 : (k : ℝ) * (2 * R - 2) / R ^ 2 ≤ 2 * k := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hkpos.le (by nlinarith : (0 : ℝ) ≤ 2 * R ^ 2 - 2 * R + 2)]
      calc ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1) ≤ (2 * γ / (k : ℝ) ^ 2) * (2 * k + 1) :=
            mul_le_mul hρ1 (by linarith) (by linarith) (by positivity)
        _ ≤ 6 * γ / k := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hkpos]
            nlinarith [mul_pos hγ0 hkpos]
    calc |(ρ * (k : ℝ) ^ 2 - γ) / R ^ 2 - ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1)|
        ≤ |(ρ * (k : ℝ) ^ 2 - γ) / R ^ 2| + |ρ * ((k : ℝ) * (2 * R - 2) / R ^ 2 + 1)| :=
          abs_sub _ _
      _ ≤ 6 * γ / (k : ℝ) ^ 2 + 6 * γ / k := by rw [abs_of_nonneg h3]; linarith
      _ ≤ 12 * γ * R / k := by
          have h6 : 6 * γ / (k : ℝ) ^ 2 ≤ 6 * γ / k :=
            div_le_div_of_nonneg_left (by positivity) hkpos hkk
          have h7 : 12 * γ / k ≤ 12 * γ * R / k :=
            div_le_div_of_nonneg_right (by nlinarith) hkpos.le
          have e2 : 6 * γ / k + 6 * γ / k = 12 * γ / k := by ring
          linarith
  have hyL : |y r' - γ / R ^ 2| ≤ ηL := by
    refine le_trans hyr ?_
    rw [div_le_iff₀ hkpos]
    have h3 : 12 * γ * R / ηL ≤ k := by linarith
    rw [div_le_iff₀ hηL] at h3
    linarith
  -- ratio facts for `d_{r-1}/D²`
  have hkr0 : 0 < (k : ℝ) - r' := by
    have := hRr'.symm.le; have := Nat.cast_nonneg (α := ℝ) r'; linarith
  have hkr0' := hkr0.ne'
  have hratio : (Nat.choose k r' : ℝ) = D * R / ((k : ℝ) - r') := by
    have h := choose_succ_ratio (k := k) (j := r') (by omega)
    rw [eq_div_iff hkr0', hD, hRr']
    linarith [h]
  have hT2a : |(R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2| ≤ 8 * R ^ 3 / (k : ℝ) ^ 3 := by
    have hr'R : (r' : ℝ) ≤ R := by rw [hRr']; linarith
    have hr'0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg _
    have hkr : (k : ℝ) / 2 ≤ (k : ℝ) - r' := by linarith
    have e : (R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2
        = R ^ 2 * ((r' : ℝ) * (2 * k - r')) / ((k : ℝ) ^ 2 * ((k : ℝ) - r') ^ 2) := by
      field_simp <;> ring
    have hnum : 0 ≤ R ^ 2 * ((r' : ℝ) * (2 * k - r')) :=
      mul_nonneg (by positivity) (mul_nonneg hr'0 (by linarith))
    rw [e, abs_of_nonneg (div_nonneg hnum (by positivity)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : ((k : ℝ) / 2) ^ 2 ≤ ((k : ℝ) - r') ^ 2 := pow_le_pow_left (by positivity) hkr 2
    have h3 : (r' : ℝ) * (2 * k - r') ≤ R * (2 * k) := by
      nlinarith [mul_le_mul_of_nonneg_right hr'R (by linarith : (0 : ℝ) ≤ 2 * k - r'),
        mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) * k - r' ≤ 2 * k) hR0.le]
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ R ^ 2 * (k : ℝ) ^ 3)
    have h5 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * R ^ 3 * (k : ℝ) ^ 2)
    nlinarith [h4, h5]
  have hT2b : r' ≠ 0 → ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 ≤ 16 * R ^ 4 / (k : ℝ) ^ 4 := by
    intro hr0
    have h := choose_le_pow (k := k) (r := r' + 1) hk2R 2 (by omega)
    have e : r' + 1 - 2 = r' - 1 := by omega
    rw [e, ← hD, ← hR] at h
    have h1 : (Nat.choose k (r' - 1) : ℝ) / D ≤ (2 * R / k) ^ 2 := by
      rw [div_le_iff₀ hD0]; exact h
    have h0 : (0 : ℝ) ≤ (Nat.choose k (r' - 1) : ℝ) / D := by positivity
    calc ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 ≤ ((2 * R / k) ^ 2) ^ 2 := pow_le_pow_left h0 h1 2
      _ = 16 * R ^ 4 / (k : ℝ) ^ 4 := by field_simp <;> ring
  have hT2d : |dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2| ≤ (8 * R ^ 3 + 16 * R ^ 4) / (k : ℝ) ^ 3 := by
    have hdmr : dm k r' / D ^ 2 = (R / ((k : ℝ) - r')) ^ 2
        - (if r' = 0 then 0 else ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2) := by
      unfold dm
      rw [hratio]
      split_ifs <;> field_simp <;> ring
    rw [hdmr]
    have h8 : 8 * R ^ 3 / (k : ℝ) ^ 3 ≤ (8 * R ^ 3 + 16 * R ^ 4) / (k : ℝ) ^ 3 :=
      div_le_div_of_nonneg_right (by nlinarith [pow_nonneg hR0.le 4]) (by positivity)
    split_ifs with hr0
    · rw [sub_zero]; exact le_trans hT2a h8
    · have h1 := hT2b hr0
      have h2 : 16 * R ^ 4 / (k : ℝ) ^ 4 ≤ 16 * R ^ 4 / (k : ℝ) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hkk4
      have h3 : 0 ≤ ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 := sq_nonneg _
      have e : (R / ((k : ℝ) - r')) ^ 2 - ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 - R ^ 2 / (k : ℝ) ^ 2
          = ((R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2)
            - ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2 := by ring
      rw [e]
      calc |((R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2) - ((Nat.choose k (r' - 1) : ℝ) / D) ^ 2|
          ≤ |(R / ((k : ℝ) - r')) ^ 2 - R ^ 2 / (k : ℝ) ^ 2|
            + |((Nat.choose k (r' - 1) : ℝ) / D) ^ 2| := abs_sub _ _
        _ ≤ 8 * R ^ 3 / (k : ℝ) ^ 3 + 16 * R ^ 4 / (k : ℝ) ^ 3 := by
            rw [abs_of_nonneg h3]; linarith [hT2a]
        _ = (8 * R ^ 3 + 16 * R ^ 4) / (k : ℝ) ^ 3 := by ring
  -- the four contributions to `X - R² ψ(γ/R²)/k²`
  have hB1 : |(∑ m ∈ Finset.range r', dm k m * psi p (y m)) / D ^ 2|
      ≤ (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) / (k : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    have hterm : ∀ m ∈ Finset.range r',
        |dm k m * psi p (y m)| ≤ 2 * ((2 * R / k) ^ 2 * D) ^ 2 * Bψ := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [abs_mul]
      have h1 := dm_small (k := k) (r' := r') (m := m) hk2R hm
      rw [← hR, ← hD] at h1
      have h2 := hψbdd m (by rw [Finset.mem_range]; omega)
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    calc |∑ m ∈ Finset.range r', dm k m * psi p (y m)|
        ≤ ∑ m ∈ Finset.range r', |dm k m * psi p (y m)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.range r', 2 * ((2 * R / k) ^ 2 * D) ^ 2 * Bψ := Finset.sum_le_sum hterm
      _ = (r' : ℝ) * (2 * ((2 * R / k) ^ 2 * D) ^ 2 * Bψ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) / (k : ℝ) ^ 3 * D ^ 2 := by
          have e : (r' : ℝ) * (2 * ((2 * R / k) ^ 2 * D) ^ 2 * Bψ)
              = (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) * D ^ 2 / (k : ℝ) ^ 4 := by
            field_simp <;> ring
          have e2 : (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) / (k : ℝ) ^ 3 * D ^ 2
              = (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) * D ^ 2 / (k : ℝ) ^ 3 := by ring
          rw [e, e2]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkk4
  have hB2 : |(dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2) * psi p (y r')|
      ≤ (8 * R ^ 3 + 16 * R ^ 4) * Bψ / (k : ℝ) ^ 3 := by
    rw [abs_mul]
    have h1 := hψbdd r' (by rw [Finset.mem_range]; omega)
    calc |dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2| * |psi p (y r')|
        ≤ (8 * R ^ 3 + 16 * R ^ 4) / (k : ℝ) ^ 3 * Bψ :=
          mul_le_mul hT2d h1 (abs_nonneg _) (by positivity)
      _ = (8 * R ^ 3 + 16 * R ^ 4) * Bψ / (k : ℝ) ^ 3 := by ring
  have hB3 : |R ^ 2 / (k : ℝ) ^ 2 * (psi p (y r') - psi p (γ / R ^ 2))|
      ≤ R ^ 2 * L * (12 * γ * R) / (k : ℝ) ^ 3 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have h2 : |psi p (y r') - psi p (γ / R ^ 2)| ≤ L * (12 * γ * R / k) :=
      le_trans (hlip (y r') hyL) (mul_le_mul_of_nonneg_left hyr hL)
    calc R ^ 2 / (k : ℝ) ^ 2 * |psi p (y r') - psi p (γ / R ^ 2)|
        ≤ R ^ 2 / (k : ℝ) ^ 2 * (L * (12 * γ * R / k)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = R ^ 2 * L * (12 * γ * R) / (k : ℝ) ^ 3 := by field_simp <;> ring
  have hB4 : |dm k (r' + 1) / D ^ 2 * psi p (y (r' + 1))|
      ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by
    rw [hyR, abs_mul]
    have hdR : |dm k (r' + 1) / D ^ 2| ≤ 1 := by
      have h0 := hd (r' + 1) (by rw [Finset.mem_range]; omega)
      have h1 : dm k (r' + 1) ≤ D ^ 2 := by
        simp only [dm, if_neg (Nat.add_one_ne_zero r'), Nat.add_sub_cancel]
        rw [← hD]
        nlinarith [sq_nonneg (Nat.choose k r' : ℝ)]
      rw [abs_div, abs_of_nonneg h0, abs_of_pos (by positivity), div_le_one (by positivity)]
      exact h1
    have hψ := psi_quad hη₁' hC₁ hloc (-ρ) (by rw [abs_neg, abs_of_nonneg hρ0]; exact hρη)
    have hρ2' : ρ ^ 2 ≤ (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by
      calc ρ ^ 2 ≤ (2 * γ / (k : ℝ) ^ 2) ^ 2 := pow_le_pow_left hρ0 hρ1 2
        _ = (2 * γ) ^ 2 / (k : ℝ) ^ 4 := by rw [div_pow]; ring
    have h4 : (2 * γ) ^ 2 / (k : ℝ) ^ 4 ≤ (2 * γ) ^ 2 / (k : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hkk4
    have h5 : (|kappa p| + C₁) * (-ρ) ^ 2 ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by
      rw [neg_sq]
      have := mul_le_mul_of_nonneg_left (le_trans hρ2' h4)
        (by positivity : (0 : ℝ) ≤ |kappa p| + C₁)
      calc (|kappa p| + C₁) * ρ ^ 2 ≤ (|kappa p| + C₁) * ((2 * γ) ^ 2 / (k : ℝ) ^ 3) := this
        _ = (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by ring
    calc |dm k (r' + 1) / D ^ 2| * |psi p (-ρ)| ≤ 1 * ((|kappa p| + C₁) * (-ρ) ^ 2) :=
          mul_le_mul hdR hψ (abs_nonneg _) zero_le_one
      _ ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by rw [one_mul]; exact h5
  have hXY : |X - R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2| ≤ E / (k : ℝ) ^ 3 := by
    rw [hX, hsplit]
    have e : (∑ m ∈ Finset.range r', dm k m * psi p (y m) + dm k r' * psi p (y r')
          + dm k (r' + 1) * psi p (y (r' + 1))) / D ^ 2 - R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2
        = (∑ m ∈ Finset.range r', dm k m * psi p (y m)) / D ^ 2
          + (dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2) * psi p (y r')
          + R ^ 2 / (k : ℝ) ^ 2 * (psi p (y r') - psi p (γ / R ^ 2))
          + dm k (r' + 1) / D ^ 2 * psi p (y (r' + 1)) := by ring
    rw [e]
    have h1 := abs_add_three ((∑ m ∈ Finset.range r', dm k m * psi p (y m)) / D ^ 2)
      ((dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2) * psi p (y r'))
      (R ^ 2 / (k : ℝ) ^ 2 * (psi p (y r') - psi p (γ / R ^ 2)))
    have h2 := abs_add ((∑ m ∈ Finset.range r', dm k m * psi p (y m)) / D ^ 2
      + (dm k r' / D ^ 2 - R ^ 2 / (k : ℝ) ^ 2) * psi p (y r')
      + R ^ 2 / (k : ℝ) ^ 2 * (psi p (y r') - psi p (γ / R ^ 2)))
      (dm k (r' + 1) / D ^ 2 * psi p (y (r' + 1)))
    have h3 : 0 ≤ (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by positivity
    have e2 : E / (k : ℝ) ^ 3
        = (r' : ℝ) * (2 * (2 * R) ^ 4 * Bψ) / (k : ℝ) ^ 3
          + (8 * R ^ 3 + 16 * R ^ 4) * Bψ / (k : ℝ) ^ 3
          + R ^ 2 * L * (12 * γ * R) / (k : ℝ) ^ 3
          + (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3
          + (|kappa p| + C₁) * (2 * γ) ^ 2 / (k : ℝ) ^ 3 := by
      rw [hE]; ring
    rw [e2]
    linarith [hB1, hB2, hB3, hB4, h1, h2, h3]
  have hXb : |X| ≤ (R ^ 2 * P0 + E) / (k : ℝ) ^ 2 := by
    have h1 : |X| ≤ |R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2| + E / (k : ℝ) ^ 3 := by
      have := abs_sub_abs_le_abs_sub X (R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2)
      linarith
    have h2 : |R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2| = R ^ 2 * P0 / (k : ℝ) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < R ^ 2),
        abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
    have h3 : E / (k : ℝ) ^ 3 ≤ E / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hE0 (by positivity) hkk3
    have e : R ^ 2 * P0 / (k : ℝ) ^ 2 + E / (k : ℝ) ^ 2 = (R ^ 2 * P0 + E) / (k : ℝ) ^ 2 := by
      ring
    linarith
  have hX12 : |X| ≤ 1 / 2 := by
    refine le_trans hXb ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlog : Real.log (D ^ 2) = 2 * Real.log D := by
    rw [Real.log_pow]; norm_num
  have hB := B_identity p R γ hR0.ne'
  have e : Real.log (D ^ 2) + Fp p X - (2 * Real.log D - Bpr p R γ / (k : ℝ) ^ 2)
      = Fp p X - cp p * (R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2) := by
    rw [hlog, mul_div_assoc', hB]; ring
  rw [e]
  calc |Fp p X - cp p * (R ^ 2 * psi p (γ / R ^ 2) / (k : ℝ) ^ 2)|
      ≤ C₂ * X ^ 2 + |cp p| * (E / (k : ℝ) ^ 3) := final_step hF hXY hX12
    _ ≤ C₂ * ((R ^ 2 * P0 + E) / (k : ℝ) ^ 2) ^ 2 + |cp p| * (E / (k : ℝ) ^ 3) := by
        have h1 : X ^ 2 ≤ ((R ^ 2 * P0 + E) / (k : ℝ) ^ 2) ^ 2 := by
          rw [← sq_abs X]; exact pow_le_pow_left (abs_nonneg _) hXb 2
        have := mul_le_mul_of_nonneg_left h1 hC₂
        linarith
    _ ≤ (C₂ * (R ^ 2 * P0 + E) ^ 2 + |cp p| * E) / (k : ℝ) ^ 3 := by
        have e1 : C₂ * ((R ^ 2 * P0 + E) / (k : ℝ) ^ 2) ^ 2
            = C₂ * (R ^ 2 * P0 + E) ^ 2 / (k : ℝ) ^ 4 := by
          rw [div_pow]; ring
        have e2 : C₂ * (R ^ 2 * P0 + E) ^ 2 / (k : ℝ) ^ 4
            ≤ C₂ * (R ^ 2 * P0 + E) ^ 2 / (k : ℝ) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hkk4
        have e3 : (C₂ * (R ^ 2 * P0 + E) ^ 2 + |cp p| * E) / (k : ℝ) ^ 3
            = C₂ * (R ^ 2 * P0 + E) ^ 2 / (k : ℝ) ^ 3 + |cp p| * (E / (k : ℝ) ^ 3) := by ring
        linarith

end AppendixB

end
