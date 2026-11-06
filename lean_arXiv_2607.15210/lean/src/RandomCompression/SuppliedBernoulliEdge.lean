/-
# Compiled version of the supplied BernoulliEdge.lean

The supplied file proves scalar convex duality and several conditional limit
statements. Its `hedge` parameter assumes the actual spectral-edge identity;
therefore this file alone does not prove Lemma A.1 or Lemma II.3 under the
paper's permitted single convergence black box.

Changes from the supplied version: replace umbrella `import Mathlib` with
cached targeted imports and repair the `Tmap_diagonal` simplifier list.
The original theorem statements and explicit hypotheses are retained.
-/
import RandomCompression.CompressionEndpointGlue
import RandomCompression.CompressionSpectral
import RandomCompression.CompressionExtension
import RandomCompression.BernoulliCriticalPoint
import Entropy.OutputSpace

set_option maxHeartbeats 400000

noncomputable section

namespace BernoulliEdge

/-! ## Small helpers (kept separate so that any version-specific fix stays local) -/

theorem aux_le_of_sq_le_sq {x y : ℝ} (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : x ≤ y := by
  nlinarith

theorem aux_eq_of_sq_eq_sq {x y : ℝ} (h : x ^ 2 = y ^ 2) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x = y :=
  le_antisymm (aux_le_of_sq_le_sq h.le hy) (aux_le_of_sq_le_sq h.ge hx)

theorem aux_mul_div_cancel {c : ℝ} (hc : c ≠ 0) (x : ℝ) : c * (x / c) = x := by
  rw [mul_div_assoc', mul_comm c x, mul_div_assoc, div_self hc, mul_one]

theorem aux_div_mul_cancel {c : ℝ} (hc : c ≠ 0) (x : ℝ) : x / c * c = x := by
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hc, mul_one]

theorem aux_le_div {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  have h1 := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc.le)
  rw [mul_inv_cancel_right₀ hc.ne'] at h1
  rw [div_eq_mul_inv]
  exact h1

/-! ## The one-variable functions -/

/-- `c_t(u) = (√(t(1-u)) - √((1-t)u))²`. -/
def cfun (t u : ℝ) : ℝ := (Real.sqrt (t * (1 - u)) - Real.sqrt ((1 - t) * u)) ^ 2

/-- `Δ_t(y) = √((1-y)² + 4ty)`. -/
def disc (t y : ℝ) : ℝ := Real.sqrt ((1 - y) ^ 2 + 4 * t * y)

/-- `g_t(y) = y R_t(y) = (y - 1 + Δ_t(y)) / 2`. -/
def gfun (t y : ℝ) : ℝ := (y - 1 + disc t y) / 2

/-- `u_t(y) = (1 + (y + 2t - 1) / Δ_t(y)) / 2`. -/
def uopt (t y : ℝ) : ℝ := (1 + (y + 2 * t - 1) / disc t y) / 2

theorem cfun_nonneg (t u : ℝ) : 0 ≤ cfun t u := sq_nonneg _

theorem cfun_self (t : ℝ) : cfun t t = 0 := by
  unfold cfun
  rw [mul_comm (1 - t) t]
  simp

theorem disc_radicand (t y : ℝ) :
    (1 - y) ^ 2 + 4 * t * y = (y + 2 * t - 1) ^ 2 + 4 * t * (1 - t) := by
  ring

theorem radicand_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    0 < (1 - y) ^ 2 + 4 * t * y := by
  rw [disc_radicand]
  have : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  nlinarith [sq_nonneg (y + 2 * t - 1)]

theorem disc_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) : 0 < disc t y :=
  Real.sqrt_pos.2 (radicand_pos ht0 ht1 y)

/-- `Δ_t(y)² = (y + 2t - 1)² + 4t(1 - t)`. -/
theorem disc_sq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    disc t y ^ 2 = (y + 2 * t - 1) ^ 2 + 4 * t * (1 - t) := by
  unfold disc
  rw [Real.sq_sqrt (radicand_pos ht0 ht1 y).le, disc_radicand]

theorem disc_zero (t : ℝ) : disc t 0 = 1 := by
  unfold disc
  first
    | norm_num
    | simp

theorem uopt_zero (t : ℝ) : uopt t 0 = t := by
  unfold uopt
  rw [disc_zero]
  ring

/-- Expanding the square: `c_t(u) = t + (1-2t)u - 2√(t(1-t))√(u(1-u))` on `[0,1]`. -/
theorem cfun_expand {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    cfun t u
      = t + (1 - 2 * t) * u - 2 * (Real.sqrt (t * (1 - t)) * Real.sqrt (u * (1 - u))) := by
  have hA : 0 ≤ t * (1 - u) := mul_nonneg ht0 (by linarith)
  have hB : 0 ≤ (1 - t) * u := mul_nonneg (by linarith) hu0
  have hC : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  have hPQ : Real.sqrt (t * (1 - u)) * Real.sqrt ((1 - t) * u)
      = Real.sqrt (t * (1 - t)) * Real.sqrt (u * (1 - u)) := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_mul hC]
    congr 1
    ring
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  unfold cfun
  linear_combination h1 + h2 - 2 * hPQ

/-! ## The Legendre inequality (app-legendre-inequality), via Cauchy–Schwarz in `ℝ²` -/

/-- Algebraic core: `m(2u-1) + (2s)(2v) ≤ Δ` when `(2u-1)² + (2v)² = 1` and
`m² + (2s)² = Δ²`. -/
theorem cs_core {m s v d u t : ℝ} (hs : s ^ 2 = t * (1 - t)) (hv : v ^ 2 = u * (1 - u))
    (hd : d ^ 2 = m ^ 2 + 4 * t * (1 - t)) (hdnn : 0 ≤ d) :
    m * (2 * u - 1) + 4 * (s * v) ≤ d := by
  have key : d ^ 2 - (m * (2 * u - 1) + 4 * (s * v)) ^ 2
      = 4 * (s * (2 * u - 1) - m * v) ^ 2 := by
    linear_combination hd - (16 * s ^ 2 + 4 * m ^ 2) * hv - 4 * hs
  refine aux_le_of_sq_le_sq ?_ hdnn
  nlinarith [key, sq_nonneg (s * (2 * u - 1) - m * v)]

/-- **Legendre inequality**: `y v - c_t(v) ≤ g_t(y)` for `v ∈ [0,1]`. -/
theorem fenchel_young {t u : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (y : ℝ) : y * u - cfun t u ≤ gfun t y := by
  rw [cfun_expand ht0.le ht1.le hu0 hu1]
  have hs : Real.sqrt (t * (1 - t)) ^ 2 = t * (1 - t) :=
    Real.sq_sqrt (mul_nonneg ht0.le (by linarith))
  have hv : Real.sqrt (u * (1 - u)) ^ 2 = u * (1 - u) :=
    Real.sq_sqrt (mul_nonneg hu0 (by linarith))
  have hL := cs_core hs hv (disc_sq ht0 ht1 y) (disc_pos ht0 ht1 y).le
  unfold gfun
  linarith

theorem q_bounds {t d q m : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hd : 0 < d) (hq : q * d = m)
    (hdsq : d ^ 2 = m ^ 2 + 4 * t * (1 - t)) : -1 ≤ q ∧ q ≤ 1 := by
  have h1 : (1 - q ^ 2) * d ^ 2 = 4 * t * (1 - t) := by
    linear_combination hdsq - (q * d + m) * hq
  have h2 : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  have h3 : 0 < d ^ 2 := by positivity
  have h4 : 0 < 1 - q ^ 2 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (neg_nonneg.2 hcon) h3.le]
  constructor <;> nlinarith [h4]

theorem uopt_mem {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    0 ≤ uopt t y ∧ uopt t y ≤ 1 := by
  have hd := disc_pos ht0 ht1 y
  have hq : (y + 2 * t - 1) / disc t y * disc t y = y + 2 * t - 1 :=
    aux_div_mul_cancel hd.ne' _
  obtain ⟨h1, h2⟩ := q_bounds ht0 ht1 hd hq (disc_sq ht0 ht1 y)
  unfold uopt
  constructor <;> linarith

theorem uopt_mem' {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    uopt t y ∈ Set.Icc (0 : ℝ) 1 :=
  uopt_mem ht0 ht1 y

/-- Algebraic core of the equality case, with `u = (1+q)/2`, `q Δ = m`. -/
theorem fy_eq_core {t y d q s v : ℝ} (hd : 0 < d) (hq : q * d = y + 2 * t - 1)
    (hdsq : d ^ 2 = (y + 2 * t - 1) ^ 2 + 4 * t * (1 - t))
    (hs : s ^ 2 = t * (1 - t)) (hs0 : 0 ≤ s)
    (hv : v ^ 2 = (1 + q) / 2 * (1 - (1 + q) / 2)) (hv0 : 0 ≤ v) :
    (y - 1 + d) / 2
      = y * ((1 + q) / 2) - (t + (1 - 2 * t) * ((1 + q) / 2) - 2 * (s * v)) := by
  have hvd2 : (v * d) ^ 2 = s ^ 2 := by
    linear_combination d ^ 2 * hv + (1 / 4 : ℝ) * hdsq - hs
      - (q * d + (y + 2 * t - 1)) / 4 * hq
  have hvd : v * d = s := aux_eq_of_sq_eq_sq hvd2 (mul_nonneg hv0 hd.le) hs0
  have h1 : d * ((y + 2 * t - 1) * q + 4 * (s * v) - d) = 0 := by
    linear_combination (y + 2 * t - 1) * hq + 4 * s * hvd - hdsq + 4 * hs
  have h0 : (y + 2 * t - 1) * q + 4 * (s * v) - d = 0 :=
    (mul_eq_zero.mp h1).resolve_left hd.ne'
  linear_combination (-1 / 2 : ℝ) * h0

/-- **Equality case**: `g_t(y) = y u_t(y) - c_t(u_t(y))`. -/
theorem fy_eq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y : ℝ) :
    gfun t y = y * uopt t y - cfun t (uopt t y) := by
  obtain ⟨hu0, hu1⟩ := uopt_mem ht0 ht1 y
  rw [cfun_expand ht0.le ht1.le hu0 hu1]
  have hd := disc_pos ht0 ht1 y
  have hq : (y + 2 * t - 1) / disc t y * disc t y = y + 2 * t - 1 :=
    aux_div_mul_cancel hd.ne' _
  have hs : Real.sqrt (t * (1 - t)) ^ 2 = t * (1 - t) :=
    Real.sq_sqrt (mul_nonneg ht0.le (by linarith))
  have hv : Real.sqrt (uopt t y * (1 - uopt t y)) ^ 2 = uopt t y * (1 - uopt t y) :=
    Real.sq_sqrt (mul_nonneg hu0 (by linarith))
  unfold gfun
  exact fy_eq_core hd hq (disc_sq ht0 ht1 y) hs (Real.sqrt_nonneg _) hv (Real.sqrt_nonneg _)

/-! ## Continuity -/

theorem continuous_disc (t : ℝ) : Continuous (disc t) := by
  show Continuous fun y => Real.sqrt ((1 - y) ^ 2 + 4 * t * y)
  first
    | exact Real.continuous_sqrt.comp (by fun_prop)
    | fun_prop
    | continuity

theorem continuous_uopt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : Continuous (uopt t) := by
  have hne : ∀ y, disc t y ≠ 0 := fun y => (disc_pos ht0 ht1 y).ne'
  have hnum : Continuous fun y : ℝ => y + 2 * t - 1 := by fun_prop
  have hdiv : Continuous fun y => (y + 2 * t - 1) / disc t y := by
    first
      | exact hnum.div (continuous_disc t) hne
      | exact (hnum.mul ((continuous_disc t).inv₀ hne)).congr
          (fun y => (div_eq_mul_inv _ _).symm)
  show Continuous fun y => (1 + (y + 2 * t - 1) / disc t y) / 2
  exact (continuous_const.add hdiv).div_const 2

theorem continuous_cfun (t : ℝ) : Continuous (cfun t) := by
  show Continuous fun u => (Real.sqrt (t * (1 - u)) - Real.sqrt ((1 - t) * u)) ^ 2
  have h1 : Continuous fun u : ℝ => Real.sqrt (t * (1 - u)) := by
    first
      | exact Real.continuous_sqrt.comp (by fun_prop)
      | fun_prop
  have h2 : Continuous fun u : ℝ => Real.sqrt ((1 - t) * u) := by
    first
      | exact Real.continuous_sqrt.comp (by fun_prop)
      | fun_prop
  exact (h1.sub h2).pow 2

/-! ## The objects of the lemma -/

variable {k : ℕ}

/-- `𝒟_{k,t} = {u ∈ [0,1]^k : ∑ c_t(uᵢ) ≤ 1/k}`. -/
def Dset (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) ∩ {u | ∑ i, cfun t (u i) ≤ 1 / (k : ℝ)}

theorem mem_Dset_iff {t : ℝ} {u : Fin k → ℝ} :
    u ∈ Dset k t ↔ (∀ i, u i ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ i, cfun t (u i) ≤ 1 / (k : ℝ) := by
  simp only [Dset, Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_setOf_eq]

/-- The linear functional `u ↦ ∑ aᵢ uᵢ`. -/
def obj (a u : Fin k → ℝ) : ℝ := ∑ i, a i * u i

/-- `K_a(w) = (1 + k ∑ g_t(aᵢ w / k)) / w`, equation (app-K-a). -/
def K (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (w : ℝ) : ℝ :=
  (1 + (k : ℝ) * ∑ i, gfun t (a i * w / k)) / w

/-- The tangent point `u(w) = (u_t(aᵢ w / k))ᵢ`. -/
def uvec (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (w : ℝ) (i : Fin k) : ℝ :=
  uopt t (a i * w / k)

/-- `F_a(w) = ∑ c_t(uᵢ(w))`. -/
def F (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (w : ℝ) : ℝ :=
  ∑ i, cfun t (uvec k t a w i)

theorem F_nonneg (k : ℕ) (t : ℝ) (a : Fin k → ℝ) (w : ℝ) : 0 ≤ F k t a w :=
  Finset.sum_nonneg fun i _ => cfun_nonneg _ _

theorem F_zero (k : ℕ) (t : ℝ) (a : Fin k → ℝ) : F k t a 0 = 0 := by
  simp only [F, uvec, mul_zero, zero_div, uopt_zero, cfun_self, Finset.sum_const_zero]

theorem continuous_F {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : Fin k → ℝ) :
    Continuous (F k t a) := by
  have hc := continuous_cfun t
  have hu := continuous_uopt ht0 ht1
  show Continuous fun w => ∑ i, cfun t (uopt t (a i * w / k))
  first
    | exact continuous_finset_sum _ (fun i _ => hc.comp (hu.comp (by fun_prop)))
    | fun_prop

theorem isCompact_Dset (k : ℕ) (t : ℝ) : IsCompact (Dset k t) := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin k => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsum : Continuous fun u : Fin k → ℝ => ∑ i, cfun t (u i) :=
    continuous_finset_sum _ fun i _ => (continuous_cfun t).comp (continuous_apply i)
  have hclosed : IsClosed (Dset k t) :=
    (isClosed_set_pi fun i _ => isClosed_Icc).inter (isClosed_le hsum continuous_const)
  exact hbox.of_isClosed_subset hclosed (fun u hu => hu.1)

theorem const_mem_Dset (k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun _ => t) ∈ Dset k t := by
  rw [mem_Dset_iff]
  refine ⟨fun _ => ⟨ht0, ht1⟩, ?_⟩
  simp only [cfun_self, Finset.sum_const_zero]
  positivity

/-! ## Step 2: the upper bound (app-support-upper) -/

theorem weak_duality (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : Fin k → ℝ)
    {u : Fin k → ℝ} (hu : u ∈ Dset k t) {w : ℝ} (hw : 0 < w) :
    obj a u ≤ K k t a w := by
  rw [mem_Dset_iff] at hu
  obtain ⟨hbox, hsum⟩ := hu
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      w * (a i * u i) - (k : ℝ) * cfun t (u i) ≤ (k : ℝ) * gfun t (a i * w / k) := by
    intro i _
    have h := fenchel_young ht0 ht1 (hbox i).1 (hbox i).2 (a i * w / k)
    have h1 := mul_le_mul_of_nonneg_left h hkpos.le
    have e : (k : ℝ) * (a i * w / k) = a i * w := aux_mul_div_cancel hkne _
    have h2 : (k : ℝ) * (a i * w / k * u i - cfun t (u i))
        = w * (a i * u i) - (k : ℝ) * cfun t (u i) := by
      linear_combination (u i) * e
    linarith
  have hsum' := Finset.sum_le_sum hterm
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum'
  have hkc : (k : ℝ) * ∑ i, cfun t (u i) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hsum hkpos.le
    rwa [aux_mul_div_cancel hkne] at this
  unfold K obj
  apply aux_le_div hw
  linarith

/-! ## Step 1: the tangency identity (app-K-a-tangency) -/

theorem tangency_aux {w : ℝ} (hw : w ≠ 0) (O Fv κ : ℝ) :
    (1 + (w * O - κ * Fv)) / w = O + (1 - κ * Fv) / w := by
  have e : 1 + (w * O - κ * Fv) = w * O + (1 - κ * Fv) := by ring
  rw [e, add_div, mul_div_assoc, aux_mul_div_cancel hw]

theorem tangency (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : Fin k → ℝ)
    {w : ℝ} (hw : 0 < w) :
    K k t a w = obj a (uvec k t a w) + (1 - (k : ℝ) * F k t a w) / w := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hG : (k : ℝ) * ∑ i, gfun t (a i * w / k)
      = w * obj a (uvec k t a w) - (k : ℝ) * F k t a w := by
    simp only [obj, F, uvec]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fy_eq ht0 ht1 (a i * w / k)]
    have e : (k : ℝ) * (a i * w / k) = a i * w := aux_mul_div_cancel hkne _
    linear_combination (uopt t (a i * w / k)) * e
  unfold K
  rw [hG]
  exact tangency_aux hw.ne' _ _ _

/-! ## Step 3: the reverse inequality -/

/-- For every `ε > 0` there are `u ∈ 𝒟_{k,t}` and `w > 0` with `K_a(w) ≤ ∑ aᵢuᵢ + ε`. -/
theorem gap (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : Fin k → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ Dset k t, ∃ w : ℝ, 0 < w ∧ K k t a w ≤ obj a u + ε := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hFc : Continuous fun w => (k : ℝ) * F k t a w :=
    continuous_const.mul (continuous_F ht0 ht1 a)
  have hF0 : (k : ℝ) * F k t a 0 = 0 := by rw [F_zero, mul_zero]
  by_cases h : ∃ w₁ : ℝ, 0 < w₁ ∧ 1 ≤ (k : ℝ) * F k t a w₁
  · -- Case 1: the intermediate value theorem gives a tangency point `w₀`.
    obtain ⟨w₁, hw₁, hF₁⟩ := h
    have hmem : (1 : ℝ) ∈ Set.Icc ((fun w => (k : ℝ) * F k t a w) 0)
        ((fun w => (k : ℝ) * F k t a w) w₁) := by
      show (1 : ℝ) ∈ Set.Icc ((k : ℝ) * F k t a 0) ((k : ℝ) * F k t a w₁)
      rw [hF0]
      exact ⟨zero_le_one, hF₁⟩
    obtain ⟨w₀, hw₀I, hw₀⟩ := intermediate_value_Icc hw₁.le hFc.continuousOn hmem
    have hw₀' : (k : ℝ) * F k t a w₀ = 1 := hw₀
    have hw₀pos : 0 < w₀ := by
      rcases hw₀I.1.lt_or_eq with hlt | heq
      · exact hlt
      · rw [← heq, hF0] at hw₀'
        exact absurd hw₀' zero_ne_one
    refine ⟨uvec k t a w₀, ?_, w₀, hw₀pos, ?_⟩
    · rw [mem_Dset_iff]
      refine ⟨fun i => uopt_mem' ht0 ht1 (a i * w₀ / k), ?_⟩
      show F k t a w₀ ≤ 1 / (k : ℝ)
      apply aux_le_div hkpos
      linarith
    · rw [tangency hk ht0 ht1 a hw₀pos, hw₀', sub_self, zero_div, add_zero]
      linarith
  · -- Case 2: `k F_a < 1` everywhere; take `w = 1/ε`, so the error `(1 - kF_a)/w ≤ ε`.
    push_neg at h
    have hw : (0 : ℝ) < 1 / ε := one_div_pos.2 hε
    refine ⟨uvec k t a (1 / ε), ?_, 1 / ε, hw, ?_⟩
    · rw [mem_Dset_iff]
      refine ⟨fun i => uopt_mem' ht0 ht1 (a i * (1 / ε) / k), ?_⟩
      show F k t a (1 / ε) ≤ 1 / (k : ℝ)
      apply aux_le_div hkpos
      linarith [h (1 / ε) hw]
    · rw [tangency hk ht0 ht1 a hw, div_div_eq_mul_div, div_one]
      have hkF : 0 ≤ (k : ℝ) * F k t a (1 / ε) := mul_nonneg hkpos.le (F_nonneg k t a _)
      nlinarith [mul_nonneg hkF hε.le]

/-! ## Steps 1–3 combined: (app-support-inf) with attainment -/

theorem support_eq_inf_K (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) :
    ∃ m : ℝ, IsGreatest (obj a '' Dset k t) m ∧ IsGLB (K k t a '' Set.Ioi 0) m := by
  have hobj : Continuous fun u : Fin k → ℝ => obj a u := by
    unfold obj
    first
      | exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)
      | fun_prop
  obtain ⟨u₀, hu₀, hmax⟩ :=
    (isCompact_Dset k t).exists_isMaxOn ⟨_, const_mem_Dset k ht0.le ht1.le⟩
      hobj.continuousOn
  have hmax' : ∀ u ∈ Dset k t, obj a u ≤ obj a u₀ := isMaxOn_iff.mp hmax
  refine ⟨obj a u₀, ⟨⟨u₀, hu₀, rfl⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hmax' u hu
  · rintro _ ⟨w, hw, rfl⟩
    exact weak_duality hk ht0 ht1 a hu₀ hw
  · intro b hb
    by_contra hlt
    push_neg at hlt
    obtain ⟨u, hu, w, hw, hK⟩ := gap hk ht0 ht1 a (half_pos (sub_pos.2 hlt))
    have h1 : b ≤ K k t a w := hb ⟨w, hw, rfl⟩
    have h2 : obj a u ≤ obj a u₀ := hmax' u hu
    linarith

/-! ## The lemma -/

/-- **Lemma (Bernoulli edge and convex duality).**
Let `r = max supp μ_{a,t}`.  Step 4 of the proof (free probability, not in Mathlib)
shows `r = inf_{w>0} K_a(w)`; this is the hypothesis `hedge`.  Then `r` is the
maximum of `u ↦ ∑ aᵢ uᵢ` over `𝒟_{k,t}`, and the maximum is attained. -/
theorem bernoulli_edge_duality (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (a : Fin k → ℝ) {r : ℝ} (hedge : IsGLB (K k t a '' Set.Ioi 0) r) :
    IsGreatest (obj a '' Dset k t) r := by
  obtain ⟨m, hmax, hglb⟩ := support_eq_inf_K hk ht0 ht1 a
  rwa [hedge.unique hglb]

/-! ## The random compression formula (Lemma `lem:random-matrix-input`)

Proved here:
* `lamMax_Scomp_lipschitz`: for every orthogonal projection `P` on `ℂⁿ ⊗ ℂᵏ`, the map
  `a ↦ λ_max(S_n(a))`, `S_n(a) = ∑ᵢ aᵢ P_{ii}`, is 1-Lipschitz for the ℓ¹-distance
  (because `0 ≤ P_{ii} ≤ I`);
* `isGreatest_lipschitz`: `a ↦ max_{u ∈ 𝒟_{k,t}} ∑ aᵢ uᵢ` is 1-Lipschitz for the
  ℓ¹-distance (because `𝒟_{k,t} ⊆ [0,1]^k`);
* `ae_forall_of_lipschitz`: almost-sure convergence for each fixed `a` upgrades to
  almost-sure convergence simultaneously for all `a` (countable dense set of `a`);
* `random_compression`: the lemma, from two inputs taken as hypotheses:
  (H1) `hBM`: for each fixed `a`, almost surely `λ_max(S_n(a)) → max supp μ_{a,t}`
       (strong block-modification theorem plus the definition of strong convergence;
       this needs free probability, which Mathlib does not have);
  (H2) `hedge`: `max supp μ_{a,t} = inf_{w>0} K_a(w)`
       (Step 4 of Lemma `lem:bernoulli-edge-duality`).
  Haar invariance of `P_n` and `d_n/(kn) → t` enter only through (H1).
-/

section RandomCompression

open MeasureTheory Filter Topology
open scoped Matrix ComplexOrder

/-- The ℓ¹-distance on `ℝᵏ`. -/
def l1dist {k : ℕ} (a b : Fin k → ℝ) : ℝ := ∑ i, |a i - b i|

theorem l1dist_comm {k : ℕ} (a b : Fin k → ℝ) : l1dist a b = l1dist b a :=
  Finset.sum_congr rfl fun i _ => abs_sub_comm _ _

theorem l1dist_nonneg {k : ℕ} (a b : Fin k → ℝ) : 0 ≤ l1dist a b :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

/-! ### The support function of `𝒟_{k,t}` is 1-Lipschitz -/

theorem obj_sub {k : ℕ} (a b u : Fin k → ℝ) :
    obj a u - obj b u = ∑ i, (a i - b i) * u i := by
  unfold obj
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem obj_sub_le {k : ℕ} {t : ℝ} (a b : Fin k → ℝ) {u : Fin k → ℝ}
    (hu : u ∈ Dset k t) : obj a u - obj b u ≤ l1dist a b := by
  rw [obj_sub, l1dist]
  rw [mem_Dset_iff] at hu
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨h0, h1⟩ := hu.1 i
  calc (a i - b i) * u i ≤ |a i - b i| * u i :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ |a i - b i| := mul_le_of_le_one_right (abs_nonneg _) h1

theorem isGreatest_lipschitz {k : ℕ} {t : ℝ} {a b : Fin k → ℝ} {ma mb : ℝ}
    (ha : IsGreatest (obj a '' Dset k t) ma) (hb : IsGreatest (obj b '' Dset k t) mb) :
    |ma - mb| ≤ l1dist a b := by
  obtain ⟨⟨ua, hua, rfl⟩, haub⟩ := ha
  obtain ⟨⟨ub, hub, rfl⟩, hbub⟩ := hb
  have h1 : obj b ua ≤ obj b ub := hbub ⟨ua, hua, rfl⟩
  have h2 : obj a ub ≤ obj a ua := haub ⟨ub, hub, rfl⟩
  have h3 := obj_sub_le a b hua
  have h4 := obj_sub_le b a hub
  rw [l1dist_comm b a] at h4
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ### From each fixed `a` to all `a` simultaneously -/

theorem ae_forall_of_lipschitz {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    (L : ℕ → (Fin k → ℝ) → Ω → ℝ) (h : (Fin k → ℝ) → ℝ)
    (hL : ∀ n a b ω, |L n a ω - L n b ω| ≤ l1dist a b)
    (hh : ∀ a b, |h a - h b| ≤ l1dist a b)
    (hconv : ∀ a, ∀ᵐ ω ∂μ, Tendsto (fun n => L n a ω) atTop (𝓝 (h a))) :
    ∀ᵐ ω ∂μ, ∀ a, Tendsto (fun n => L n a ω) atTop (𝓝 (h a)) := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (Fin k → ℝ)
  haveI : Countable s := hsc.to_subtype
  have hs : ∀ᵐ ω ∂μ, ∀ q : s, Tendsto (fun n => L n q.1 ω) atTop (𝓝 (h q.1)) :=
    ae_all_iff.2 fun q => hconv q.1
  filter_upwards [hs] with ω hω a
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hδ : 0 < ε / (3 * (k + 1)) := div_pos hε (by positivity)
  obtain ⟨q, hqs, hq⟩ := hsd.exists_dist_lt a hδ
  -- the ℓ¹-distance from `a` to the nearby point `q` of the dense set
  have hl1 : l1dist a q < ε / 3 := by
    have hsum : l1dist a q ≤ ∑ _i : Fin k, dist a q := by
      unfold l1dist
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← Real.dist_eq]
      exact dist_le_pi_dist a q i
    have hconst : ∑ _i : Fin k, dist a q = k * dist a q := by simp
    have hle : l1dist a q ≤ (k + 1) * dist a q := by
      nlinarith [dist_nonneg (x := a) (y := q)]
    calc l1dist a q ≤ (k + 1) * dist a q := hle
      _ < (k + 1) * (ε / (3 * (k + 1))) := mul_lt_mul_of_pos_left hq hk1
      _ = ε / 3 := by
        first
          | rw [mul_div_assoc', mul_comm (3 : ℝ) _, mul_div_mul_left ε 3 hk1.ne']
          | (field_simp; ring)
          | field_simp
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hω ⟨q, hqs⟩) (ε / 3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hL n a q ω
  have h2 := hh q a
  rw [l1dist_comm q a] at h2
  have h3 : |L n q ω - h q| < ε / 3 := by
    have := hN n hn
    rwa [Real.dist_eq] at this
  rw [Real.dist_eq]
  have t1 := abs_sub_le (L n a ω) (L n q ω) (h a)
  have t2 := abs_sub_le (L n q ω) (h q) (h a)
  linarith

/-! ### The concrete matrices `S_n(a) = ∑ᵢ aᵢ P_{ii}` -/

variable {n : ℕ}

/-- The diagonal block `P_{ii}` of `P = ∑_{i,j} P_{ij} ⊗ |i⟩⟨j|`, for the basis
`|x⟩ ⊗ |i⟩ ↦ (x, i)` of `ℂⁿ ⊗ ℂᵏ`. -/
def block {k : ℕ} (P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) (i : Fin k) :
    Matrix (Fin n) (Fin n) ℂ :=
  P.submatrix (fun x => (x, i)) (fun x => (x, i))

/-- `S_n(a) = ∑ᵢ aᵢ P_{ii}`. -/
def Scomp {k : ℕ} (P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) (a : Fin k → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (a i : ℂ) • block P i

/-- The Rayleigh quotient `Re ⟨v, X v⟩`. -/
def rayleigh (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (star v ⬝ᵥ (X *ᵥ v)).re

/-- Unit vectors of `ℂⁿ`. -/
abbrev UnitVec (n : ℕ) := {v : Fin n → ℂ // (star v ⬝ᵥ v).re = 1}

/-- `λ_max(X) = sup_{‖v‖ = 1} Re ⟨v, X v⟩`.  For Hermitian `X` this is the largest
eigenvalue (Rayleigh–Ritz). -/
def lamMax (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ⨆ v : UnitVec n, rayleigh X v.1

theorem rayleigh_add (X Y : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    rayleigh (X + Y) v = rayleigh X v + rayleigh Y v := by
  simp [rayleigh, Matrix.add_mulVec]

theorem rayleigh_smul (c : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    rayleigh ((c : ℂ) • X) v = c * rayleigh X v := by
  first
    | simp [rayleigh, Matrix.smul_mulVec_assoc]
    | (unfold rayleigh; rw [Matrix.smul_mulVec_assoc]; simp)

theorem rayleigh_Scomp {k : ℕ} (P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
    (a : Fin k → ℝ) (v : Fin n → ℂ) :
    rayleigh (Scomp P a) v = ∑ i, a i * rayleigh (block P i) v := by
  let φ : Matrix (Fin n) (Fin n) ℂ →+ ℝ :=
    AddMonoidHom.mk' (fun X => rayleigh X v) (fun X Y => rayleigh_add X Y v)
  have h : φ (∑ i, (a i : ℂ) • block P i) = ∑ i, φ ((a i : ℂ) • block P i) :=
    map_sum φ _ _
  have hφ : ∀ X, φ X = rayleigh X v := by
    intro X
    first
      | rfl
      | simp [φ]
  simp only [hφ] at h
  unfold Scomp
  rw [h]
  exact Finset.sum_congr rfl fun i _ => rayleigh_smul (a i) (block P i) v

/-- For an orthogonal projection `P`, `0 ≤ ⟨v, P_{ii} v⟩ ≤ ⟨v, v⟩`. -/
theorem rayleigh_block_bounds {k : ℕ} {P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ}
    (hPh : P.IsHermitian) (hPP : P * P = P) (i : Fin k) (v : Fin n → ℂ) :
    0 ≤ rayleigh (block P i) v ∧ rayleigh (block P i) v ≤ (star v ⬝ᵥ v).re := by
  -- `P` and `1 - P` are positive semidefinite
  have hP : P.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [hPh.eq, hPP] at h
  have hQ : (1 - P).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
    have e : (1 - P)ᴴ * (1 - P) = 1 - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh.eq, mul_sub, mul_one,
        sub_mul, one_mul, hPP, sub_self, sub_zero]
    rwa [e] at h
  -- compressions of positive semidefinite matrices are positive semidefinite
  have hB : (block P i).PosSemidef := hP.submatrix _
  have e2 : (1 - P).submatrix (fun x : Fin n => (x, i)) (fun x => (x, i)) = 1 - block P i := by
    ext x y
    simp [block, Matrix.one_apply]
  have hC : (1 - block P i).PosSemidef := by
    have h := hQ.submatrix (fun x : Fin n => (x, i))
    rwa [e2] at h
  have nonneg : ∀ {M : Matrix (Fin n) (Fin n) ℂ}, M.PosSemidef → 0 ≤ rayleigh M v := by
    intro M hM
    unfold rayleigh
    first
      | exact (Complex.nonneg_iff.mp (hM.2 v)).1
      | simpa using (Complex.le_def.mp (hM.2 v)).1
      | exact hM.re_dotProduct_nonneg v
  have e3 : rayleigh (1 - block P i) v = (star v ⬝ᵥ v).re - rayleigh (block P i) v := by
    simp [rayleigh, Matrix.sub_mulVec]
  have h2 := nonneg hC
  rw [e3] at h2
  exact ⟨nonneg hB, by linarith⟩

/-- `|λ_max(S_n(a)) - λ_max(S_n(b))| ≤ ‖a - b‖₁` for every orthogonal projection `P`. -/
theorem lamMax_Scomp_lipschitz {k : ℕ} {P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ}
    (hPh : P.IsHermitian) (hPP : P * P = P) (a b : Fin k → ℝ) :
    |lamMax (Scomp P a) - lamMax (Scomp P b)| ≤ l1dist a b := by
  have hr : ∀ (v : UnitVec n) (i : Fin k),
      0 ≤ rayleigh (block P i) v.1 ∧ rayleigh (block P i) v.1 ≤ 1 := fun v i =>
    ⟨(rayleigh_block_bounds hPh hPP i v.1).1,
      (rayleigh_block_bounds hPh hPP i v.1).2.trans_eq v.2⟩
  have hcmp : ∀ (c d : Fin k → ℝ) (v : UnitVec n),
      rayleigh (Scomp P c) v.1 ≤ rayleigh (Scomp P d) v.1 + l1dist c d := by
    intro c d v
    rw [rayleigh_Scomp, rayleigh_Scomp, l1dist, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h0, h1⟩ := hr v i
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self (c i - d i))) h0,
      mul_nonneg (abs_nonneg (c i - d i)) (sub_nonneg.2 h1)]
  have hbdd : ∀ c : Fin k → ℝ,
      BddAbove (Set.range fun v : UnitVec n => rayleigh (Scomp P c) v.1) := by
    intro c
    refine ⟨∑ i, |c i|, ?_⟩
    rintro _ ⟨v, rfl⟩
    show rayleigh (Scomp P c) v.1 ≤ ∑ i, |c i|
    rw [rayleigh_Scomp]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h0, h1⟩ := hr v i
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self (c i))) h0,
      mul_nonneg (abs_nonneg (c i)) (sub_nonneg.2 h1)]
  rcases isEmpty_or_nonempty (UnitVec n) with hE | hN
  · have h0 : ∀ X : Matrix (Fin n) (Fin n) ℂ, lamMax X = 0 := fun X =>
      Real.iSup_of_isEmpty _
    rw [h0, h0, sub_self, abs_zero]
    exact l1dist_nonneg a b
  · have key : ∀ c d : Fin k → ℝ, lamMax (Scomp P c) ≤ lamMax (Scomp P d) + l1dist c d := by
      intro c d
      apply ciSup_le
      intro v
      exact (hcmp c d v).trans (add_le_add_right (le_ciSup (hbdd d) v) _)
    rw [abs_sub_le_iff]
    constructor
    · linarith [key a b]
    · linarith [key b a, l1dist_comm a b]

/-! ### The lemma -/

/-- **Lemma (random compression formula), formal form.**
Let `P n ω` be orthogonal projections on `ℂⁿ ⊗ ℂᵏ` (for the paper: Haar random
projections of rank `d_n` with `d_n/(kn) → t`), and `edge a = max supp μ_{a,t}`.
Assume
* `hBM`: for each fixed `a`, almost surely `λ_max(S_n(a)) → edge a`
  (strong block-modification theorem and the definition of strong convergence);
* `hedge`: `edge a = inf_{w>0} K_a(w)` (Step 4 of Lemma `lem:bernoulli-edge-duality`).
Then, on a single event of probability one, simultaneously for every `a`,
`λ_max(S_n(a)) → edge a`, and `edge a` is the maximum of `∑ aᵢ uᵢ` over `𝒟_{k,t}`. -/
theorem random_compression (hk : 0 < k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : ∀ n : ℕ, Ω → Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
    (hPh : ∀ n ω, (P n ω).IsHermitian) (hPP : ∀ n ω, P n ω * P n ω = P n ω)
    (edge : (Fin k → ℝ) → ℝ)
    (hBM : ∀ a, ∀ᵐ ω ∂μ,
      Tendsto (fun n => lamMax (Scomp (P n ω) a)) atTop (𝓝 (edge a)))
    (hedge : ∀ a, IsGLB (K k t a '' Set.Ioi 0) (edge a)) :
    ∀ᵐ ω ∂μ, ∀ a : Fin k → ℝ,
      Tendsto (fun n => lamMax (Scomp (P n ω) a)) atTop (𝓝 (edge a)) ∧
        IsGreatest (obj a '' Dset k t) (edge a) := by
  have hmax : ∀ a, IsGreatest (obj a '' Dset k t) (edge a) :=
    fun a => bernoulli_edge_duality hk ht0 ht1 a (hedge a)
  have hlipE : ∀ a b, |edge a - edge b| ≤ l1dist a b :=
    fun a b => isGreatest_lipschitz (hmax a) (hmax b)
  have hlipL : ∀ (n : ℕ) (a b : Fin k → ℝ) (ω : Ω),
      |lamMax (Scomp (P n ω) a) - lamMax (Scomp (P n ω) b)| ≤ l1dist a b :=
    fun n a b ω => lamMax_Scomp_lipschitz (hPh n ω) (hPP n ω) a b
  filter_upwards [ae_forall_of_lipschitz (fun n a ω => lamMax (Scomp (P n ω) a)) edge
    hlipL hlipE hBM] with ω hω a
  exact ⟨hω a, hmax a⟩

end RandomCompression

/-! ## Section `sec:output-space`: support functions of the output set

Proved here:
* `sum_pos_of_mem_Dset`: if `t > 1/k²` then `∑ uᵢ > 0` on `𝒟_{k,t}`, so `u/∑ uᵢ` is defined;
* `exists_max_ratio`: the maximum of `⟨h,u⟩/∑ uᵢ` over `𝒟_{k,t}` is attained;
  its value is `h_{𝒦_{k,t}}(diag h)`, eq. (limit-support-formula);
* `Tmap_diagonal`: `T_n(diag c) = S_n(c)`, the partial-trace step of Step 2;
* `lamMax_Scomp_antitone`: `λ ↦ λ_max(S_n(h - λ𝟙))` is nonincreasing;
* `tendsto_sInf_of_antitone`: roots of nonincreasing functions converge;
* `support_limit_diag`: Step 2 of the proof: almost surely, for every `h ∈ ℝᵏ`,
  `inf {λ : λ_max(S_n(h - λ𝟙)) ≤ 0} → max_{u ∈ 𝒟_{k,t}} ⟨h,u⟩/∑ uᵢ`;
* `ae_tendstoUniformlyOn_of_lipschitz`: Step 4 of the proof (the δ-net argument).
Not formalised: Lemma `lem:support-channel` (congruence by `P_{A,n}^{-1/2}`), the rotation
to diagonal `H` in Step 3 (Haar invariance), Lemma `lem:hausdorff-support` (minimax),
von Neumann's trace inequality in Step 1, and the corollary.
-/

section OutputSpace

open MeasureTheory Filter Topology
open scoped Matrix ComplexOrder

variable {n : ℕ}

/-- `c_t(0) = t`. -/
theorem cfun_zero {t : ℝ} (ht : 0 ≤ t) : cfun t 0 = t := by
  unfold cfun
  simp [Real.sq_sqrt ht]

/-- If `t > 1/k²`, then `0 ∉ 𝒟_{k,t}`, i.e. `∑ uᵢ > 0` for every `u ∈ 𝒟_{k,t}`. -/
theorem sum_pos_of_mem_Dset {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 1 / (k : ℝ) ^ 2 < t)
    {u : Fin k → ℝ} (hu : u ∈ Dset k t) : 0 < ∑ i, u i := by
  rw [mem_Dset_iff] at hu
  obtain ⟨hbox, hsum⟩ := hu
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have ht0 : 0 ≤ t := le_trans (by positivity) ht.le
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ u i := fun i _ => (hbox i).1
  rcases (Finset.sum_nonneg hnn).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hzero : ∀ i, u i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg hnn).1 heq.symm i (Finset.mem_univ i)
    have hc : ∑ i, cfun t (u i) = k * t := by
      simp [hzero, cfun_zero ht0]
    rw [hc] at hsum
    have h1 := mul_le_mul_of_nonneg_right hsum hkpos.le
    have h2 := mul_lt_mul_of_pos_right ht (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)
    have e1 : 1 / (k : ℝ) ^ 2 * (k : ℝ) ^ 2 = 1 := by
      first
        | exact one_div_mul_cancel (pow_ne_zero 2 hkne)
        | field_simp
    have e2 : 1 / (k : ℝ) * (k : ℝ) = 1 := by
      first
        | exact one_div_mul_cancel hkne
        | field_simp
    nlinarith [h1, h2, e1, e2]

theorem obj_sub_const {k : ℕ} (h u : Fin k → ℝ) (s : ℝ) :
    obj (fun i => h i - s) u = obj h u - s * ∑ i, u i := by
  unfold obj
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The ratio `⟨h,u⟩ / ∑ uᵢ`. -/
def ratio {k : ℕ} (h u : Fin k → ℝ) : ℝ := obj h u / ∑ i, u i

/-- The maximum of `⟨h,u⟩ / ∑ uᵢ` over `𝒟_{k,t}` is attained. -/
theorem exists_max_ratio {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 1 / (k : ℝ) ^ 2 < t)
    (ht1 : t < 1) (h : Fin k → ℝ) :
    ∃ u₀ ∈ Dset k t, ∀ u ∈ Dset k t, ratio h u ≤ ratio h u₀ := by
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
  have hnum : Continuous fun u : Fin k → ℝ => obj h u := by
    unfold obj
    first
      | exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)
      | fun_prop
  have hden : Continuous fun u : Fin k → ℝ => ∑ i, u i :=
    continuous_finset_sum _ fun i _ => continuous_apply i
  have hcont : ContinuousOn (fun u : Fin k → ℝ => ratio h u) (Dset k t) :=
    hnum.continuousOn.div hden.continuousOn
      (fun u hu => (sum_pos_of_mem_Dset hk ht hu).ne')
  obtain ⟨u₀, hu₀, hmax⟩ :=
    (isCompact_Dset k t).exists_isMaxOn ⟨_, const_mem_Dset k ht0.le ht1.le⟩ hcont
  exact ⟨u₀, hu₀, fun u hu => isMaxOn_iff.mp hmax u hu⟩

/-- `T_n(H) = Tr_B(P_n (I_n ⊗ H))`, eq. (def-T-map), for the basis `|x⟩ ⊗ |j⟩ ↦ (x, j)`. -/
def Tmap {k : ℕ} (P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
    (H : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun x y => ∑ j, ∑ l, P (x, j) (y, l) * H l j

/-- The partial-trace step of Step 2: `T_n(diag c) = ∑ᵢ cᵢ P_{ii} = S_n(c)`. -/
theorem Tmap_diagonal {k : ℕ} (P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
    (c : Fin k → ℝ) :
    Tmap P (Matrix.diagonal fun i => (c i : ℂ)) = Scomp P c := by
  ext x y
  simp [Tmap, Scomp, block, Matrix.diagonal_apply, mul_comm, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]

theorem rayleigh_block_unit {k : ℕ} {P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ}
    (hPh : P.IsHermitian) (hPP : P * P = P) (v : UnitVec n) (i : Fin k) :
    0 ≤ rayleigh (block P i) v.1 ∧ rayleigh (block P i) v.1 ≤ 1 :=
  ⟨(rayleigh_block_bounds hPh hPP i v.1).1,
    (rayleigh_block_bounds hPh hPP i v.1).2.trans_eq v.2⟩

theorem bddAbove_rayleigh_Scomp {k : ℕ} {P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ}
    (hPh : P.IsHermitian) (hPP : P * P = P) (c : Fin k → ℝ) :
    BddAbove (Set.range fun v : UnitVec n => rayleigh (Scomp P c) v.1) := by
  refine ⟨∑ i, |c i|, ?_⟩
  rintro _ ⟨v, rfl⟩
  show rayleigh (Scomp P c) v.1 ≤ ∑ i, |c i|
  rw [rayleigh_Scomp]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨h0, h1⟩ := rayleigh_block_unit hPh hPP v i
  nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self (c i))) h0,
    mul_nonneg (abs_nonneg (c i)) (sub_nonneg.2 h1)]

/-- `λ ↦ λ_max(S_n(h - λ𝟙))` is nonincreasing, since `S_n(h - λ𝟙) = S_n(h) - λ P_{A,n}`
and `P_{A,n} ≥ 0`. -/
theorem lamMax_Scomp_antitone {k : ℕ} {P : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ}
    (hPh : P.IsHermitian) (hPP : P * P = P) (h : Fin k → ℝ) {s s' : ℝ} (hss : s ≤ s') :
    lamMax (Scomp P fun i => h i - s') ≤ lamMax (Scomp P fun i => h i - s) := by
  rcases isEmpty_or_nonempty (UnitVec n) with hE | hN
  · have h0 : ∀ X : Matrix (Fin n) (Fin n) ℂ, lamMax X = 0 := fun X =>
      Real.iSup_of_isEmpty _
    simp only [h0, le_refl]
  · apply ciSup_le
    intro v
    refine le_trans ?_ (le_ciSup (bddAbove_rayleigh_Scomp hPh hPP _) v)
    show rayleigh (Scomp P fun i => h i - s') v.1 ≤ rayleigh (Scomp P fun i => h i - s) v.1
    rw [rayleigh_Scomp, rayleigh_Scomp]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h0, -⟩ := rayleigh_block_unit hPh hPP v i
    nlinarith [mul_nonneg (sub_nonneg.2 hss) h0]

/-- **Roots of nonincreasing functions converge.**  If each `f n` is nonincreasing and,
for every `ε > 0`, eventually `f n (m - ε) > 0 > f n (m + ε)`, then
`inf {s : f n s ≤ 0} → m`. -/
theorem tendsto_sInf_of_antitone (f : ℕ → ℝ → ℝ) (m : ℝ) (hanti : ∀ n, Antitone (f n))
    (hlo : ∀ ε > 0, ∀ᶠ n in atTop, 0 < f n (m - ε))
    (hhi : ∀ ε > 0, ∀ᶠ n in atTop, f n (m + ε) < 0) :
    Tendsto (fun n => sInf {s : ℝ | f n s ≤ 0}) atTop (𝓝 m) := by
  have key : ∀ ε > 0, ∀ᶠ n in atTop,
      m - ε ≤ sInf {s : ℝ | f n s ≤ 0} ∧ sInf {s : ℝ | f n s ≤ 0} ≤ m + ε := by
    intro ε hε
    filter_upwards [hlo ε hε, hhi ε hε] with n h1 h2
    have hmem : m + ε ∈ {s : ℝ | f n s ≤ 0} := le_of_lt h2
    have hlow : ∀ s ∈ {s : ℝ | f n s ≤ 0}, m - ε ≤ s := by
      intro s hs
      by_contra hlt
      push_neg at hlt
      have hmono := hanti n hlt.le
      have hs' : f n s ≤ 0 := hs
      linarith
    exact ⟨le_csInf ⟨_, hmem⟩ hlow, csInf_le ⟨m - ε, hlow⟩ hmem⟩
  rw [tendsto_order]
  refine ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · filter_upwards [key ((m - a') / 2) (by linarith)] with n hn
    linarith [hn.1]
  · filter_upwards [key ((a' - m) / 2) (by linarith)] with n hn
    linarith [hn.2]

/-- **Step 2 of the proof of Theorem `thm:output-space-limit` (diagonal `H`).**
Under the hypotheses of `random_compression` and `t ∈ (1/k², 1)`, almost surely, for
every `h ∈ ℝᵏ`, the support function `h_n(diag h) = inf {λ : λ_max(S_n(h - λ𝟙)) ≤ 0}`
(Lemma `lem:support-channel` and `Tmap_diagonal`) converges to
`max_{u ∈ 𝒟_{k,t}} ⟨h,u⟩/∑ uᵢ = h_{𝒦_{k,t}}(diag h)`. -/
theorem support_limit_diag (hk : 0 < k) {t : ℝ} (ht : 1 / (k : ℝ) ^ 2 < t) (ht1 : t < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : ∀ n : ℕ, Ω → Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ)
    (hPh : ∀ n ω, (P n ω).IsHermitian) (hPP : ∀ n ω, P n ω * P n ω = P n ω)
    (edge : (Fin k → ℝ) → ℝ)
    (hBM : ∀ a, ∀ᵐ ω ∂μ,
      Tendsto (fun n => lamMax (Scomp (P n ω) a)) atTop (𝓝 (edge a)))
    (hedge : ∀ a, IsGLB (K k t a '' Set.Ioi 0) (edge a)) :
    ∀ᵐ ω ∂μ, ∀ h : Fin k → ℝ, ∃ u₀ ∈ Dset k t,
      (∀ u ∈ Dset k t, ratio h u ≤ ratio h u₀) ∧
      Tendsto (fun n => sInf {s : ℝ | lamMax (Scomp (P n ω) fun i => h i - s) ≤ 0})
        atTop (𝓝 (ratio h u₀)) := by
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
  filter_upwards [random_compression hk ht0 ht1 μ P hPh hPP edge hBM hedge] with ω hω h
  obtain ⟨u₀, hu₀, hmax⟩ := exists_max_ratio hk ht ht1 h
  refine ⟨u₀, hu₀, hmax, ?_⟩
  have hpos0 := sum_pos_of_mem_Dset hk ht hu₀
  have hobj0 : obj h u₀ = ratio h u₀ * ∑ i, u₀ i := (aux_div_mul_cancel hpos0.ne' _).symm
  apply tendsto_sInf_of_antitone (fun n s => lamMax (Scomp (P n ω) fun i => h i - s))
    (ratio h u₀)
  · intro n a b hab
    exact lamMax_Scomp_antitone (hPh n ω) (hPP n ω) h hab
  · intro ε hε
    have hB : 0 < edge (fun i => h i - (ratio h u₀ - ε)) := by
      have hle : obj (fun i => h i - (ratio h u₀ - ε)) u₀ ≤
          edge (fun i => h i - (ratio h u₀ - ε)) :=
        (hω (fun i => h i - (ratio h u₀ - ε))).2.2 ⟨u₀, hu₀, rfl⟩
      rw [obj_sub_const] at hle
      nlinarith [mul_pos hε hpos0]
    exact (hω (fun i => h i - (ratio h u₀ - ε))).1.eventually_const_lt hB
  · intro ε hε
    have hA : edge (fun i => h i - (ratio h u₀ + ε)) < 0 := by
      obtain ⟨⟨u', hu', he⟩, -⟩ := (hω (fun i => h i - (ratio h u₀ + ε))).2
      rw [← he, obj_sub_const]
      have hpos := sum_pos_of_mem_Dset hk ht hu'
      have hobj : obj h u' = ratio h u' * ∑ i, u' i := (aux_div_mul_cancel hpos.ne' _).symm
      nlinarith [mul_le_mul_of_nonneg_right (hmax u' hu') hpos.le, mul_pos hε hpos]
    exact (hω (fun i => h i - (ratio h u₀ + ε))).1.eventually_lt_const hA

/-- **Step 4 (the δ-net argument), deterministic form.**  If `g n` and `g₀` are
1-Lipschitz and `g n x → g₀ x` for every `x` in a set `D` whose closure contains the
compact set `B`, then `g n → g₀` uniformly on `B`. -/
theorem tendstoUniformlyOn_of_lipschitz {X : Type*} [PseudoMetricSpace X] {B D : Set X}
    (hB : IsCompact B) (hBD : B ⊆ closure D) (g : ℕ → X → ℝ) (g₀ : X → ℝ)
    (hg : ∀ n x y, |g n x - g n y| ≤ dist x y) (hg₀ : ∀ x y, |g₀ x - g₀ y| ≤ dist x y)
    (hconv : ∀ x ∈ D, Tendsto (fun n => g n x) atTop (𝓝 (g₀ x))) :
    TendstoUniformlyOn g g₀ atTop B := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  -- a finite ε/3-net of `B` with centres in `D`
  obtain ⟨F, hF⟩ := hB.elim_finite_subcover (fun d : D => Metric.ball (d : X) (ε / 3))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      obtain ⟨d, hdD, hxd⟩ := Metric.mem_closure_iff.1 (hBD hx) (ε / 3) hε3
      exact Set.mem_iUnion.2 ⟨⟨d, hdD⟩, Metric.mem_ball.2 hxd⟩)
  have hev : ∀ᶠ n in atTop, ∀ d ∈ F, |g n (d : X) - g₀ d| < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro d _
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv d d.2) (ε / 3) hε3
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have h := hN n hn
    rwa [Real.dist_eq] at h
  filter_upwards [hev] with n hn x hx
  obtain ⟨d, hdF, hxd₀⟩ := Set.mem_iUnion₂.1 (hF hx)
  have hxd : dist x d < ε / 3 := Metric.mem_ball.1 hxd₀
  have h1 := hg n x d
  have h2 := hn d hdF
  have h3 := hg₀ d x
  rw [dist_comm] at h3
  rw [Real.dist_eq]
  have t1 := abs_sub_le (g₀ x) (g₀ d) (g n x)
  have t2 := abs_sub_le (g₀ d) (g n d) (g n x)
  have e1 : |g₀ x - g₀ d| = |g₀ d - g₀ x| := abs_sub_comm _ _
  have e2 : |g₀ d - g n d| = |g n d - g₀ d| := abs_sub_comm _ _
  have e3 : |g n d - g n x| = |g n x - g n d| := abs_sub_comm _ _
  linarith

/-- **Step 4, almost-sure form.**  Countably many probability-one events, one for each
point of a countable set `D` dense in the compact set `B`, give uniform convergence on
`B` almost surely. -/
theorem ae_tendstoUniformlyOn_of_lipschitz {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Type*} [PseudoMetricSpace X] {B D : Set X} (hB : IsCompact B) (hDc : D.Countable)
    (hBD : B ⊆ closure D) (g : ℕ → X → Ω → ℝ) (g₀ : X → ℝ)
    (hg : ∀ n x y ω, |g n x ω - g n y ω| ≤ dist x y)
    (hg₀ : ∀ x y, |g₀ x - g₀ y| ≤ dist x y)
    (hconv : ∀ x ∈ D, ∀ᵐ ω ∂μ, Tendsto (fun n => g n x ω) atTop (𝓝 (g₀ x))) :
    ∀ᵐ ω ∂μ, TendstoUniformlyOn (fun n x => g n x ω) g₀ atTop B := by
  have h := (ae_ball_iff hDc).2 hconv
  filter_upwards [h] with ω hω
  exact tendstoUniformlyOn_of_lipschitz hB hBD (fun n x => g n x ω) g₀
    (fun n x y => hg n x y ω) hg₀ hω

end OutputSpace

end BernoulliEdge

end

#print axioms BernoulliEdge.bernoulli_edge_duality
#print axioms BernoulliEdge.random_compression
#print axioms BernoulliEdge.support_limit_diag
#print axioms BernoulliEdge.ae_tendstoUniformlyOn_of_lipschitz
