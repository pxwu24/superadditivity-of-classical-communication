import Entropy.Defs

open Real Finset
noncomputable section
namespace AppendixB

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
      · exact Finset.insert_subset hx (fun a ha => Finset.mem_of_mem_erase (hJs ha))
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

lemma sum_mem_eq_ite {k : ℕ} (I : Finset (Fin k)) (f : Fin k → ℝ) :
    ∑ i ∈ I, f i = ∑ i, if i ∈ I then f i else 0 := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- `∑_I ∑_{i∈I} f_i = C(k-1, r) ∑_i f_i` over the `(r+1)`-subsets. -/
lemma sum_over_subsets {k : ℕ} (r : ℕ) (f : Fin k → ℝ) :
    ∑ I ∈ subsets k (r + 1), ∑ i ∈ I, f i = ((k - 1).choose r : ℝ) * ∑ i, f i := by
  have hrepr : (∑ I ∈ subsets k (r + 1), ∑ i ∈ I, f i)
      = ∑ I ∈ subsets k (r + 1), ∑ i, if i ∈ I then f i else 0 := by
    exact Finset.sum_congr rfl (fun I _ => sum_mem_eq_ite I f)
  rw [hrepr, Finset.sum_comm, Finset.mul_sum]
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
    rw [sum_mem_eq_ite I ε, mul_neg, Finset.sum_mul_sum]
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
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsum : ∑ i ∈ I, ((k : ℝ) * q i - 1) = k * ∑ i ∈ I, q i - r := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hI, nsmul_eq_mul, mul_one]
  simp only [shuffle]
  rw [hsum]
  have e : 1 + ((k : ℝ) * ∑ i ∈ I, q i - r) / r = (k : ℝ) * (∑ i ∈ I, q i) / r := by
    field_simp
  rw [e, div_div, ← h1]
  field_simp
  ring

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

end AppendixB
end
