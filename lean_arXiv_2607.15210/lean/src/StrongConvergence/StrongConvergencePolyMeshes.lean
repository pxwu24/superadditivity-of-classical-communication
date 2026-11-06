import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-! Arithmetic meshes for the two polynomial interpolation variables: rank
density `d/N` and reciprocal dimensions constrained to be multiples of `k`. -/

open Set

namespace ProjectionChannels.PolyChebyshev

/-- Rank densities with denominator `N` form a mesh of width `1/N` in `[0,1]`. -/
theorem rank_grid_mesh (N : ℕ) (hN : 0 < N)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ d : ℕ, d ≤ N ∧ |x - (d : ℝ) / N| ≤ 1 / N := by
  let d := Nat.floor (x * N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod : 0 ≤ x * (N : ℝ) := mul_nonneg hx.1 hNr.le
  have hdle : d ≤ N := Nat.floor_le_of_le (by nlinarith [hx.2])
  have hlow : (d : ℝ) ≤ x * N := Nat.floor_le hprod
  have hupp : x * N < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsmall : (d : ℝ) / N ≤ x := (div_le_iff₀ hNr).mpr hlow
  refine ⟨d, hdle, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hsmall), le_div_iff₀ hNr]
  have hcancel : (d : ℝ) / N * N = d := div_mul_cancel₀ _ hNr.ne'
  nlinarith

/-- Reciprocal multiples of `k`, restricted to dimensions at least `N₀`,
form a mesh of width `k/N₀²`, including at the endpoint zero. -/
theorem reciprocal_grid_mesh (k N₀ : ℕ) (hk : 0 < k) (hN₀ : 0 < N₀)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / N₀)) :
    ∃ N : ℕ, k ∣ N ∧ N₀ ≤ N ∧ |x - 1 / (N : ℝ)| ≤ (k : ℝ) / (N₀ : ℝ) ^ 2 := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hN₀r : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  by_cases hx0 : x = 0
  · let N := k * N₀ ^ 2
    have hNN₀ : N₀ ≤ N := by dsimp [N]; nlinarith [Nat.one_le_iff_ne_zero.mpr hk.ne', Nat.one_le_iff_ne_zero.mpr hN₀.ne']
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN₀.trans_le hNN₀
    refine ⟨N, ⟨N₀ ^ 2, rfl⟩, hNN₀, ?_⟩
    rw [hx0, zero_sub, abs_neg, abs_of_pos (one_div_pos.mpr hNr)]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [N]
    push_cast
    apply (div_le_div_iff₀ (mul_pos hkr (sq_pos_of_pos hN₀r)) (sq_pos_of_pos hN₀r)).mpr
    nlinarith [sq_nonneg (k - 1 : ℝ), sq_pos_of_pos hN₀r]
  · have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    let d := Nat.ceil (1 / ((k : ℝ) * x))
    let N := k * d
    have hkx : 0 < (k : ℝ) * x := mul_pos hkr hxp
    have hdp : 0 < d := Nat.ceil_pos.mpr (one_div_pos.mpr hkx)
    have hNp : 0 < N := Nat.mul_pos hk hdp
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
    have hdl : 1 / ((k : ℝ) * x) ≤ (d : ℝ) := Nat.le_ceil _
    have hdu : (d : ℝ) < 1 / ((k : ℝ) * x) + 1 :=
      Nat.ceil_lt_add_one (one_div_nonneg.mpr hkx.le)
    have hcancel : (1 / ((k : ℝ) * x)) * ((k : ℝ) * x) = 1 :=
      one_div_mul_cancel hkx.ne'
    have hlow : 1 ≤ (N : ℝ) * x := by
      have h := mul_le_mul_of_nonneg_right hdl hkx.le
      dsimp [N]
      push_cast
      nlinarith
    have hupp : (N : ℝ) * x < 1 + (k : ℝ) * x := by
      have h := mul_lt_mul_of_pos_right hdu hkx
      dsimp [N]
      push_cast
      nlinarith
    have hNN₀ : N₀ ≤ N := by
      have hprod := mul_le_mul_of_nonneg_left hx.2 hNr.le
      have hdiv : 1 ≤ (N : ℝ) / N₀ :=
        hlow.trans (by simpa only [div_eq_mul_inv, one_mul] using hprod)
      exact_mod_cast (one_le_div₀ hN₀r).mp hdiv
    have hsmall : 1 / (N : ℝ) ≤ x := (div_le_iff₀ hNr).mpr (by nlinarith [hlow])
    refine ⟨N, ⟨d, rfl⟩, hNN₀, ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hsmall)]
    have hstep : x - 1 / (N : ℝ) ≤ (k : ℝ) * x ^ 2 := by
      have hfac := mul_le_mul_of_nonneg_left hlow hkx.le
      have hcancelN : (1 / (N : ℝ)) * N = 1 := one_div_mul_cancel hNr.ne'
      apply (mul_le_mul_iff_of_pos_right hNr).mp
      nlinarith
    calc
      _ ≤ (k : ℝ) * x ^ 2 := hstep
      _ ≤ (k : ℝ) * (1 / (N₀ : ℝ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hkr.le
        nlinarith [mul_self_le_mul_self hx.1 hx.2]
      _ = (k : ℝ) / (N₀ : ℝ) ^ 2 := by field_simp

#print axioms rank_grid_mesh
#print axioms reciprocal_grid_mesh

end ProjectionChannels.PolyChebyshev
