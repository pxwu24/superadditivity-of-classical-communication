import StrongConvergence.StrongConvergenceHaarPairMoments
import StrongConvergence.StrongConvergenceHaarVariance
import StrongConvergence.StrongConvergenceVarianceAlgebra

/-! Exact variance identities for the diagonal of a genuine Haar unitary orbit. -/
open Matrix MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.HaarMoment
variable {E : Type*} [Fintype E] [DecidableEq E]

lemma continuous_weighted_diagonal_square (P : Matrix E E ℂ) (w : E → ℝ) :
    Continuous (fun U : Matrix.unitaryGroup E ℂ =>
      (∑ l, w l * ((orbit P U l l).re - (Matrix.trace P).re / Fintype.card E))^2) :=
  (continuous_finset_sum Finset.univ (fun l _ =>
    continuous_const.mul ((continuous_orbit_diag P l).sub continuous_const))).pow 2

lemma integrable_weighted_diagonal_square (P : Matrix E E ℂ) (w : E → ℝ) :
    Integrable (fun U : Matrix.unitaryGroup E ℂ =>
      (∑ l, w l * ((orbit P U l l).re - (Matrix.trace P).re / Fintype.card E))^2)
        HaarProjection.unitaryHaar :=
  (continuous_weighted_diagonal_square P w).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma weighted_diagonal_centering (P : Matrix E E ℂ) (w : E → ℝ)
    (U : Matrix.unitaryGroup E ℂ) :
    (∑ l, w l * ((orbit P U l l).re - (Matrix.trace P).re / Fintype.card E)) =
      (∑ l, w l * (orbit P U l l).re) -
        (Matrix.trace P).re / Fintype.card E * ∑ l, w l := by
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

lemma diagSecond_sub_diagCross_of_rotation {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    {i j : E} (hij : i ≠ j)
    (hrotation : diagSecond P i = diagCross P i j + entrySecond P i j) :
    diagSecond P i - diagCross P i j =
      (Matrix.trace P).re * ((Fintype.card E : ℝ) - (Matrix.trace P).re) /
        ((Fintype.card E : ℝ) * ((Fintype.card E : ℝ)^2 - 1)) := by
  exact HaarVarianceAlgebra.second_moment_difference _ _ _ _ _
    (by exact_mod_cast hN) hrotation
    (second_moment_projection_trace hP hPP i j hij)
    (second_moment_trace_square P i j hij)

lemma weighted_diagonal_variance_moments [Nonempty E] (P : Matrix E E ℂ)
    (w : E → ℝ) {i j : E} (hij : i ≠ j) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (∑ l, w l * ((orbit P U l l).re - (Matrix.trace P).re / Fintype.card E))^2
        ∂HaarProjection.unitaryHaar) =
    (diagSecond P i - diagCross P i j) *
      ((∑ l, (w l)^2) - (∑ l, w l)^2 / Fintype.card E) := by
  let m : ℝ := (Matrix.trace P).re / Fintype.card E
  have hN : (Fintype.card E : ℝ) ≠ 0 := by positivity
  have hrow : diagSecond P i + ((Fintype.card E : ℝ)-1)*diagCross P i j =
      Fintype.card E * m^2 := by
    have h := second_moment_trace_square P i j hij
    dsimp [m]
    field_simp
    nlinarith [h]
  apply HaarVarianceAlgebra.centered_weighted_variance
    (fun U l => (orbit P U l l).re) w m (diagSecond P i) (diagCross P i j)
    (integrable_orbit_diag P) (integrable_diagCross P) (integral_orbit_diag P)
    _ _ hrow
  · intro l
    change diagCross P l l = diagSecond P i
    rw [diagCross_self, diagSecond_eq P l i]
  · intro l m hlm
    exact diagCross_eq P hlm hij

lemma weighted_diagonal_variance_le_moments [Nonempty E]
    (P : Matrix E E ℂ) (w : E → ℝ) {i j : E} (hij : i ≠ j)
    (hcoeff : 0 ≤ diagSecond P i - diagCross P i j) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (∑ l, w l * ((orbit P U l l).re - (Matrix.trace P).re / Fintype.card E))^2
        ∂HaarProjection.unitaryHaar) ≤
    (diagSecond P i - diagCross P i j) * ∑ l, (w l)^2 := by
  rw [weighted_diagonal_variance_moments P w hij]
  apply mul_le_mul_of_nonneg_left _ hcoeff
  apply sub_le_self
  positivity

lemma weighted_diagonal_variance_of_rotation {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    (w : E → ℝ) {i j : E} (hij : i ≠ j)
    (hrotation : diagSecond P i = diagCross P i j + entrySecond P i j) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (∑ l, w l * ((orbit P U l l).re - (Matrix.trace P).re / Fintype.card E))^2
        ∂HaarProjection.unitaryHaar) =
    ((Matrix.trace P).re * ((Fintype.card E : ℝ) - (Matrix.trace P).re) /
      ((Fintype.card E : ℝ) * ((Fintype.card E : ℝ)^2 - 1))) *
      ((∑ l, (w l)^2) - (∑ l, w l)^2 / Fintype.card E) := by
  letI : Nonempty E := ⟨i⟩
  rw [weighted_diagonal_variance_moments P w hij,
    diagSecond_sub_diagCross_of_rotation hP hPP hN hij hrotation]

lemma weighted_diagonal_variance_le_of_rotation {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    (w : E → ℝ) {i j : E} (hij : i ≠ j)
    (hrotation : diagSecond P i = diagCross P i j + entrySecond P i j) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (∑ l, w l * ((orbit P U l l).re - (Matrix.trace P).re / Fintype.card E))^2
        ∂HaarProjection.unitaryHaar) ≤ (1 / (Fintype.card E : ℝ)) * ∑ l, (w l)^2 := by
  letI : Nonempty E := ⟨i⟩
  have hcoeff : 0 ≤ diagSecond P i - diagCross P i j := by
    rw [hrotation]
    simp only [add_sub_cancel_left]
    exact integral_nonneg (fun U => Complex.normSq_nonneg _)
  have hle := weighted_diagonal_variance_le_moments P w hij hcoeff
  apply hle.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun l _ => sq_nonneg _))
  rw [diagSecond_sub_diagCross_of_rotation hP hPP hN hij hrotation]
  apply HaarVarianceAlgebra.haar_variance_coefficient_le_inv
  exact_mod_cast hN

/-- The exact covariance coefficient of a Haar-random orthogonal projection. -/
theorem diagSecond_sub_diagCross {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    {i j : E} (hij : i ≠ j) :
    diagSecond P i - diagCross P i j =
      (Matrix.trace P).re * ((Fintype.card E : ℝ) - (Matrix.trace P).re) /
        ((Fintype.card E : ℝ) * ((Fintype.card E : ℝ)^2 - 1)) :=
  diagSecond_sub_diagCross_of_rotation hP hPP hN hij
    (diagSecond_eq_diagCross_add_entrySecond hP hij)

/-- The common off-diagonal squared-modulus moment. -/
theorem entrySecond_eq_formula {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    {i j : E} (hij : i ≠ j) :
    entrySecond P i j =
      (Matrix.trace P).re * ((Fintype.card E : ℝ) - (Matrix.trace P).re) /
        ((Fintype.card E : ℝ) * ((Fintype.card E : ℝ)^2 - 1)) := by
  have h := diagSecond_sub_diagCross hP hPP hN hij
  have hr := diagSecond_eq_diagCross_add_entrySecond hP hij
  linarith

/-- The common moment of two distinct diagonal entries. -/
theorem diagCross_eq_formula {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    {i j : E} (hij : i ≠ j) :
    diagCross P i j =
      (Matrix.trace P).re * ((Fintype.card E : ℝ) * (Matrix.trace P).re - 1) /
        ((Fintype.card E : ℝ) * ((Fintype.card E : ℝ)^2 - 1)) := by
  let N : ℝ := Fintype.card E
  let d : ℝ := (Matrix.trace P).re
  have hN1 : 1 < N := by dsimp [N]; exact_mod_cast hN
  have hN0 : N ≠ 0 := by linarith
  have hden : N * (N^2-1) ≠ 0 := by nlinarith
  have hd := diagSecond_sub_diagCross hP hPP hN hij
  change diagSecond P i - diagCross P i j = d*(N-d)/(N*(N^2-1)) at hd
  have hd' := (eq_div_iff hden).mp hd
  have ht := second_moment_trace_square P i j hij
  change N * diagSecond P i + N*(N-1)*diagCross P i j = d^2 at ht
  change diagCross P i j = d*(N*d-1)/(N*(N^2-1))
  apply (eq_div_iff hden).mpr
  apply (mul_left_cancel₀ hN0)
  linear_combination (N^2-1)*ht - hd'

/-- The common square moment of a diagonal entry. -/
theorem diagSecond_eq_formula {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    (i : E) :
    diagSecond P i =
      (Matrix.trace P).re * ((Matrix.trace P).re + 1) /
        ((Fintype.card E : ℝ) * ((Fintype.card E : ℝ) + 1)) := by
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hN i
  have hij := Ne.symm hji
  rw [diagSecond_eq_diagCross_add_entrySecond hP hij,
    diagCross_eq_formula hP hPP hN hij, entrySecond_eq_formula hP hPP hN hij]
  have hN1 : (1:ℝ) < Fintype.card E := by exact_mod_cast hN
  have hN0 : (Fintype.card E : ℝ) ≠ 0 := by linarith
  have hm : (Fintype.card E : ℝ)-1 ≠ 0 := by linarith
  have hp : (Fintype.card E : ℝ)+1 ≠ 0 := by linarith
  have hf : (Fintype.card E : ℝ)^2-1 =
      ((Fintype.card E : ℝ)-1)*((Fintype.card E : ℝ)+1) := by ring
  rw [hf]
  field_simp
  ring

/-- Exact variance for an arbitrary real weighted sum of projection diagonal entries. -/
theorem weighted_diagonal_variance {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    (w : E → ℝ) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (∑ l, w l * ((orbit P U l l).re - (Matrix.trace P).re / Fintype.card E))^2
        ∂HaarProjection.unitaryHaar) =
    ((Matrix.trace P).re * ((Fintype.card E : ℝ) - (Matrix.trace P).re) /
      ((Fintype.card E : ℝ) * ((Fintype.card E : ℝ)^2 - 1))) *
      ((∑ l, (w l)^2) - (∑ l, w l)^2 / Fintype.card E) := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hN
  exact weighted_diagonal_variance_of_rotation hP hPP hN w hij
    (diagSecond_eq_diagCross_add_entrySecond hP hij)

/-- A uniform finite-dimensional variance bound, with no asymptotic hypothesis. -/
theorem weighted_diagonal_variance_le {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    (w : E → ℝ) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (∑ l, w l * ((orbit P U l l).re - (Matrix.trace P).re / Fintype.card E))^2
        ∂HaarProjection.unitaryHaar) ≤ (1 / (Fintype.card E : ℝ)) * ∑ l, (w l)^2 := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hN
  exact weighted_diagonal_variance_le_of_rotation hP hPP hN w hij
    (diagSecond_eq_diagCross_add_entrySecond hP hij)

/-- The same bound written as a centered weighted trace. -/
theorem weighted_diagonal_variance_centered_le {P : Matrix E E ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hN : 1 < Fintype.card E)
    (w : E → ℝ) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      ((∑ l, w l * (orbit P U l l).re) -
        (Matrix.trace P).re / Fintype.card E * ∑ l, w l)^2
        ∂HaarProjection.unitaryHaar) ≤ (1 / (Fintype.card E : ℝ)) * ∑ l, (w l)^2 := by
  simpa only [weighted_diagonal_centering] using weighted_diagonal_variance_le hP hPP hN w

end ProjectionChannels.HaarMoment

#print axioms ProjectionChannels.HaarMoment.diagSecond_sub_diagCross
#print axioms ProjectionChannels.HaarMoment.weighted_diagonal_variance
#print axioms ProjectionChannels.HaarMoment.weighted_diagonal_variance_le

#print axioms ProjectionChannels.HaarMoment.entrySecond_eq_formula
#print axioms ProjectionChannels.HaarMoment.diagCross_eq_formula
#print axioms ProjectionChannels.HaarMoment.diagSecond_eq_formula
