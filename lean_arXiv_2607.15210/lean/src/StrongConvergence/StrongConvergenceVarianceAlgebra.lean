import StrongConvergence.StrongConvergenceHaarMoment

/-! Finite-sum and integral algebra for the variance of exchangeable diagonal
entries.  This file derives consequences of explicitly supplied moments; the
Haar moment identities themselves are proved separately. -/

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace ProjectionChannels.HaarVarianceAlgebra

variable {E Ω : Type*} [Fintype E] [DecidableEq E]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma exchangeable_quadratic (w : E → ℝ) (a b : ℝ) :
    (∑ i, ∑ j, w i * w j * (if i = j then a else b)) =
      (a-b) * ∑ i, (w i)^2 + b * (∑ i, w i)^2 := by
  have h (i j : E) : w i * w j * (if i = j then a else b) =
      (if i = j then (a-b) * (w i)^2 else 0) + b * w i * w j := by
    split_ifs with hij
    · subst j; ring
    · ring
  simp_rw [h, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.mul_sum]
  ring

omit [Fintype E] [DecidableEq E] in
lemma integrable_centered_product (x : Ω → E → ℝ) (m : ℝ)
    (hx : ∀ i, Integrable (fun ω => x ω i) μ)
    (hxx : ∀ i j, Integrable (fun ω => x ω i * x ω j) μ) (i j : E) :
    Integrable (fun ω => (x ω i-m) * (x ω j-m)) μ := by
  have h := (((hxx i j).sub ((hx i).mul_const m)).sub
    ((hx j).const_mul m)).add (integrable_const (m*m))
  convert h using 1
  ext ω
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

omit [Fintype E] [DecidableEq E] in
lemma integral_centered_product (x : Ω → E → ℝ) (m : ℝ)
    (hx : ∀ i, Integrable (fun ω => x ω i) μ)
    (hxx : ∀ i j, Integrable (fun ω => x ω i * x ω j) μ)
    (hmean : ∀ i, (∫ ω, x ω i ∂μ) = m) (i j : E) :
    (∫ ω, (x ω i-m) * (x ω j-m) ∂μ) =
      (∫ ω, x ω i * x ω j ∂μ) - m^2 := by
  have h (ω : Ω) : (x ω i-m) * (x ω j-m) =
      ((x ω i*x ω j - x ω i*m) - m*x ω j) + m*m := by ring
  simp_rw [h]
  have h1 : Integrable (fun ω => x ω i*x ω j - x ω i*m) μ :=
    (hxx i j).sub ((hx i).mul_const m)
  have h2 : Integrable (fun ω => x ω i*x ω j - x ω i*m - m*x ω j) μ :=
    h1.sub ((hx j).const_mul m)
  rw [integral_add h2 (integrable_const (m*m)),
    integral_sub h1 ((hx j).const_mul m),
    integral_sub (hxx i j) ((hx i).mul_const m)]
  simp [integral_mul_const, integral_const_mul, hmean]
  ring

omit [DecidableEq E] [IsProbabilityMeasure μ] in
lemma integral_weighted_square (x : Ω → E → ℝ) (w : E → ℝ)
    (hxx : ∀ i j, Integrable (fun ω => x ω i * x ω j) μ) :
    (∫ ω, (∑ i, w i * x ω i)^2 ∂μ) =
      ∑ i, ∑ j, w i * w j * ∫ ω, x ω i * x ω j ∂μ := by
  have h (ω : Ω) : (∑ i, w i * x ω i)^2 =
      ∑ i, ∑ j, (w i*w j) * (x ω i*x ω j) := by
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [h]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro j _; exact (hxx i j).const_mul _
  · intro i _
    exact integrable_finset_sum _ (fun j _ => (hxx i j).const_mul _)

theorem centered_weighted_variance [Nonempty E] (x : Ω → E → ℝ)
    (w : E → ℝ) (m α β : ℝ)
    (hx : ∀ i, Integrable (fun ω => x ω i) μ)
    (hxx : ∀ i j, Integrable (fun ω => x ω i * x ω j) μ)
    (hmean : ∀ i, (∫ ω, x ω i ∂μ) = m)
    (hdiag : ∀ i, (∫ ω, x ω i * x ω i ∂μ) = α)
    (hoff : ∀ i j, i ≠ j → (∫ ω, x ω i * x ω j ∂μ) = β)
    (hrow : α + (Fintype.card E-1 : ℝ)*β = Fintype.card E*m^2) :
    (∫ ω, (∑ i, w i * (x ω i-m))^2 ∂μ) =
      (α-β) * ((∑ i, (w i)^2) - (∑ i, w i)^2 / Fintype.card E) := by
  rw [integral_weighted_square (fun ω i => x ω i-m) w
    (integrable_centered_product x m hx hxx)]
  simp_rw [integral_centered_product x m hx hxx hmean]
  have hmom (i j : E) : (∫ ω, x ω i*x ω j ∂μ)-m^2 =
      if i=j then α-m^2 else β-m^2 := by
    by_cases h : i=j
    · subst j; simp [hdiag]
    · simp [h, hoff i j h]
  simp_rw [hmom]
  rw [exchangeable_quadratic]
  have hN : (Fintype.card E : ℝ) ≠ 0 := by positivity
  have hb : β-m^2 = -(α-β) / Fintype.card E := by
    apply (eq_div_iff hN).mpr
    nlinarith [hrow]
  have hdiff : (α-m^2)-(β-m^2) = α-β := by ring
  rw [hdiff, hb]
  field_simp
  ring

theorem centered_weighted_variance_le [Nonempty E] (x : Ω → E → ℝ)
    (w : E → ℝ) (m α β : ℝ)
    (hx : ∀ i, Integrable (fun ω => x ω i) μ)
    (hxx : ∀ i j, Integrable (fun ω => x ω i * x ω j) μ)
    (hmean : ∀ i, (∫ ω, x ω i ∂μ) = m)
    (hdiag : ∀ i, (∫ ω, x ω i * x ω i ∂μ) = α)
    (hoff : ∀ i j, i ≠ j → (∫ ω, x ω i * x ω j ∂μ) = β)
    (hrow : α + (Fintype.card E-1 : ℝ)*β = Fintype.card E*m^2)
    (hcoeff : 0 ≤ α-β) :
    (∫ ω, (∑ i, w i * (x ω i-m))^2 ∂μ) ≤ (α-β) * ∑ i, (w i)^2 := by
  rw [centered_weighted_variance x w m α β hx hxx hmean hdiag hoff hrow]
  apply mul_le_mul_of_nonneg_left _ hcoeff
  apply sub_le_self
  positivity

theorem second_moment_difference (N d α β γ : ℝ) (hN : 1 < N)
    (hrotation : α = β+γ)
    (hprojection : N*α + N*(N-1)*γ = d)
    (htrace : N*α + N*(N-1)*β = d^2) :
    α-β = d*(N-d)/(N*(N^2-1)) := by
  have hden : N*(N^2-1) ≠ 0 := by
    have : 0 < N*(N^2-1) := by nlinarith
    exact ne_of_gt this
  apply (eq_div_iff hden).mpr
  linear_combination N*hprojection - htrace + (N^2*(N-1))*hrotation

omit [IsProbabilityMeasure μ] in
lemma row_identity_of_fixed_sum [Nonempty E] (x : Ω → E → ℝ)
    (m α β : ℝ)
    (hxx : ∀ i j, Integrable (fun ω => x ω i * x ω j) μ)
    (hmean : ∀ i, (∫ ω, x ω i ∂μ) = m)
    (hdiag : ∀ i, (∫ ω, x ω i * x ω i ∂μ) = α)
    (hoff : ∀ i j, i ≠ j → (∫ ω, x ω i * x ω j ∂μ) = β)
    (hsum : ∀ ω, ∑ i, x ω i = Fintype.card E*m) :
    α + (Fintype.card E-1 : ℝ)*β = Fintype.card E*m^2 := by
  obtain ⟨i⟩ := ‹Nonempty E›
  have hmom (j : E) : (∫ ω, x ω i*x ω j ∂μ) =
      β + if i=j then α-β else 0 := by
    by_cases h : i=j
    · subst j; simp [hdiag]
    · simp [h, hoff i j h]
  have hpoint (ω : Ω) : (∑ j, x ω i*x ω j) =
      x ω i * (Fintype.card E*m) := by rw [← Finset.mul_sum, hsum]
  calc
    α + (Fintype.card E-1 : ℝ)*β =
        ∑ j, ∫ ω, x ω i*x ω j ∂μ := by
      simp_rw [hmom, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    _ = ∫ ω, ∑ j, x ω i*x ω j ∂μ :=
      (integral_finset_sum _ (fun j _ => hxx i j)).symm
    _ = _ := by simp_rw [hpoint]; rw [integral_mul_const, hmean]; ring

lemma row_identity_of_trace_square (N d α β : ℝ) (hN : N ≠ 0)
    (htrace : N*α + N*(N-1)*β = d^2) :
    α + (N-1)*β = N*(d/N)^2 := by
  calc
    α + (N-1)*β = d^2/N := by
      apply (eq_div_iff hN).mpr
      nlinarith [htrace]
    _ = _ := by field_simp; ring

lemma haar_variance_coefficient_nonneg (N d : ℝ) (hN : 1 < N)
    (hd0 : 0 ≤ d) (hdN : d ≤ N) :
    0 ≤ d*(N-d)/(N*(N^2-1)) := by
  apply div_nonneg
  · exact mul_nonneg hd0 (sub_nonneg.mpr hdN)
  · have : 0 < N*(N^2-1) := by nlinarith
    exact le_of_lt this

lemma haar_variance_coefficient_le_inv (N d : ℝ) (hN : 2 ≤ N) :
    d*(N-d)/(N*(N^2-1)) ≤ 1/N := by
  have hN0 : 0 < N := by linarith
  have hden : 0 < N*(N^2-1) := by nlinarith
  apply (div_le_iff₀ hden).mpr
  have hcancel : 1/N*(N*(N^2-1)) = N^2-1 := by
    field_simp
  rw [hcancel]
  nlinarith [sq_nonneg (2*d-N), sq_nonneg (N-2)]

end ProjectionChannels.HaarVarianceAlgebra

#print axioms ProjectionChannels.HaarVarianceAlgebra.centered_weighted_variance
#print axioms ProjectionChannels.HaarVarianceAlgebra.second_moment_difference
