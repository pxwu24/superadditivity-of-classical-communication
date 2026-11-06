import StrongConvergence.StrongConvergenceHaarMoment

open Matrix MeasureTheory
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.HaarMoment
variable {E : Type*} [Fintype E] [DecidableEq E]

def diagSecond (P : Matrix E E ℂ) (i : E) : ℝ :=
  ∫ U : Matrix.unitaryGroup E ℂ, (orbit P U i i).re ^ 2 ∂HaarProjection.unitaryHaar

def diagCross (P : Matrix E E ℂ) (i j : E) : ℝ :=
  ∫ U : Matrix.unitaryGroup E ℂ,
    (orbit P U i i).re * (orbit P U j j).re ∂HaarProjection.unitaryHaar

def entrySecond (P : Matrix E E ℂ) (i j : E) : ℝ :=
  ∫ U : Matrix.unitaryGroup E ℂ,
    Complex.normSq (orbit P U i j) ∂HaarProjection.unitaryHaar

lemma continuous_orbit_entry (P : Matrix E E ℂ) (i j : E) :
    Continuous (fun U : Matrix.unitaryGroup E ℂ => orbit P U i j) :=
  (HaarProjection.continuous_unitary_orbit P).matrix_elem i j

lemma integrable_diagSecond (P : Matrix E E ℂ) (i : E) :
    Integrable (fun U : Matrix.unitaryGroup E ℂ => (orbit P U i i).re ^ 2)
      HaarProjection.unitaryHaar :=
  ((continuous_orbit_diag P i).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integrable_diagCross (P : Matrix E E ℂ) (i j : E) :
    Integrable (fun U : Matrix.unitaryGroup E ℂ =>
      (orbit P U i i).re * (orbit P U j j).re) HaarProjection.unitaryHaar :=
  ((continuous_orbit_diag P i).mul (continuous_orbit_diag P j)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integrable_entrySecond (P : Matrix E E ℂ) (i j : E) :
    Integrable (fun U : Matrix.unitaryGroup E ℂ => Complex.normSq (orbit P U i j))
      HaarProjection.unitaryHaar :=
  (Complex.continuous_normSq.comp (continuous_orbit_entry P i j)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma orbit_permutation (P : Matrix E E ℂ) (e : Equiv.Perm E)
    (U : Matrix.unitaryGroup E ℂ) (i j : E) :
    orbit P (star (ProjectionOrbit.permuteColumns (1 : Matrix.unitaryGroup E ℂ) e) * U) i j
      = orbit P U (e i) (e j) := by
  have h := ProjectionOrbit.permuteColumns_diagonalization
    (1 : Matrix.unitaryGroup E ℂ) e (orbit P U)
  have hi := congrFun (congrFun h i) j
  simpa [orbit, Matrix.UnitaryGroup.mul_val, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.mul_assoc] using hi

lemma diagSecond_permutation (P : Matrix E E ℂ) (e : Equiv.Perm E) (i : E) :
    diagSecond P i = diagSecond P (e i) := by
  have h := integral_mul_left_eq_self (μ := HaarProjection.unitaryHaar)
    (fun U : Matrix.unitaryGroup E ℂ => (orbit P U i i).re ^ 2)
    (star (ProjectionOrbit.permuteColumns (1 : Matrix.unitaryGroup E ℂ) e))
  simpa only [diagSecond, orbit_permutation] using h.symm

lemma diagCross_permutation (P : Matrix E E ℂ) (e : Equiv.Perm E) (i j : E) :
    diagCross P i j = diagCross P (e i) (e j) := by
  have h := integral_mul_left_eq_self (μ := HaarProjection.unitaryHaar)
    (fun U : Matrix.unitaryGroup E ℂ => (orbit P U i i).re * (orbit P U j j).re)
    (star (ProjectionOrbit.permuteColumns (1 : Matrix.unitaryGroup E ℂ) e))
  simpa only [diagCross, orbit_permutation] using h.symm

lemma entrySecond_permutation (P : Matrix E E ℂ) (e : Equiv.Perm E) (i j : E) :
    entrySecond P i j = entrySecond P (e i) (e j) := by
  have h := integral_mul_left_eq_self (μ := HaarProjection.unitaryHaar)
    (fun U : Matrix.unitaryGroup E ℂ => Complex.normSq (orbit P U i j))
    (star (ProjectionOrbit.permuteColumns (1 : Matrix.unitaryGroup E ℂ) e))
  simpa only [entrySecond, orbit_permutation] using h.symm

omit [Fintype E] in
lemma exists_permutation_pair {i j l m : E} (hij : i ≠ j) (hlm : l ≠ m) :
    ∃ e : Equiv.Perm E, e i = l ∧ e j = m := by
  let e₁ := Equiv.swap i l
  have hj : e₁ j ≠ l := by
    have hi : e₁ i = l := by simp [e₁]
    intro h
    exact hij (e₁.injective (hi.trans h.symm))
  refine ⟨e₁.trans (Equiv.swap (e₁ j) m), ?_, ?_⟩
  · simp only [Equiv.trans_apply, e₁, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hj) hlm
  · simp

lemma diagSecond_eq (P : Matrix E E ℂ) (i j : E) :
    diagSecond P i = diagSecond P j := by
  simpa using diagSecond_permutation P (Equiv.swap i j) i

lemma diagCross_eq (P : Matrix E E ℂ) {i j l m : E} (hij : i ≠ j) (hlm : l ≠ m) :
    diagCross P i j = diagCross P l m := by
  obtain ⟨e, hi, hj⟩ := exists_permutation_pair hij hlm
  simpa [hi, hj] using diagCross_permutation P e i j

lemma entrySecond_eq (P : Matrix E E ℂ) {i j l m : E} (hij : i ≠ j) (hlm : l ≠ m) :
    entrySecond P i j = entrySecond P l m := by
  obtain ⟨e, hi, hj⟩ := exists_permutation_pair hij hlm
  simpa [hi, hj] using entrySecond_permutation P e i j

lemma orbit_isHermitian {P : Matrix E E ℂ} (hP : P.IsHermitian)
    (U : Matrix.unitaryGroup E ℂ) : (orbit P U).IsHermitian := by
  dsimp [Matrix.IsHermitian, orbit] at *
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

lemma orbit_idempotent {P : Matrix E E ℂ} (hP : P * P = P)
    (U : Matrix.unitaryGroup E ℂ) : orbit P U * orbit P U = orbit P U := by
  have hU : (U : Matrix E E ℂ).conjTranspose * (U : Matrix E E ℂ) = 1 := U.prop.1
  dsimp [orbit]
  calc
    _ = (U : Matrix E E ℂ) * (P * ((U : Matrix E E ℂ).conjTranspose * U) * P) *
        (U : Matrix E E ℂ).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, hP]

lemma orbit_trace (P : Matrix E E ℂ) (U : Matrix.unitaryGroup E ℂ) :
    Matrix.trace (orbit P U) = Matrix.trace P := by
  have hU : (U : Matrix E E ℂ).conjTranspose * (U : Matrix E E ℂ) = 1 := U.prop.1
  rw [orbit, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

lemma diagCross_self (P : Matrix E E ℂ) (i : E) :
    diagCross P i i = diagSecond P i := by simp [diagCross, diagSecond, pow_two]

lemma entrySecond_self {P : Matrix E E ℂ} (hP : P.IsHermitian) (i : E) :
    entrySecond P i i = diagSecond P i := by
  unfold entrySecond diagSecond
  congr 1
  funext U
  have hh := congrArg Complex.im ((orbit_isHermitian hP U).coe_re_apply_self i)
  have hi : (orbit P U i i).im = 0 := by simpa using hh.symm
  simp [Complex.normSq_apply, hi, pow_two]

lemma sum_orbit_entry_normSq {P : Matrix E E ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (U : Matrix.unitaryGroup E ℂ) (i : E) :
    ∑ j, Complex.normSq (orbit P U i j) = (orbit P U i i).re := by
  have hh := orbit_isHermitian hP U
  have hp := congrArg Complex.re (congrFun (congrFun (orbit_idempotent hPP U) i) i)
  rw [Matrix.mul_apply, Complex.re_sum] at hp
  convert hp using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← hh.apply j i, Complex.star_def, Complex.mul_conj]
  simp

lemma sum_entrySecond_row [Nonempty E] {P : Matrix E E ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (i : E) :
    ∑ j, entrySecond P i j = (Matrix.trace P).re / Fintype.card E := by
  unfold entrySecond
  rw [← integral_finset_sum _ (fun j _ => integrable_entrySecond P i j)]
  simp_rw [sum_orbit_entry_normSq hP hPP]
  exact integral_orbit_diag P i

lemma sum_diagCross_row [Nonempty E] (P : Matrix E E ℂ) (i : E) :
    ∑ j, diagCross P i j = (Matrix.trace P).re ^ 2 / Fintype.card E := by
  have htrace (U : Matrix.unitaryGroup E ℂ) :
      ∑ j, (orbit P U j j).re = (Matrix.trace P).re := by
    rw [← Complex.re_sum]
    change (Matrix.trace (orbit P U)).re = _
    rw [orbit_trace]
  unfold diagCross
  rw [← integral_finset_sum _ (fun j _ => integrable_diagCross P i j)]
  simp_rw [← Finset.mul_sum, htrace]
  rw [integral_mul_const, integral_orbit_diag]
  ring

lemma sum_of_constant_off_diagonal (f : E → E → ℝ) (i : E) (α γ : ℝ)
    (hdiag : f i i = α) (hoff : ∀ j, i ≠ j → f i j = γ) :
    ∑ j, f i j = α + ((Fintype.card E : ℝ) - 1) * γ := by
  have hc : 1 ≤ Fintype.card E := Fintype.card_pos_iff.mpr ⟨i⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag]
  have he : ∑ j ∈ Finset.univ.erase i, f i j = ((Fintype.card E : ℝ) - 1) * γ := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, γ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hoff j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = _ := by simp [Finset.card_erase_of_mem, Nat.cast_sub hc]
  rw [he, add_comm]

theorem second_moment_projection_trace {P : Matrix E E ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (i j : E) (hij : i ≠ j) :
    (Fintype.card E : ℝ) * diagSecond P i +
      (Fintype.card E : ℝ) * ((Fintype.card E : ℝ) - 1) * entrySecond P i j =
      (Matrix.trace P).re := by
  letI : Nonempty E := ⟨i⟩
  have hs := sum_entrySecond_row hP hPP i
  rw [sum_of_constant_off_diagonal (entrySecond P) i (diagSecond P i)
    (entrySecond P i j) (entrySecond_self hP i)
    (fun l hil => entrySecond_eq P hil hij)] at hs
  have hc : (Fintype.card E : ℝ) ≠ 0 := by positivity
  have hh := (eq_div_iff hc).mp hs
  nlinarith [hh]

theorem second_moment_trace_square (P : Matrix E E ℂ) (i j : E) (hij : i ≠ j) :
    (Fintype.card E : ℝ) * diagSecond P i +
      (Fintype.card E : ℝ) * ((Fintype.card E : ℝ) - 1) * diagCross P i j =
      (Matrix.trace P).re ^ 2 := by
  letI : Nonempty E := ⟨i⟩
  have hs := sum_diagCross_row P i
  rw [sum_of_constant_off_diagonal (diagCross P) i (diagSecond P i)
    (diagCross P i j) (diagCross_self P i)
    (fun l hil => diagCross_eq P hil hij)] at hs
  have hc : (Fintype.card E : ℝ) ≠ 0 := by positivity
  have hh := (eq_div_iff hc).mp hs
  nlinarith [hh]

end ProjectionChannels.HaarMoment

#print axioms ProjectionChannels.HaarMoment.diagCross_eq
#print axioms ProjectionChannels.HaarMoment.entrySecond_eq
#print axioms ProjectionChannels.HaarMoment.second_moment_projection_trace
#print axioms ProjectionChannels.HaarMoment.second_moment_trace_square
