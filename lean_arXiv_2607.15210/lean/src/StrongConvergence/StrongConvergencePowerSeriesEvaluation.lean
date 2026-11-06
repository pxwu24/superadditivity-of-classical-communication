import StrongConvergence.StrongConvergenceFreeCumulant
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Absolute evaluation of real formal power series.  Every multiplicative
identity below requires and proves the relevant absolute-convergence facts. -/

open PowerSeries
open scoped BigOperators

noncomputable section
namespace ProjectionChannels.PowerSeriesEvaluation

def eval (F : PowerSeries ℝ) (z : ℝ) : ℝ := ∑' n : ℕ, coeff ℝ n F * z ^ n

def AbsSummable (F : PowerSeries ℝ) (z : ℝ) : Prop :=
  Summable (fun n : ℕ => |coeff ℝ n F * z ^ n|)

def absSum (F : PowerSeries ℝ) (z : ℝ) : ℝ := ∑' n : ℕ, |coeff ℝ n F * z ^ n|

theorem AbsSummable.summable {F : PowerSeries ℝ} {z : ℝ} (h : AbsSummable F z) :
    Summable (fun n : ℕ => coeff ℝ n F * z ^ n) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using h

theorem absSum_nonneg (F : PowerSeries ℝ) (z : ℝ) : 0 ≤ absSum F z :=
  tsum_nonneg (fun _ => abs_nonneg _)

theorem abs_eval_le_absSum {F : PowerSeries ℝ} {z : ℝ} (h : AbsSummable F z) :
    |eval F z| ≤ absSum F z := by
  simpa only [eval, absSum, Real.norm_eq_abs] using
    norm_tsum_le_tsum_norm (show Summable (fun n => ‖coeff ℝ n F * z ^ n‖) by
      simpa only [Real.norm_eq_abs] using h)

@[simp] theorem absSummable_C (c z : ℝ) : AbsSummable (C ℝ c) z := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  have hn0 : n ≠ 0 := by simpa using hn
  simp [PowerSeries.coeff_C, hn0]

@[simp] theorem eval_C (c z : ℝ) : eval (C ℝ c) z = c := by
  unfold eval
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [PowerSeries.coeff_C, hn]

@[simp] theorem absSum_C (c z : ℝ) : absSum (C ℝ c) z = |c| := by
  unfold absSum
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [PowerSeries.coeff_C, hn]

@[simp] theorem absSummable_one (z : ℝ) : AbsSummable (1 : PowerSeries ℝ) z := by
  simpa only [map_one] using absSummable_C 1 z

@[simp] theorem eval_one (z : ℝ) : eval (1 : PowerSeries ℝ) z = 1 := by
  simpa only [map_one] using eval_C 1 z

@[simp] theorem absSum_one (z : ℝ) : absSum (1 : PowerSeries ℝ) z = 1 := by
  simpa only [map_one, abs_one] using absSum_C 1 z

theorem AbsSummable.add {F G : PowerSeries ℝ} {z : ℝ}
    (hF : AbsSummable F z) (hG : AbsSummable G z) : AbsSummable (F + G) z := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ (Summable.add hF hG)
  intro n
  simpa only [map_add, add_mul] using abs_add_le (coeff ℝ n F * z ^ n) (coeff ℝ n G * z ^ n)

theorem eval_add {F G : PowerSeries ℝ} {z : ℝ}
    (hF : AbsSummable F z) (hG : AbsSummable G z) : eval (F + G) z = eval F z + eval G z := by
  simp only [eval, map_add, add_mul]
  exact hF.summable.tsum_add hG.summable

theorem AbsSummable.neg {F : PowerSeries ℝ} {z : ℝ} (hF : AbsSummable F z) :
    AbsSummable (-F) z := by
  simpa only [AbsSummable, map_neg, neg_mul, abs_neg] using hF

theorem eval_neg (F : PowerSeries ℝ) (z : ℝ) : eval (-F) z = -eval F z := by
  simp only [eval, map_neg, neg_mul, tsum_neg]

theorem AbsSummable.sub {F G : PowerSeries ℝ} {z : ℝ}
    (hF : AbsSummable F z) (hG : AbsSummable G z) : AbsSummable (F - G) z := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem eval_sub {F G : PowerSeries ℝ} {z : ℝ}
    (hF : AbsSummable F z) (hG : AbsSummable G z) : eval (F - G) z = eval F z - eval G z := by
  rw [sub_eq_add_neg, eval_add hF hG.neg, eval_neg, sub_eq_add_neg]

theorem coeff_mul_eval_term (F G : PowerSeries ℝ) (z : ℝ) (n : ℕ) :
    coeff ℝ n (F * G) * z ^ n =
      ∑ ij ∈ Finset.antidiagonal n,
        (coeff ℝ ij.1 F * z ^ ij.1) * (coeff ℝ ij.2 G * z ^ ij.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn := Finset.mem_antidiagonal.mp hij
  rw [← hn, pow_add]
  ring

theorem AbsSummable.mul {F G : PowerSeries ℝ} {z : ℝ}
    (hF : AbsSummable F z) (hG : AbsSummable G z) : AbsSummable (F * G) z := by
  have hFn : Summable (fun n => ‖coeff ℝ n F * z ^ n‖) := by
    simpa only [Real.norm_eq_abs] using hF
  have hGn : Summable (fun n => ‖coeff ℝ n G * z ^ n‖) := by
    simpa only [Real.norm_eq_abs] using hG
  simpa only [AbsSummable, Real.norm_eq_abs, coeff_mul_eval_term] using
    summable_norm_sum_mul_antidiagonal_of_summable_norm hFn hGn

theorem eval_mul {F G : PowerSeries ℝ} {z : ℝ}
    (hF : AbsSummable F z) (hG : AbsSummable G z) : eval (F * G) z = eval F z * eval G z := by
  have hFn : Summable (fun n => ‖coeff ℝ n F * z ^ n‖) := by
    simpa only [Real.norm_eq_abs] using hF
  have hGn : Summable (fun n => ‖coeff ℝ n G * z ^ n‖) := by
    simpa only [Real.norm_eq_abs] using hG
  simpa only [eval, coeff_mul_eval_term] using
    (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hFn hGn).symm

theorem AbsSummable.pow {F : PowerSeries ℝ} {z : ℝ} (hF : AbsSummable F z) (n : ℕ) :
    AbsSummable (F ^ n) z := by
  induction n with
  | zero => simpa only [pow_zero] using absSummable_one z
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem eval_pow {F : PowerSeries ℝ} {z : ℝ} (hF : AbsSummable F z) (n : ℕ) :
    eval (F ^ n) z = eval F z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, eval_mul (hF.pow n) hF, ih, pow_succ]

private theorem tsum_abs_convolution_le (f g : ℕ → ℝ)
    (hf : Summable (fun n => |f n|)) (hg : Summable (fun n => |g n|)) :
    (∑' n, |∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2|) ≤
      (∑' n, |f n|) * (∑' n, |g n|) := by
  have hfn : Summable (fun n => ‖f n‖) := by simpa only [Real.norm_eq_abs] using hf
  have hgn : Summable (fun n => ‖g n‖) := by simpa only [Real.norm_eq_abs] using hg
  have hconv : Summable (fun n => |∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2|) := by
    simpa only [Real.norm_eq_abs] using
      summable_norm_sum_mul_antidiagonal_of_summable_norm (f := f) (g := g) hfn hgn
  have hfan : Summable (fun n => ‖|f n|‖) := by simpa only [Real.norm_eq_abs, abs_abs] using hf
  have hgan : Summable (fun n => ‖|g n|‖) := by simpa only [Real.norm_eq_abs, abs_abs] using hg
  have hmaj : Summable (fun n : ℕ => ∑ ij ∈ Finset.antidiagonal n, |f ij.1| * |g ij.2|) :=
    summable_sum_mul_antidiagonal_of_summable_norm' (f := fun n => |f n|)
      (g := fun n => |g n|) hfan hf hgan hg
  calc
    _ ≤ ∑' n : ℕ, ∑ ij ∈ Finset.antidiagonal n, |f ij.1| * |g ij.2| := by
      apply Summable.tsum_le_tsum _ hconv hmaj
      intro n
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun ij : ℕ × ℕ => f ij.1 * g ij.2) (Finset.antidiagonal n)
    _ = (∑' n, |f n|) * (∑' n, |g n|) :=
      (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        (f := fun n => |f n|) (g := fun n => |g n|) hfan hgan).symm

theorem absSum_mul_le {F G : PowerSeries ℝ} {z : ℝ}
    (hF : AbsSummable F z) (hG : AbsSummable G z) :
    absSum (F * G) z ≤ absSum F z * absSum G z := by
  simpa only [absSum, coeff_mul_eval_term] using
    tsum_abs_convolution_le (fun n => coeff ℝ n F * z^n)
      (fun n => coeff ℝ n G * z^n) hF hG

theorem absSum_pow_le {F : PowerSeries ℝ} {z : ℝ} (hF : AbsSummable F z) (n : ℕ) :
    absSum (F ^ n) z ≤ absSum F z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (absSum_mul_le (hF.pow n) hF).trans
      (mul_le_mul_of_nonneg_right ih (absSum_nonneg F z))

/-- Formal series absolutely evaluable at a fixed real argument form a
subalgebra. -/
def summableSubalgebra (z : ℝ) : Subalgebra ℝ (PowerSeries ℝ) where
  carrier := {F | AbsSummable F z}
  zero_mem' := by simpa only [map_zero] using absSummable_C 0 z
  one_mem' := absSummable_one z
  add_mem' := fun hF hG => hF.add hG
  mul_mem' := fun hF hG => hF.mul hG
  algebraMap_mem' := fun c => absSummable_C c z

/-- Evaluation is an algebra homomorphism on the domain of absolute
convergence; thus formal polynomial identities can be evaluated rigorously. -/
def evalAlgHom (z : ℝ) : summableSubalgebra z →ₐ[ℝ] ℝ where
  toFun F := eval F.val z
  map_zero' := by simpa only [map_zero] using eval_C 0 z
  map_one' := eval_one z
  map_add' F G := eval_add F.property G.property
  map_mul' F G := eval_mul F.property G.property
  commutes' c := eval_C c z

theorem coeff_pow_eq_zero_of_lt {W : PowerSeries ℝ}
    (hW : constantCoeff ℝ W = 0) {n r : ℕ} (hnr : n < r) :
    coeff ℝ n (W ^ r) = 0 := by
  have hd : (X : PowerSeries ℝ) ∣ W := PowerSeries.X_dvd_iff.mpr hW
  exact (PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hd r)) n hnr

/-- The native formal substitution has the expected univariate coefficient
formula. Only finitely many terms on the right can be nonzero. -/
theorem coeff_formalSubst (G W : PowerSeries ℝ) (hW : constantCoeff ℝ W = 0) (n : ℕ) :
    coeff ℝ n (FreeCumulant.formalSubst W hW G) =
      ∑' r : ℕ, coeff ℝ r G * coeff ℝ n (W ^ r) := by
  have hfinite : (Function.support (fun r : ℕ => coeff ℝ r G * coeff ℝ n (W ^ r))).Finite := by
    apply (Finset.finite_toSet (Finset.range (n + 1))).subset
    intro r hr
    by_contra hnot
    have hnr : n < r := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hnot
    have hz := coeff_pow_eq_zero_of_lt hW hnr
    exact hr (by simp [hz])
  rw [tsum_eq_finsum hfinite]
  unfold FreeCumulant.formalSubst
  rw [MvPowerSeries.coe_substAlgHom]
  change MvPowerSeries.coeff ℝ (Finsupp.single () n)
    (MvPowerSeries.subst (fun _ : Unit => W) G) = _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hW))]
  rw [← finsum_comp_equiv ((AddEquiv.finsuppUnique : (Unit →₀ ℕ) ≃+ ℕ).symm.toEquiv)]
  apply finsum_congr
  intro r
  simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, AddEquiv.finsuppUnique_symm,
    smul_eq_mul]
  rw [Finsupp.prod_single_index (h := fun (_ : Unit) (e : ℕ) => W ^ e) (pow_zero W)]
  rfl

/-- Absolute convergence of every term in the double series for composition,
under the natural absolute-majorant condition on the outer series. -/
theorem summable_abs_substTerms {G W : PowerSeries ℝ} {z : ℝ}
    (hW : AbsSummable W z) (hG : AbsSummable G (absSum W z)) :
    Summable (fun rn : ℕ × ℕ =>
      |coeff ℝ rn.1 G * coeff ℝ rn.2 (W ^ rn.1) * z ^ rn.2|) := by
  have hrow (r : ℕ) : Summable (fun n =>
      |coeff ℝ r G * coeff ℝ n (W ^ r) * z ^ n|) := by
    simpa only [abs_mul, mul_assoc] using
      (Summable.mul_left |coeff ℝ r G| (hW.pow r))
  have hroweq (r : ℕ) : (∑' n, |coeff ℝ r G * coeff ℝ n (W ^ r) * z ^ n|) =
      |coeff ℝ r G| * absSum (W ^ r) z := by
    simp only [absSum, abs_mul, mul_assoc, tsum_mul_left]
  have hmaj : Summable (fun r => |coeff ℝ r G| * absSum W z ^ r) := by
    simpa only [AbsSummable, abs_mul, abs_pow, abs_of_nonneg (absSum_nonneg W z)] using hG
  apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
  refine ⟨hrow, Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => abs_nonneg _)) ?_ hmaj⟩
  intro r
  rw [hroweq]
  exact mul_le_mul_of_nonneg_left (absSum_pow_le hW r) (abs_nonneg _)

theorem coeff_eval_formalSubst (G W : PowerSeries ℝ)
    (hW : constantCoeff ℝ W = 0) (z : ℝ) (n : ℕ) :
    coeff ℝ n (FreeCumulant.formalSubst W hW G) * z ^ n =
      ∑' r, coeff ℝ r G * coeff ℝ n (W ^ r) * z ^ n := by
  rw [coeff_formalSubst, tsum_mul_right]

theorem AbsSummable.formalSubst {G W : PowerSeries ℝ} {z : ℝ}
    (hW0 : constantCoeff ℝ W = 0)
    (hW : AbsSummable W z) (hG : AbsSummable G (absSum W z)) :
    AbsSummable (FreeCumulant.formalSubst W hW0 G) z := by
  have hdouble := summable_abs_substTerms hW hG
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ hdouble.prod_symm.prod
  intro n
  rw [coeff_eval_formalSubst]
  have hn := hdouble.prod_symm.prod_factor n
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
    (show Summable (fun r => ‖coeff ℝ r G * coeff ℝ n (W ^ r) * z ^ n‖) by
      simpa only [Real.norm_eq_abs] using hn)

/-- Evaluation commutes with native formal substitution whenever the inner
series is absolutely convergent and its absolute mass lies in an absolute
convergence domain of the outer series. -/
theorem eval_formalSubst {G W : PowerSeries ℝ} {z : ℝ}
    (hW0 : constantCoeff ℝ W = 0)
    (hW : AbsSummable W z) (hG : AbsSummable G (absSum W z)) :
    eval (FreeCumulant.formalSubst W hW0 G) z = eval G (eval W z) := by
  have ha := summable_abs_substTerms hW hG
  have hs : Summable (fun rn : ℕ × ℕ =>
      coeff ℝ rn.1 G * coeff ℝ rn.2 (W ^ rn.1) * z ^ rn.2) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using ha
  unfold eval
  simp_rw [coeff_eval_formalSubst]
  rw [Summable.tsum_comm (f := fun r n =>
    coeff ℝ r G * coeff ℝ n (W ^ r) * z ^ n) hs]
  apply tsum_congr
  intro r
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  congr 1
  exact eval_pow hW r

@[simp] theorem absSummable_X (z : ℝ) : AbsSummable (X : PowerSeries ℝ) z := by
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn
  have hn1 : n ≠ 1 := by simpa using hn
  simp [coeff_X, hn1]

@[simp] theorem eval_X (z : ℝ) : eval (X : PowerSeries ℝ) z = z := by
  unfold eval
  rw [tsum_eq_single 1]
  · simp
  · intro n hn
    simp [coeff_X, hn]

@[simp] theorem absSum_X (z : ℝ) : absSum (X : PowerSeries ℝ) z = |z| := by
  unfold absSum
  rw [tsum_eq_single 1]
  · simp
  · intro n hn
    simp [coeff_X, hn]

theorem AbsSummable.mono {F : PowerSeries ℝ} {x y : ℝ}
    (hF : AbsSummable F y) (hxy : |x| ≤ |y|) : AbsSummable F x := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ hF
  intro n
  simp only [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxy n) (abs_nonneg _)

theorem absSummable_rescale_iff (F : PowerSeries ℝ) (c z : ℝ) :
    AbsSummable (rescale c F) z ↔ AbsSummable F (c * z) := by
  have ht (n : ℕ) : coeff ℝ n (rescale c F) * z ^ n = coeff ℝ n F * (c*z)^n := by
    rw [coeff_rescale, mul_pow]
    ring
  simp only [AbsSummable, ht]

theorem eval_rescale (F : PowerSeries ℝ) (c z : ℝ) :
    eval (rescale c F) z = eval F (c * z) := by
  apply tsum_congr
  intro n
  rw [coeff_rescale, mul_pow]
  ring

theorem AbsSummable.sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℝ) {z : ℝ}
    (hF : ∀i ∈ s, AbsSummable (F i) z) : AbsSummable (∑i ∈ s, F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using absSummable_C 0 z
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem eval_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℝ) {z : ℝ}
    (hF : ∀i ∈ s, AbsSummable (F i) z) :
    eval (∑i ∈ s, F i) z = ∑i ∈ s, eval (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using eval_C 0 z
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [eval_add (hF i (Finset.mem_insert_self _ _))
      (AbsSummable.sum s F (fun j hj => hF j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))]

#print axioms eval_formalSubst
#print axioms AbsSummable.formalSubst
#print axioms absSum_mul_le

end ProjectionChannels.PowerSeriesEvaluation
