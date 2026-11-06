import Dimension182.RevisionK182Multiplier
import Dimension182.RevisionK182BoundaryTools

/-! A transfer between two positive coordinates with an added vanishing
coordinate. This file records exact finite-sum and derivative identities. -/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace ProjectionChannels.RevisionK182
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def birthCurve (u : ι → ℝ) (i j z : ι) (M : ℝ) (r : ℕ) (x : ℝ) (l : ι) : ℝ :=
  if l=i then u i-x else if l=j then u j+x else if l=z then M*x^r else u l

theorem birthCurve_zero (u : ι → ℝ) (i j z : ι) (M : ℝ) (r : ℕ)
    (hr : r ≠ 0) (hz : u z=0) : birthCurve u i j z M r 0 = u := by
  ext l
  by_cases hi : l=i
  · simp [birthCurve,hi]
  · by_cases hj : l=j
    · subst l
      simp [birthCurve,hi]
    · by_cases hlz : l=z
      · subst l
        simp [birthCurve,hi,hj,hr,hz]
      · simp [birthCurve,hi,hj,hlz]

theorem continuous_birthCurve (u : ι → ℝ) (i j z : ι) (M : ℝ) (r : ℕ) :
    Continuous (birthCurve u i j z M r) := by
  apply continuous_pi
  intro l
  unfold birthCurve
  split_ifs <;> fun_prop

theorem sum_birthCurve (f : ℝ → ℝ) (u : ι → ℝ) {i j z : ι}
    (hij : i≠j) (hiz : i≠z) (hjz : j≠z) (hz : u z=0)
    (M x : ℝ) (r : ℕ) :
    (∑ l, f (birthCurve u i j z M r x l)) = (∑ l, f (u l)) +
      (f (u i-x)-f (u i)) + (f (u j+x)-f (u j)) + (f (M*x^r)-f 0) := by
  have heq (l : ι) : f (birthCurve u i j z M r x l) = f (u l) +
      (if l=i then f (u i-x)-f (u i) else 0) +
      (if l=j then f (u j+x)-f (u j) else 0) +
      (if l=z then f (M*x^r)-f 0 else 0) := by
    by_cases hi : l=i
    · subst l
      simp [birthCurve,hij,hiz]
    · by_cases hj : l=j
      · subst l
        simp [birthCurve,hij.symm,hjz]
      · by_cases hlz : l=z
        · subst l
          simp [birthCurve,hi,hj,hz]
        · simp [birthCurve,hi,hj,hlz]
  simp_rw [heq]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem mass_birthCurve (u : ι → ℝ) {i j z : ι}
    (hij : i≠j) (hiz : i≠z) (hjz : j≠z) (hz : u z=0)
    (M x : ℝ) (r : ℕ) :
    mass (birthCurve u i j z M r x) = mass u + M*x^r := by
  have h := sum_birthCurve id u hij hiz hjz hz M x r
  simp only [id_eq] at h
  change (∑ l, birthCurve u i j z M r x l) = _
  rw [h]
  unfold mass
  ring

theorem birthCurve_in_box_eventually (u : ι → ℝ) {i j z : ι}
    (hu : ∀ l, u l ∈ Icc 0 1) (hi : u i ∈ Ioo 0 1) (hj : u j ∈ Ioo 0 1)
    (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : r ≠ 0) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ l, birthCurve u i j z M r x l ∈ Icc 0 1 := by
  have hei : ∀ᶠ x in 𝓝 (0 : ℝ), u i-x ∈ Ioo 0 1 := by
    exact (show ContinuousAt (fun x : ℝ => u i-x) 0 by fun_prop).eventually
      (by simpa only [sub_zero] using Ioo_mem_nhds hi.1 hi.2)
  have hej : ∀ᶠ x in 𝓝 (0 : ℝ), u j+x ∈ Ioo 0 1 := by
    exact (show ContinuousAt (fun x : ℝ => u j+x) 0 by fun_prop).eventually
      (by simpa only [add_zero] using Ioo_mem_nhds hj.1 hj.2)
  have hez : ∀ᶠ x in 𝓝 (0 : ℝ), M*x^r < 1 := by
    exact (show ContinuousAt (fun x : ℝ => M*x^r) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simp [hr] : M*(0:ℝ)^r < 1))
  filter_upwards [nhdsWithin_le_nhds hei,nhdsWithin_le_nhds hej,
    nhdsWithin_le_nhds hez,self_mem_nhdsWithin] with x hxi hxj hxz hxp l
  unfold birthCurve
  split_ifs
  · exact ⟨hxi.1.le,hxi.2.le⟩
  · exact ⟨hxj.1.le,hxj.2.le⟩
  · exact ⟨mul_nonneg hM.le (pow_nonneg (show 0 ≤ x from le_of_lt hxp) _),hxz.le⟩
  · exact hu l

theorem hasDerivAt_sum_birthCurve (f : ℝ → ℝ) (u : ι → ℝ) {i j z : ι}
    (hij : i≠j) (hiz : i≠z) (hjz : j≠z) (hz : u z=0)
    (M : ℝ) (r : ℕ) {fi fj fz : ℝ}
    (hi : HasDerivAt f fi (u i)) (hj : HasDerivAt f fj (u j))
    (hborn : HasDerivAt (fun x : ℝ => f (M*x^r)) fz 0) :
    HasDerivAt (fun x => ∑ l, f (birthCurve u i j z M r x l)) (-fi+fj+fz) 0 := by
  have hei : HasDerivAt (fun x : ℝ => f (u i-x)) (-fi) 0 := by
    convert hi.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_sub (u i)) (by simp) using 1 <;>
      simp only [sub_zero,Function.comp_apply,neg_mul,one_mul,mul_neg_one]
  have hej : HasDerivAt (fun x : ℝ => f (u j+x)) fj 0 := by
    convert hj.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_add (u j)) (by simp) using 1 <;>
      simp only [add_zero,Function.comp_apply,mul_one]
  have hpair := (hei.sub_const (f (u i))).const_add (∑ l, f (u l))
  have hh := (hpair.add (hej.sub_const (f (u j)))).add (hborn.sub_const (f 0))
  convert hh using 1
  funext x
  exact sum_birthCurve f u hij hiz hjz hz M x r

theorem hasDerivWithinAt_sum_birthCurve (f : ℝ → ℝ) (u : ι → ℝ) {i j z : ι}
    (hij : i≠j) (hiz : i≠z) (hjz : j≠z) (hz : u z=0)
    (M : ℝ) (r : ℕ) {fi fj fz : ℝ}
    (hi : HasDerivAt f fi (u i)) (hj : HasDerivAt f fj (u j))
    (hborn : HasDerivWithinAt (fun x : ℝ => f (M*x^r)) fz (Ici 0) 0) :
    HasDerivWithinAt (fun x => ∑ l, f (birthCurve u i j z M r x l))
      (-fi+fj+fz) (Ici 0) 0 := by
  have hei : HasDerivAt (fun x : ℝ => f (u i-x)) (-fi) 0 := by
    convert hi.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_sub (u i)) (by simp) using 1 <;>
      simp only [sub_zero,Function.comp_apply,neg_mul,one_mul,mul_neg_one]
  have hej : HasDerivAt (fun x : ℝ => f (u j+x)) fj 0 := by
    convert hj.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_add (u j)) (by simp) using 1 <;>
      simp only [add_zero,Function.comp_apply,mul_one]
  have hpair := ((hei.hasDerivWithinAt (s:=Ici 0)).sub_const (f (u i))).const_add (∑ l, f (u l))
  have hh := (hpair.add (hej.hasDerivWithinAt.sub_const (f (u j)))).add (hborn.sub_const (f 0))
  convert hh using 1
  funext x
  exact sum_birthCurve f u hij hiz hjz hz M x r

end ProjectionChannels.RevisionK182
