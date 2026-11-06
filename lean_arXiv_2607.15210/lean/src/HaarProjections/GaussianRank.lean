import Preliminaries.PreliminariesMatrix
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Polynomial.Roots

open scoped BigOperators NNReal ENNReal
open MeasureTheory MeasureTheory.Measure ProbabilityTheory MvPolynomial Matrix

noncomputable section

namespace GaussianRank

/-- The real component law of a standard circular complex Gaussian. -/
def realComponent : Measure ℝ := gaussianReal 0 (1 / 2)

instance : IsProbabilityMeasure realComponent := by
  unfold realComponent
  infer_instance

instance : NoAtoms realComponent where
  measure_singleton x := by
    apply gaussianReal_absolutelyContinuous (0 : ℝ) (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)
    exact measure_singleton x

/-- A standard circular complex Gaussian has independent N(0,1/2) real and imaginary parts. -/
def complexGaussian : Measure ℂ :=
  (realComponent.prod realComponent).map Complex.measurableEquivRealProd.symm

instance : IsProbabilityMeasure complexGaussian :=
  isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

instance : NoAtoms complexGaussian where
  measure_singleton z := by
    rw [complexGaussian, MeasurableEquiv.map_apply]
    have h : Complex.measurableEquivRealProd.symm ⁻¹' {z} =
        {Complex.measurableEquivRealProd z} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact Complex.measurableEquivRealProd.symm_apply_eq
    rw [h]
    exact measure_singleton _

/-- A nonzero complex polynomial vanishes on a finite, hence null, set for an atomless law. -/
theorem polynomial_ae_ne_zero (μ : Measure ℂ) [NoAtoms μ]
    (p : Polynomial ℂ) (hp : p ≠ 0) : ∀ᵐ z ∂μ, p.eval z ≠ 0 := by
  have h := (Polynomial.finite_setOf_isRoot hp).measure_zero μ
  simpa only [ae_iff, Set.compl_setOf, not_not, Polynomial.IsRoot] using h

/-- A nonzero polynomial in finitely many independent atomless complex variables is nonzero a.s. -/
theorem mvPolynomial_ae_ne_zero_fin (n : ℕ)
    (μ : Fin n → Measure ℂ) [∀ i, SigmaFinite (μ i)] [∀ i, NoAtoms (μ i)]
    (p : MvPolynomial (Fin n) ℂ) (hp : p ≠ 0) :
    ∀ᵐ z ∂Measure.pi μ, MvPolynomial.eval z p ≠ 0 := by
  classical
  induction n with
  | zero =>
    have hc : p.coeff 0 ≠ 0 := by
      intro h
      apply hp
      rw [MvPolynomial.eq_C_of_isEmpty p, h, map_zero]
    filter_upwards [] with z
    rw [MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eval_C]
    exact hc
  | succ n ih =>
    let q := MvPolynomial.finSuccEquiv ℂ n p
    have hq : q ≠ 0 := by
      intro h
      apply hp
      apply (MvPolynomial.finSuccEquiv ℂ n).injective
      simpa only [map_zero] using h
    have hcoef : ∃ j, q.coeff j ≠ 0 := by
      by_contra! h
      apply hq
      apply Polynomial.ext
      intro j
      simpa only [Polynomial.coeff_zero] using h j
    obtain ⟨j, hj⟩ := hcoef
    have htail := ih (fun i => μ i.succ) (q.coeff j) hj
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
    have he := measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
    have hm : MeasurableSet {x : ℂ × (Fin n → ℂ) |
        MvPolynomial.eval (Fin.cons x.1 x.2) p ≠ 0} := by
      apply MeasurableSet.compl
      have hc : Continuous (fun x : ℂ × (Fin n → ℂ) => (Fin.cons x.1 x.2 : Fin (n + 1) → ℂ)) := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero] using
            (continuous_fst : Continuous (fun x : ℂ × (Fin n → ℂ) => x.1))
        · simpa only [Fin.cons_succ] using (continuous_apply j).comp
            (continuous_snd : Continuous (fun x : ℂ × (Fin n → ℂ) => x.2))
      exact (p.continuous_eval.comp hc).measurable (measurableSet_singleton 0)
    have hprod : ∀ᵐ x ∂(μ 0).prod (Measure.pi (fun i => μ i.succ)),
        MvPolynomial.eval (Fin.cons x.1 x.2) p ≠ 0 := by
      rw [ae_prod_iff_ae_ae hm, ae_ae_comm hm]
      filter_upwards [htail] with z hz
      have hmap : q.map (MvPolynomial.eval z) ≠ 0 := by
        intro h
        have hh := congrArg (fun r : Polynomial ℂ => r.coeff j) h
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hh
        exact hz hh
      simpa only [MvPolynomial.eval_eq_eval_mv_eval', q] using
        polynomial_ae_ne_zero (μ 0) (q.map (MvPolynomial.eval z)) hmap
    have ha := he.quasiMeasurePreserving.ae hprod
    filter_upwards [ha] with z hz
    simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, e] using hz

/-- The polynomial nonvanishing theorem with an arbitrary finite coordinate set. -/
theorem mvPolynomial_ae_ne_zero {I : Type*} [Fintype I]
    (μ : I → Measure ℂ) [∀ i, SigmaFinite (μ i)] [∀ i, NoAtoms (μ i)]
    (p : MvPolynomial I ℂ) (hp : p ≠ 0) :
    ∀ᵐ z ∂Measure.pi μ, MvPolynomial.eval z p ≠ 0 := by
  classical
  let e := Fintype.equivFin I
  let q := MvPolynomial.renameEquiv ℂ e p
  have hq : q ≠ 0 := by
    intro h
    apply hp
    apply (MvPolynomial.renameEquiv ℂ e).injective
    simpa only [map_zero] using h
  have ha := mvPolynomial_ae_ne_zero_fin (Fintype.card I)
    (fun i => μ (e.symm i)) q hq
  have he := (measurePreserving_piCongrLeft μ e.symm).symm
  have hb := he.quasiMeasurePreserving.ae ha
  filter_upwards [hb] with z hz
  simpa [q, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft', Function.comp_def] using hz

/-- Restricting rows and columns cannot increase matrix rank. -/
theorem rank_submatrix_le_general {I J I' J' : Type*}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (G : Matrix I J ℂ) (f : I' → I) (g : J' → J) :
    (G.submatrix f g).rank ≤ G.rank := by
  classical
  have h : (1 : Matrix I I ℂ).submatrix f (Equiv.refl I) * G *
      (1 : Matrix J J ℂ).submatrix (Equiv.refl J) g = G.submatrix f g := by
    rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one]
    rfl
  rw [← h]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Independent atomless entries give a rectangular matrix maximal rank almost surely. -/
theorem ae_matrix_rank {I J : Type*} [Fintype I] [Fintype J]
    (μ : I × J → Measure ℂ) [∀ i, SigmaFinite (μ i)] [∀ i, NoAtoms (μ i)] :
    ∀ᵐ z ∂Measure.pi μ,
      Matrix.rank ((fun i j => z (i, j)) : Matrix I J ℂ) = min (Fintype.card I) (Fintype.card J) := by
  classical
  let r := min (Fintype.card I) (Fintype.card J)
  let f : Fin r → I := fun i => (Fintype.equivFin I).symm (Fin.castLE (min_le_left _ _) i)
  let g : Fin r → J := fun j => (Fintype.equivFin J).symm (Fin.castLE (min_le_right _ _) j)
  let Q : Matrix (Fin r) (Fin r) (MvPolynomial (I × J) ℂ) :=
    fun i j => MvPolynomial.X (f i, g j)
  let p := Q.det
  have heval (z : I × J → ℂ) : MvPolynomial.eval z p =
      Matrix.det ((fun i j => z (f i, g j)) : Matrix (Fin r) (Fin r) ℂ) := by
    dsimp only [p]
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [Q]
  let z₀ : I × J → ℂ := fun ij =>
    if ((Fintype.equivFin I) ij.1).val = ((Fintype.equivFin J) ij.2).val then 1 else 0
  have hidentity : ((fun i j => z₀ (f i, g j)) : Matrix (Fin r) (Fin r) ℂ) = (1 : Matrix (Fin r) (Fin r) ℂ) := by
    ext i j
    simp [z₀, f, g, Matrix.one_apply, Fin.ext_iff]
  have hp : p ≠ 0 := by
    intro h
    have hbad := congrArg (MvPolynomial.eval z₀) h
    rw [heval, hidentity, Matrix.det_one, map_zero] at hbad
    exact one_ne_zero hbad
  filter_upwards [mvPolynomial_ae_ne_zero μ p hp] with z hz
  let G : Matrix I J ℂ := fun i j => z (i, j)
  have hn : (G.submatrix f g).det ≠ 0 := by
    simpa only [heval, G, Matrix.submatrix] using hz
  have hr := Matrix.rank_of_isUnit (G.submatrix f g)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn))
  have hlow := rank_submatrix_le_general G f g
  have hup := le_min (Matrix.rank_le_card_height G) (Matrix.rank_le_card_width G)
  simp only [Fintype.card_fin] at hr
  change G.rank = r
  omega

/-- Maximal rank for actual independent standard complex Gaussian entries. -/
theorem ae_complexGaussian_matrix_rank (I J : Type*) [Fintype I] [Fintype J] :
    ∀ᵐ z ∂Measure.pi (fun _ : I × J => complexGaussian),
      Matrix.rank ((fun i j => z (i, j)) : Matrix I J ℂ) = min (Fintype.card I) (Fintype.card J) :=
  ae_matrix_rank _

/-- Reindexing the independent Gaussian coordinates preserves the maximal-rank statement. -/
theorem ae_complexGaussian_matrix_rank_reindex
    (I J K : Type*) [Fintype I] [Fintype J] [Fintype K] (e : I × J ≃ K) :
    ∀ᵐ z ∂Measure.pi (fun _ : K => complexGaussian),
      Matrix.rank ((fun i j => z (e (i, j))) : Matrix I J ℂ) =
        min (Fintype.card I) (Fintype.card J) := by
  have he := (measurePreserving_piCongrLeft (fun _ : K => complexGaussian) e).symm
  have ha := he.quasiMeasurePreserving.ae (ae_complexGaussian_matrix_rank I J)
  simpa [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft'] using ha

/-- Both ranks needed in the Gaussian proof of full local support hold on one event of probability one. -/
theorem ae_gaussian_whitening_rank_inputs
    (A B D : Type*) [Fintype A] [Fintype B] [Fintype D]
    (hd : Fintype.card D ≤ Fintype.card A * Fintype.card B) :
    ∀ᵐ z ∂Measure.pi (fun _ : (A × B) × D => complexGaussian),
      let G : Matrix (A × B) D ℂ := fun ab d => z (ab, d)
      G.rank = Fintype.card D ∧
        (PreliminariesMatrix.flatten G).rank =
          min (Fintype.card A) (Fintype.card B * Fintype.card D) := by
  have h1 := ae_complexGaussian_matrix_rank (A × B) D
  have h2 := ae_complexGaussian_matrix_rank_reindex A (B × D) ((A × B) × D)
    (Equiv.prodAssoc A B D).symm
  filter_upwards [h1, h2] with z hz1 hz2
  constructor
  · simpa only [Fintype.card_prod, min_eq_right hd] using hz1
  · simpa only [PreliminariesMatrix.flatten, Fintype.card_prod,
      Equiv.prodAssoc_symm_apply] using hz2

end GaussianRank

