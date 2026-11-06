import StrongConvergence.StrongConvergenceHaarPairMoments

/-! Finite Haar second-moment calculations, without asymptotic inputs. -/
open Matrix MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.HaarMoment

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma integral_orbit_conjugate (P : Matrix E E ℂ)
    (f : Matrix E E ℂ → ℝ) (V : Matrix.unitaryGroup E ℂ) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      f ((V : Matrix E E ℂ) * orbit P U * (V : Matrix E E ℂ).conjTranspose)
      ∂HaarProjection.unitaryHaar) =
    ∫ U : Matrix.unitaryGroup E ℂ, f (orbit P U) ∂HaarProjection.unitaryHaar := by
  have h := integral_mul_left_eq_self (μ := HaarProjection.unitaryHaar)
    (fun U : Matrix.unitaryGroup E ℂ => f (orbit P U)) V
  simpa only [orbit, Matrix.UnitaryGroup.mul_val, Matrix.conjTranspose_mul,
    Matrix.mul_assoc] using h

def pairMix (i j : E) (c : ℝ) (z : ℂ) : Matrix E E ℂ :=
  1 + Matrix.stdBasisMatrix i i ((c:ℂ)-1) +
    Matrix.stdBasisMatrix j j (-(c:ℂ)-1) +
    Matrix.stdBasisMatrix i j ((c:ℂ)*z) +
    Matrix.stdBasisMatrix j i ((c:ℂ)*star z)

lemma pairMix_row_i {i j : E} (hij : i≠j) (c : ℝ) (z : ℂ) (b : E) :
    pairMix i j c z i b = (if b=i then (c:ℂ) else 0) +
      (if b=j then (c:ℂ)*z else 0) := by
  by_cases hbi : b=i <;> by_cases hbj : b=j <;>
    simp_all [pairMix,Matrix.stdBasisMatrix,Matrix.one_apply,eq_comm] <;> ring

lemma pairMix_row_j {i j : E} (hij : i≠j) (c : ℝ) (z : ℂ) (b : E) :
    pairMix i j c z j b = (if b=i then (c:ℂ)*star z else 0) -
      (if b=j then (c:ℂ) else 0) := by
  by_cases hbi : b=i <;> by_cases hbj : b=j <;>
    simp_all [pairMix,Matrix.stdBasisMatrix,Matrix.one_apply,eq_comm] <;> ring

lemma pairMix_row_other {i j a : E} (hai : a≠i) (haj : a≠j)
    (c : ℝ) (z : ℂ) (b : E) :
    pairMix i j c z a b = if a=b then 1 else 0 := by
  simp [pairMix,Matrix.stdBasisMatrix,Matrix.one_apply,hai,haj,Ne.symm hai,Ne.symm haj]

lemma pairMix_isHermitian (i j : E) (c : ℝ) (z : ℂ) :
    (pairMix i j c z).IsHermitian := by
  ext a b
  simp [pairMix,Matrix.stdBasisMatrix,Matrix.conjTranspose_apply,Matrix.one_apply,
    star_add,star_sub,StarMul.star_mul]
  by_cases hai : a=i <;> by_cases haj : a=j <;>
    by_cases hbi : b=i <;> by_cases hbj : b=j <;>
    simp_all [eq_comm] <;> ring

lemma pairMix_mul_apply (i j : E) (c : ℝ) (z : ℂ) (M : Matrix E E ℂ) (a b : E) :
    (pairMix i j c z * M) a b = M a b +
      (if a=i then ((c:ℂ)-1)*M i b else 0) +
      (if a=j then (-(c:ℂ)-1)*M j b else 0) +
      (if a=i then (c:ℂ)*z*M j b else 0) +
      (if a=j then (c:ℂ)*star z*M i b else 0) := by
  simp only [pairMix,Matrix.add_mul,Matrix.one_mul,Matrix.add_apply]
  by_cases hai : a=i <;> by_cases haj : a=j <;>
    simp_all [Matrix.stdBasisMatrix,Matrix.mul_apply,ite_and,eq_comm]

lemma pairMix_square {i j : E} (hij : i≠j) (c : ℝ) (hc : 2*c^2=1)
    (z : ℂ) (hz : z*star z=1) :
    pairMix i j c z * pairMix i j c z = 1 := by
  have hc' : 2*(c:ℂ)^2=1 := by exact_mod_cast hc
  have hz' : star z*z=1 := by simpa [mul_comm] using hz
  ext a b
  rw [pairMix_mul_apply]
  by_cases hai : a=i
  · subst a
    simp only [if_pos rfl,if_neg hij]
    rw [pairMix_row_i hij,pairMix_row_j hij]
    by_cases hbi : b=i <;> by_cases hbj : b=j
    · exact False.elim (hij (hbi.symm.trans hbj))
    · simp only [if_pos hbi,if_neg hbj,Matrix.one_apply,← hbi,ite_true]
      calc
        _ = 2*(c:ℂ)^2 := by linear_combination (c:ℂ)^2*hz
        _ = 1 := hc'
    · simp only [if_neg hbi,if_pos hbj,Matrix.one_apply,Ne.symm hbi,ite_false]
      simp only [ite_true]; ring
    · simp [hbi,hbj,Matrix.one_apply,Ne.symm hbi]
  · by_cases haj : a=j
    · subst a
      simp only [if_neg hij.symm,if_pos rfl]
      rw [pairMix_row_i hij,pairMix_row_j hij]
      by_cases hbi : b=i <;> by_cases hbj : b=j
      · exact False.elim (hij (hbi.symm.trans hbj))
      · simp only [if_pos hbi,if_neg hbj,Matrix.one_apply,Ne.symm hbj,ite_false]
        simp only [ite_true]; ring
      · simp only [if_neg hbi,if_pos hbj,Matrix.one_apply,← hbj,ite_true]
        calc
          _ = 2*(c:ℂ)^2 := by linear_combination (c:ℂ)^2*hz'
          _ = 1 := hc'
      · simp [hbi,hbj,Matrix.one_apply,Ne.symm hbj]
    · simp [hai,haj,pairMix_row_other hai haj,Matrix.one_apply]

def pairMixUnitary {i j : E} (hij : i≠j) (c : ℝ) (hc : 2*c^2=1)
    (z : ℂ) (hz : z*star z=1) : Matrix.unitaryGroup E ℂ :=
  ⟨pairMix i j c z, Matrix.mem_unitaryGroup_iff'.mpr (by
    change (pairMix i j c z).conjTranspose * pairMix i j c z=1
    rw [(pairMix_isHermitian i j c z).eq]
    exact pairMix_square hij c hc z hz)⟩

lemma pairMix_left_i {i j : E} (hij : i≠j) (c : ℝ) (z : ℂ)
    (P : Matrix E E ℂ) (b : E) :
    (pairMix i j c z * P) i b = (c:ℂ)*P i b+(c:ℂ)*z*P j b := by
  rw [pairMix_mul_apply]
  simp only [if_pos rfl,if_neg hij,ite_true]
  ring

lemma pairMix_left_j {i j : E} (hij : i≠j) (c : ℝ) (z : ℂ)
    (P : Matrix E E ℂ) (b : E) :
    (pairMix i j c z * P) j b = (c:ℂ)*star z*P i b-(c:ℂ)*P j b := by
  rw [pairMix_mul_apply]
  simp only [if_pos rfl,if_neg hij.symm,ite_true]
  ring

lemma pairMix_right_i {i j : E} (hij : i≠j) (c : ℝ) (z : ℂ)
    (P : Matrix E E ℂ) (a : E) :
    (P * pairMix i j c z) a i = (c:ℂ)*P a i+(c:ℂ)*star z*P a j := by
  have hcol b : pairMix i j c z b i = star (pairMix i j c z i b) := by
    exact (congrFun (congrFun (pairMix_isHermitian i j c z).eq b) i).symm
  simp_rw [Matrix.mul_apply,hcol,pairMix_row_i hij,star_add,apply_ite star,
    star_zero,star_mul',Complex.star_def,Complex.conj_ofReal]
  simp only [mul_add,mul_ite,mul_zero,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

lemma pairMix_right_j {i j : E} (hij : i≠j) (c : ℝ) (z : ℂ)
    (P : Matrix E E ℂ) (a : E) :
    (P * pairMix i j c z) a j = (c:ℂ)*z*P a i-(c:ℂ)*P a j := by
  have hcol b : pairMix i j c z b j = star (pairMix i j c z j b) := by
    exact (congrFun (congrFun (pairMix_isHermitian i j c z).eq b) j).symm
  simp_rw [Matrix.mul_apply,hcol,pairMix_row_j hij,star_sub,apply_ite star,
    star_zero,star_mul',star_star,Complex.star_def,Complex.conj_ofReal]
  simp only [mul_sub,mul_ite,mul_zero,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

lemma pairMix_diagonal_i {i j : E} (hij : i≠j) (c : ℝ) (z : ℂ)
    (hz : z*star z=1) (P : Matrix E E ℂ) :
    (pairMix i j c z * P * pairMix i j c z) i i =
      (c:ℂ)^2*(P i i+P j j+z*P j i+star z*P i j) := by
  rw [pairMix_right_i hij,pairMix_left_i hij,pairMix_left_i hij]
  linear_combination (c:ℂ)^2*P j j*hz

lemma pairMix_diagonal_j {i j : E} (hij : i≠j) (c : ℝ) (z : ℂ)
    (hz : z*star z=1) (P : Matrix E E ℂ) :
    (pairMix i j c z * P * pairMix i j c z) j j =
      (c:ℂ)^2*(P i i+P j j-z*P j i-star z*P i j) := by
  rw [pairMix_right_j hij,pairMix_left_j hij,pairMix_left_j hij]
  linear_combination (c:ℂ)^2*P i i*hz

lemma pairMix_four_diagonal_squares {i j : E} (hij : i≠j) (c : ℝ)
    (hc : 2*c^2=1) (P : Matrix E E ℂ) (hP : P.IsHermitian) :
    ((pairMix i j c 1*P*pairMix i j c 1) i i).re^2 +
    ((pairMix i j c 1*P*pairMix i j c 1) j j).re^2 +
    ((pairMix i j c Complex.I*P*pairMix i j c Complex.I) i i).re^2 +
    ((pairMix i j c Complex.I*P*pairMix i j c Complex.I) j j).re^2 =
      (P i i).re^2+(P j j).re^2+2*(P i i).re*(P j j).re+2*Complex.normSq (P i j) := by
  have h1 : (1:ℂ)*star (1:ℂ)=1 := by simp
  have hI : Complex.I*star Complex.I=1 := by simp [Complex.star_def]
  have hji : P j i = star (P i j) :=
    (congrFun (congrFun hP.eq j) i).symm
  have hc2 : c^2=1/2 := by linarith
  rw [pairMix_diagonal_i hij c 1 h1,pairMix_diagonal_j hij c 1 h1,
    pairMix_diagonal_i hij c Complex.I hI,pairMix_diagonal_j hij c Complex.I hI,hji]
  have hcp : (c:ℂ)^2=(1/2:ℂ) := by rw [← Complex.ofReal_pow,hc2]; norm_num
  rw [hcp]
  simp [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.normSq_apply]
  ring

lemma pairMix_integrable_diagonal_square (P : Matrix E E ℂ) (i j l : E)
    (c : ℝ) (z : ℂ) :
    Integrable (fun U : Matrix.unitaryGroup E ℂ =>
      ((pairMix i j c z * orbit P U * pairMix i j c z) l l).re^2)
      HaarProjection.unitaryHaar := by
  have h : Continuous (fun U : Matrix.unitaryGroup E ℂ =>
      ((pairMix i j c z * orbit P U * pairMix i j c z) l l).re^2) :=
    (Complex.continuous_re.comp
      (((continuous_const.matrix_mul (HaarProjection.continuous_unitary_orbit P)).matrix_mul
        continuous_const).matrix_elem l l)).pow 2
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma pairMix_integral_diagonal_square (P : Matrix E E ℂ) {i j : E}
    (hij : i≠j) (l : E) (c : ℝ) (hc : 2*c^2=1) (z : ℂ) (hz : z*star z=1) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      ((pairMix i j c z * orbit P U * pairMix i j c z) l l).re^2
      ∂HaarProjection.unitaryHaar) = diagSecond P l := by
  have h := integral_orbit_conjugate P (fun M => (M l l).re^2)
    (pairMixUnitary hij c hc z hz)
  change (∫ U : Matrix.unitaryGroup E ℂ,
      ((pairMix i j c z * orbit P U * (pairMix i j c z).conjTranspose) l l).re^2
      ∂HaarProjection.unitaryHaar) = diagSecond P l at h
  rwa [(pairMix_isHermitian i j c z).eq] at h

theorem diagSecond_eq_diagCross_add_entrySecond {P : Matrix E E ℂ}
    (hP : P.IsHermitian) {i j : E} (hij : i≠j) :
    diagSecond P i = diagCross P i j + entrySecond P i j := by
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2≠0 := by positivity
  have hc : 2*c^2=1 := by dsimp [c]; field_simp <;> nlinarith
  have h1 : (1:ℂ)*star (1:ℂ)=1 := by simp
  have hI : Complex.I*star Complex.I=1 := by simp [Complex.star_def]
  have hi1 := pairMix_integrable_diagonal_square P i j i c 1
  have hj1 := pairMix_integrable_diagonal_square P i j j c 1
  have hiI := pairMix_integrable_diagonal_square P i j i c Complex.I
  have hjI := pairMix_integrable_diagonal_square P i j j c Complex.I
  have he := integral_congr_ae (μ := HaarProjection.unitaryHaar)
    (Filter.Eventually.of_forall (fun U : Matrix.unitaryGroup E ℂ =>
      pairMix_four_diagonal_squares hij c hc (orbit P U) (orbit_isHermitian hP U)))
  have hL1 := integral_add hi1 hj1
  have hL2 := integral_add (hi1.add hj1) hiI
  have hL3 := integral_add ((hi1.add hj1).add hiI) hjI
  simp only [Pi.add_apply] at hL1 hL2 hL3
  rw [hL3,hL2,hL1] at he
  rw [pairMix_integral_diagonal_square P hij i c hc 1 h1,
    pairMix_integral_diagonal_square P hij j c hc 1 h1,
    pairMix_integral_diagonal_square P hij i c hc Complex.I hI,
    pairMix_integral_diagonal_square P hij j c hc Complex.I hI] at he
  have hcross : Integrable (fun U : Matrix.unitaryGroup E ℂ =>
      2*(orbit P U i i).re*(orbit P U j j).re) HaarProjection.unitaryHaar := by
    simpa only [mul_assoc] using (integrable_diagCross P i j).const_mul 2
  have hR1 := integral_add (integrable_diagSecond P i) (integrable_diagSecond P j)
  have hR2 := integral_add ((integrable_diagSecond P i).add (integrable_diagSecond P j)) hcross
  have hR3 := integral_add (((integrable_diagSecond P i).add (integrable_diagSecond P j)).add hcross)
    ((integrable_entrySecond P i j).const_mul 2)
  simp only [Pi.add_apply] at hR1 hR2 hR3
  rw [hR3,hR2,hR1] at he
  simp_rw [mul_assoc,integral_const_mul] at he
  change diagSecond P i+diagSecond P j+diagSecond P i+diagSecond P j =
    diagSecond P i+diagSecond P j+2*diagCross P i j+2*entrySecond P i j at he
  rw [diagSecond_eq P j i] at he
  linarith

#print axioms diagSecond_eq_diagCross_add_entrySecond

end ProjectionChannels.HaarMoment
