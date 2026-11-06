import StrongConvergence.StrongConvergenceHaarVarianceResult

/-! Genuine Haar second-compression moments. Mixed off-diagonal products are
annihilated by an actual coordinate sign-flip unitary and Haar invariance. -/
open Matrix MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace ProjectionChannels.HaarMoment
variable {E : Type*} [Fintype E] [DecidableEq E]

def signFlip (r : E) : Matrix E E ℂ :=
  Matrix.diagonal (fun i => if i=r then (-1:ℂ) else 1)

lemma signFlip_star (r : E) : (signFlip r).conjTranspose=signFlip r := by
  ext i j
  simp [signFlip,Matrix.conjTranspose_apply,Matrix.diagonal_apply]
  split_ifs <;> simp_all

lemma signFlip_square (r : E) : signFlip r*signFlip r=1 := by
  rw [signFlip,Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply,Matrix.one_apply]
  split_ifs <;> simp_all

def signFlipUnitary (r : E) : Matrix.unitaryGroup E ℂ :=
  ⟨signFlip r,Matrix.mem_unitaryGroup_iff'.mpr (by rw [Matrix.star_eq_conjTranspose,signFlip_star,signFlip_square])⟩

lemma signFlip_conjugate_entry (M : Matrix E E ℂ) (r i j : E) :
    (signFlip r*M*signFlip r) i j=
      (if i=r then (-1:ℂ) else 1)*M i j*(if j=r then (-1:ℂ) else 1) := by
  simp [signFlip,Matrix.diagonal_mul,Matrix.mul_diagonal]

lemma orbit_signFlip (P : Matrix E E ℂ) (U : Matrix.unitaryGroup E ℂ) (r i j : E) :
    orbit P (signFlipUnitary r*U) i j=
      (if i=r then (-1:ℂ) else 1)*orbit P U i j*(if j=r then (-1:ℂ) else 1) := by
  have hh : orbit P (signFlipUnitary r*U)=signFlip r*orbit P U*signFlip r := by
    simp only [orbit,Matrix.UnitaryGroup.mul_val,signFlipUnitary,Matrix.conjTranspose_mul,
      signFlip_star,Matrix.mul_assoc]
  rw [hh,signFlip_conjugate_entry]

/-- Four distinct indices give a vanishing mixed product. No moment formula
or freeness hypothesis is used: one sign flip negates the integrand. -/
theorem integral_disjoint_entry_product (P : Matrix E E ℂ)
    (a b c d : E) (hab : a≠b) (hac : a≠c) (had : a≠d) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (orbit P U a b*orbit P U c d).re ∂HaarProjection.unitaryHaar)=0 := by
  have hh := integral_mul_left_eq_self (μ:=HaarProjection.unitaryHaar)
    (fun U : Matrix.unitaryGroup E ℂ => (orbit P U a b*orbit P U c d).re)
    (signFlipUnitary a)
  simp only [orbit_signFlip,if_pos rfl,if_neg hab.symm,if_neg hac.symm,if_neg had.symm,
    neg_one_mul,mul_one,one_mul,neg_mul,Complex.neg_re,ite_true,integral_neg] at hh
  linarith

lemma integrable_entry_product (P : Matrix E E ℂ) (a b c d : E) :
    Integrable (fun U : Matrix.unitaryGroup E ℂ => (orbit P U a b*orbit P U c d).re)
      HaarProjection.unitaryHaar :=
  (Complex.continuous_re.comp ((continuous_orbit_entry P a b).mul
    (continuous_orbit_entry P c d))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma integral_diagonal_product {P : Matrix E E ℂ} (hP : P.IsHermitian) (a b : E) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (orbit P U a a*orbit P U b b).re ∂HaarProjection.unitaryHaar)=diagCross P a b := by
  unfold diagCross
  congr 1
  funext U
  rw [← (orbit_isHermitian hP U).coe_re_apply_self a,
    ← (orbit_isHermitian hP U).coe_re_apply_self b]
  simp

lemma integral_reversed_product {P : Matrix E E ℂ} (hP : P.IsHermitian) (a b : E) :
    (∫ U : Matrix.unitaryGroup E ℂ,
      (orbit P U a b*orbit P U b a).re ∂HaarProjection.unitaryHaar)=entrySecond P a b := by
  unfold entrySecond
  congr 1
  funext U
  rw [← (orbit_isHermitian hP U).apply b a]
  simp [Complex.star_def,Complex.mul_conj]

variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A] [DecidableEq K]

/-- The precise covariance pattern needed by a diagonal block compression. -/
theorem integral_block_entry_product {P : Matrix (A×K) (A×K) ℂ}
    (hP : P.IsHermitian) (x y : A×K) (hxy : x≠y) (u v : A) (i j : K) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      (orbit P U (u,i) (v,i)*orbit P U (v,j) (u,j)).re ∂HaarProjection.unitaryHaar)=
      (if u=v then diagCross P x y else 0)+
      (if i=j then entrySecond P x y else 0)+
      (if u=v ∧ i=j then diagSecond P x-diagCross P x y-entrySecond P x y else 0) := by
  by_cases huv : u=v
  · subst v
    by_cases hij : i=j
    · subst j
      rw [integral_diagonal_product hP,diagCross_self,diagSecond_eq P (u,i) x]
      simp
    · rw [integral_diagonal_product hP,
        diagCross_eq P (show (u,i)≠(u,j) by simp [hij]) hxy]
      simp [hij]
  · by_cases hij : i=j
    · subst j
      rw [integral_reversed_product hP,
        entrySecond_eq P (show (u,i)≠(v,i) by simp [huv]) hxy]
      simp [huv]
    · rw [integral_disjoint_entry_product P (u,i) (v,i) (v,j) (u,j)
        (by simp [huv]) (by simp [huv]) (by simp [hij])]
      simp [huv,hij]

lemma compression_entry (P : Matrix (A×K) (A×K) ℂ) (a : K → ℝ) (u v : A) :
    blockCompression (diagonalBlock P) a u v=∑ i,(a i:ℂ)*P (u,i) (v,i) := by
  simp [blockCompression,diagonalBlock,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]

lemma compression_second_trace (P : Matrix (A×K) (A×K) ℂ) (a : K → ℝ) :
    (Matrix.trace ((blockCompression (diagonalBlock P) a)^2)).re=
      ∑ u,∑ v,∑ i,∑ j,a i*a j*(P (u,i) (v,i)*P (v,j) (u,j)).re := by
  simp only [pow_two,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,compression_entry,
    Finset.sum_mul,Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re,Complex.mul_im]
  ring

lemma compression_covariance_sum (a : K → ℝ) (α β γ : ℝ) :
    (∑ u:A,∑ v:A,∑ i:K,∑ j:K,a i*a j*
      ((if u=v then β else 0)+(if i=j then γ else 0)+
        (if u=v ∧ i=j then α-β-γ else 0)))=
      (Fintype.card A:ℝ)*β*(∑ i,a i)^2+
      (Fintype.card A:ℝ)*((α-β)+(Fintype.card A-1)*γ)*(∑ i,(a i)^2) := by
  simp only [mul_add,Finset.sum_add_distrib,mul_ite,mul_zero,ite_and]
  simp only [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_ite_irrel,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp_rw [← pow_two]
  ring_nf
  simp <;> ring

/-- Exact expected second trace in terms of the genuine Haar pair moments. -/
theorem integral_compression_second_trace {P : Matrix (A×K) (A×K) ℂ}
    (hP : P.IsHermitian) (x y : A×K) (hxy : x≠y) (a : K → ℝ) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      (Matrix.trace ((blockCompression (diagonalBlock (orbit P U)) a)^2)).re
      ∂HaarProjection.unitaryHaar)=
      (Fintype.card A:ℝ)*diagCross P x y*(∑ i,a i)^2+
      (Fintype.card A:ℝ)*((diagSecond P x-diagCross P x y)+
        (Fintype.card A-1)*entrySecond P x y)*(∑ i,(a i)^2) := by
  have hi (u v : A) (i j : K) : Integrable
      (fun U : Matrix.unitaryGroup (A×K) ℂ =>
        a i*a j*(orbit P U (u,i) (v,i)*orbit P U (v,j) (u,j)).re)
      HaarProjection.unitaryHaar :=
    (integrable_entry_product P (u,i) (v,i) (v,j) (u,j)).const_mul _
  simp_rw [compression_second_trace]
  rw [integral_finset_sum _ (fun u _=> integrable_finset_sum _ (fun v _=>
    integrable_finset_sum _ (fun i _=> integrable_finset_sum _ (fun j _=>hi u v i j))))]
  simp_rw [integral_finset_sum _ (fun v _=>integrable_finset_sum _
    (fun i _=>integrable_finset_sum _ (fun j _=>hi _ v i j)))]
  simp_rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>hi _ _ i j))]
  simp_rw [integral_finset_sum _ (fun j _=>hi _ _ _ j),integral_const_mul,
    integral_block_entry_product hP x y hxy]
  exact compression_covariance_sum a _ _ _

/-- Exact second moment of a Haar-random projection compression. This is a
finite Haar integral identity, with no asymptotic-freeness input. -/
theorem integral_compression_second_trace_formula {P : Matrix (A×K) (A×K) ℂ}
    (hP : P.IsHermitian) (hPP : P*P=P) (hN : 1<Fintype.card (A×K)) (a : K → ℝ) :
    (∫ U : Matrix.unitaryGroup (A×K) ℂ,
      (Matrix.trace ((blockCompression (diagonalBlock (orbit P U)) a)^2)).re
      ∂HaarProjection.unitaryHaar)=
      (Fintype.card A:ℝ)*
        ((Matrix.trace P).re*((Fintype.card (A×K):ℝ)*(Matrix.trace P).re-1)/
          ((Fintype.card (A×K):ℝ)*((Fintype.card (A×K):ℝ)^2-1)))*(∑ i,a i)^2+
      (Fintype.card A:ℝ)^2*
        ((Matrix.trace P).re*((Fintype.card (A×K):ℝ)-(Matrix.trace P).re)/
          ((Fintype.card (A×K):ℝ)*((Fintype.card (A×K):ℝ)^2-1)))*(∑ i,(a i)^2) := by
  obtain ⟨x,y,hxy⟩ := Fintype.exists_pair_of_one_lt_card hN
  rw [integral_compression_second_trace hP x y hxy,
    diagSecond_eq_diagCross_add_entrySecond hP hxy,
    diagCross_eq_formula hP hPP hN hxy,entrySecond_eq_formula hP hPP hN hxy]
  ring

lemma continuous_compression_second_trace (P : Matrix (A×K) (A×K) ℂ) (a : K → ℝ) :
    Continuous (fun U : Matrix.unitaryGroup (A×K) ℂ =>
      (Matrix.trace ((blockCompression (diagonalBlock (orbit P U)) a)^2)).re) := by
  simp_rw [compression_second_trace]
  apply continuous_finset_sum
  intro u _
  apply continuous_finset_sum
  intro v _
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul (Complex.continuous_re.comp
    ((continuous_orbit_entry P (u,i) (v,i)).mul (continuous_orbit_entry P (v,j) (u,j))))

end ProjectionChannels.HaarMoment

namespace ProjectionChannels.Canonical
open HaarMoment

theorem integral_compression_second_trace_formula {k : ℕ} {t : ℝ}
    (hk : 2≤k) (ht0 : 0≤t) (ht1 : t≤1) (n : ℕ) (a : Fin k → ℝ) :
    (∫ ω, (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^2)).re
      ∂probability k)=
      (n+1)*((rankSequence k t n:ℝ)*((k*(n+1))*(rankSequence k t n:ℝ)-1)/
        ((k*(n+1))*((k*(n+1))^2-1)))*(∑ i,a i)^2+
      (n+1)^2*((rankSequence k t n:ℝ)*((k*(n+1))-(rankSequence k t n:ℝ))/
        ((k*(n+1))*((k*(n+1))^2-1)))*(∑ i,(a i)^2) := by
  let f : Matrix.unitaryGroup (Index k n) ℂ → ℝ := fun U =>
    (Matrix.trace ((blockCompression (diagonalBlock
      (HaarMoment.orbit (baseProjection k t n) U)) a)^2)).re
  have hmp := evaluation_measurePreserving k n
  have hmap := integral_map (μ:=probability k) hmp.measurable.aemeasurable
    (f:=f) (continuous_compression_second_trace (baseProjection k t n) a).aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  change (∫ ω,f (evaluation k n ω) ∂probability k)=_
  rw [← hmap]
  have hN : 1<Fintype.card (Fin (n+1)×Fin k) := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    nlinarith
  rw [HaarMoment.integral_compression_second_trace_formula
    (baseProjection_isHermitian k t n) (baseProjection_idempotent k t n) hN a]
  rw [ProjectionStrongConvergence.trace_projection_eq_rank _ (baseProjection_idempotent k t n),
    baseProjection_rank ht0 ht1]
  simp only [Complex.natCast_re,Fintype.card_fin,Fintype.card_prod,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  ring

private lemma second_coefficients_normalized (d n k x y : ℝ)
    (hn : n≠0) (hk : k≠0) (hden : (k*n)^2-1≠0) :
    (n*(d*(k*n*d-1)/(k*n*((k*n)^2-1)))*x^2+
      n^2*(d*(k*n-d)/(k*n*((k*n)^2-1)))*y)/n=
      (d/(k*n))*(d/(k*n)-(1/(k*n))^2)/(1-(1/(k*n))^2)*x^2+
      (d/(k*n))*(1-d/(k*n))/(k*(1-(1/(k*n))^2))*y := by
  have hkn : k*n≠0 := mul_ne_zero hk hn
  have he : 1-(1/(k*n))^2≠0 := by
    intro he
    apply hden
    field_simp [hkn] at he
    nlinarith
  field_simp [hn,hk,hden,he]
  <;> ring

theorem normalized_second_moment_formula {k : ℕ} {t : ℝ}
    (hk : 2≤k) (ht0 : 0≤t) (ht1 : t≤1) (n : ℕ) (a : Fin k → ℝ) :
    (∫ ω, (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^2)).re
      ∂probability k)/((n:ℝ)+1)=
      ((rankSequence k t n:ℝ)/(k*(n+1)))*
        ((rankSequence k t n:ℝ)/(k*(n+1))-(1/(k*(n+1)))^2)/
        (1-(1/(k*(n+1)))^2)*(∑ i,a i)^2+
      ((rankSequence k t n:ℝ)/(k*(n+1)))*
        (1-(rankSequence k t n:ℝ)/(k*(n+1)))/
        (k*(1-(1/(k*(n+1)))^2))*(∑ i,(a i)^2) := by
  rw [integral_compression_second_trace_formula hk ht0 ht1]
  apply second_coefficients_normalized
  · positivity
  · have hk' : (2:ℝ)≤k := by exact_mod_cast hk
    linarith
  · have hk' : (2:ℝ)≤k := by exact_mod_cast hk
    have hn' : (0:ℝ)≤n := by positivity
    have hh : 1<(k:ℝ)*(n+1) := by nlinarith
    nlinarith [sq_nonneg ((k:ℝ)*(n+1)-1)]

/-- The expected second empirical moment of the actual canonical Haar
compression has the Bernoulli free-compression normalization. No strong
convergence or free-probability statement is assumed. -/
theorem normalized_second_moment_tendsto {k : ℕ} {t : ℝ}
    (hk : 2≤k) (ht0 : 0≤t) (ht1 : t≤1) (a : Fin k → ℝ) :
    Tendsto (fun n : ℕ => (∫ ω,
      (Matrix.trace ((blockCompression (diagonalBlock (projection k t ω n)) a)^2)).re
        ∂probability k)/((n:ℝ)+1)) atTop
      (𝓝 (t^2*(∑ i,a i)^2+t*(1-t)/(k:ℝ)*(∑ i,(a i)^2))) := by
  have hk0 : 0<k := by omega
  have hkR : (k:ℝ)≠0 := by positivity
  have hq := rank_density_tendsto hk0 ht0
  have he : Tendsto (fun n : ℕ => 1/((k:ℝ)*(n+1))) atTop (𝓝 (0:ℝ)) := by
    simpa only [div_div,mul_comm,zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.div_const (k:ℝ))
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 (1:ℝ)) := tendsto_const_nhds
  have hβ := (hq.mul (hq.sub (he.pow 2))).div (h1.sub (he.pow 2)) (by norm_num)
  have hγ := (hq.mul (h1.sub hq)).div
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (k:ℝ)) atTop (𝓝 (k:ℝ))).mul (h1.sub (he.pow 2))) (by simpa using hkR)
  have hh := (hβ.mul_const ((∑ i,a i)^2)).add (hγ.mul_const (∑ i,(a i)^2))
  simp_rw [normalized_second_moment_formula hk ht0 ht1]
  simpa only [Pi.div_apply,zero_pow (by omega : 2≠0),sub_zero,mul_one,div_one,← pow_two] using hh

end ProjectionChannels.Canonical

#print axioms ProjectionChannels.HaarMoment.integral_disjoint_entry_product
#print axioms ProjectionChannels.HaarMoment.integral_block_entry_product
#print axioms ProjectionChannels.HaarMoment.integral_compression_second_trace_formula
#print axioms ProjectionChannels.Canonical.integral_compression_second_trace_formula
#print axioms ProjectionChannels.Canonical.normalized_second_moment_tendsto
