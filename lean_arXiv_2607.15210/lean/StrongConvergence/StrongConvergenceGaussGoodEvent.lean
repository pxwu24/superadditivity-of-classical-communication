import StrongConvergence.StrongConvergenceGaussMarginals
import StrongConvergence.StrongConvergenceGaussNormTails
import StrongConvergence.StrongConvergenceSphereNet
import StrongConvergence.StrongConvergenceWhiteningLipschitz

open MeasureTheory GaussianRank Matrix StrongConvergence
open scoped NNReal ENNReal Matrix.L2OpNorm
noncomputable section
namespace ProjectionChannels.GaussConcentration

variable {E D : Type*} [Fintype E] [Fintype D] [DecidableEq D]

lemma matrixGaussian_unit_vector_upper (v : EuclideanSpace ℂ D) (hv : ‖v‖ = 1)
    (a : ℝ) (ha : 1 < a) :
    (matrixGaussian E D).real {G | a * Fintype.card E ≤ ‖Matrix.toEuclideanLin G v‖^2} ≤
      (a * Real.exp (1-a))^Fintype.card E := by
  have hm := map_measureReal_apply (μ := matrixGaussian E D)
    (continuous_matrix_vector_apply v).measurable
    (s := {x : EuclideanSpace ℂ E | a * Fintype.card E ≤ ‖x‖^2})
    (isClosed_le continuous_const (continuous_norm.pow 2)).measurableSet
  rw [matrixGaussian_unit_vector_law v hv] at hm
  have h := radialGaussian_complex_norm_sq_upper_real E a ha
  rw [hm] at h
  exact h

lemma matrixGaussian_unit_vector_lower (v : EuclideanSpace ℂ D) (hv : ‖v‖ = 1)
    (d : ℝ) (hd : 0 < d) :
    (matrixGaussian E D).real {G | ‖Matrix.toEuclideanLin G v‖^2 ≤ d * Fintype.card E} ≤
      (Real.exp 1 * d)^Fintype.card E := by
  have hm := map_measureReal_apply (μ := matrixGaussian E D)
    (continuous_matrix_vector_apply v).measurable
    (s := {x : EuclideanSpace ℂ E | ‖x‖^2 ≤ d * Fintype.card E})
    (isClosed_le (continuous_norm.pow 2) continuous_const).measurableSet
  rw [matrixGaussian_unit_vector_law v hv] at hm
  have h := radialGaussian_complex_norm_sq_lower_real E d hd
  rw [hm] at h
  exact h

/-- A quantitative operator-norm bound from the half-sphere net. -/
theorem matrixGaussian_opNorm_tail (a : ℝ) (ha : 1 < a) :
    (matrixGaussian E D).real {G | 2 * Real.sqrt (a * Fintype.card E) < ‖G‖} ≤
      5^(2*Fintype.card D) * (a * Real.exp (1-a))^Fintype.card E := by
  classical
  obtain ⟨s, hs, hc, hnet⟩ := exists_sphere_net (E := EuclideanSpace ℂ D) (1/2) (by norm_num)
  rw [complex_euclidean_finrank] at hc
  norm_num at hc
  let A : EuclideanSpace ℂ D → Set (Matrix E D ℂ) :=
    fun v => {G | a * Fintype.card E ≤ ‖Matrix.toEuclideanLin G v‖^2}
  have hsub : {G : Matrix E D ℂ | 2 * Real.sqrt (a * Fintype.card E) < ‖G‖} ⊆
      ⋃ v ∈ s, A v := by
    intro G hG
    by_contra hnot
    have hpoint : ∀ v ∈ s, ‖Matrix.toEuclideanLin G v‖ ≤ Real.sqrt (a * Fintype.card E) := by
      intro v hv
      have hn : ¬ G ∈ A v := fun hvG => hnot (Set.mem_iUnion₂.mpr ⟨v,hv,hvG⟩)
      dsimp [A] at hn
      exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (le_of_lt (not_le.mp hn))
    let T : EuclideanSpace ℂ D →L[ℝ] EuclideanSpace ℂ E :=
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G)).restrictScalars ℝ
    have ht := opNorm_le_of_sphere_net T s (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1) (Real.sqrt_nonneg _) hnet hpoint
    have hn : ‖T‖ = ‖G‖ := by
      dsimp [T]
      rw [ContinuousLinearMap.norm_restrictScalars]
      rfl
    rw [hn] at ht
    have ht' : ‖G‖ ≤ 2 * Real.sqrt (a * Fintype.card E) := by
      convert ht using 1
      ring
    exact (not_lt_of_ge ht') hG
  calc
    _ ≤ (matrixGaussian E D).real (⋃ v ∈ s, A v) := measureReal_mono hsub
    _ ≤ ∑ v ∈ s, (matrixGaussian E D).real (A v) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ s, (a * Real.exp (1-a))^Fintype.card E := by
      apply Finset.sum_le_sum
      intro v hv
      exact matrixGaussian_unit_vector_upper v (hs v hv) a ha
    _ = (s.card : ℝ) * (a * Real.exp (1-a))^Fintype.card E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- Before simplifying constants, the lower-frame failure probability is the
sum of an operator upper-tail and the union of lower-tail events on a net. -/
theorem matrixGaussian_lowerFrame_failure (a d ε : ℝ)
    (ha : 1 < a) (hd : 0 < d) (hε : 0 < ε) :
    (matrixGaussian E D).real
        {G | ¬ LowerFrame
          (Real.sqrt (d * Fintype.card E) - ε * (2 * Real.sqrt (a * Fintype.card E))) G} ≤
      5^(2*Fintype.card D) * (a * Real.exp (1-a))^Fintype.card E +
      (1+2/ε)^(2*Fintype.card D) * (Real.exp 1 * d)^Fintype.card E := by
  classical
  obtain ⟨s, hs, hc, hnet⟩ := exists_sphere_net (E := EuclideanSpace ℂ D) ε hε
  rw [complex_euclidean_finrank] at hc
  let A : EuclideanSpace ℂ D → Set (Matrix E D ℂ) :=
    fun v => {G | ‖Matrix.toEuclideanLin G v‖^2 ≤ d * Fintype.card E}
  let B : Set (Matrix E D ℂ) := {G | 2 * Real.sqrt (a * Fintype.card E) < ‖G‖}
  have hsub : {G : Matrix E D ℂ | ¬ LowerFrame
      (Real.sqrt (d * Fintype.card E) - ε * (2 * Real.sqrt (a * Fintype.card E))) G} ⊆
      B ∪ ⋃ v ∈ s, A v := by
    intro G hG
    by_contra hnot
    have hb : ‖G‖ ≤ 2 * Real.sqrt (a * Fintype.card E) := by
      exact le_of_not_gt (fun h => hnot (Or.inl h))
    have hpoint : ∀ v ∈ s, Real.sqrt (d * Fintype.card E) ≤ ‖Matrix.toEuclideanLin G v‖ := by
      intro v hv
      have hn : ¬ G ∈ A v := fun hvG => hnot (Or.inr (Set.mem_iUnion₂.mpr ⟨v,hv,hvG⟩))
      dsimp [A] at hn
      exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, (not_le.mp hn).le⟩
    apply hG
    intro x
    let T : EuclideanSpace ℂ D →L[ℝ] EuclideanSpace ℂ E :=
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G)).restrictScalars ℝ
    have ht := lower_norm_of_sphere_net T s hnet hpoint x
    have hn : ‖T‖ = ‖G‖ := by
      dsimp [T]
      rw [ContinuousLinearMap.norm_restrictScalars]
      rfl
    rw [hn] at ht
    exact (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg x)).trans ht
  calc
    _ ≤ (matrixGaussian E D).real (B ∪ ⋃ v ∈ s, A v) := measureReal_mono hsub
    _ ≤ (matrixGaussian E D).real B + (matrixGaussian E D).real (⋃ v ∈ s, A v) :=
      measureReal_union_le _ _
    _ ≤ _ := add_le_add (matrixGaussian_opNorm_tail a ha) (by
      calc
        _ ≤ ∑ v ∈ s, (matrixGaussian E D).real (A v) := measureReal_biUnion_finset_le _ _
        _ ≤ ∑ _v ∈ s, (Real.exp 1 * d)^Fintype.card E := by
          apply Finset.sum_le_sum
          intro v hv
          exact matrixGaussian_unit_vector_lower v (hs v hv) d hd
        _ = (s.card : ℝ) * (Real.exp 1 * d)^Fintype.card E := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity))


/-- A convenient positive lower-frame constant. Its numerical size is not
optimized; only positivity and dimension-independent exponential tails matter. -/
def gaussianFrameConstant (t : ℝ) : ℝ := 8 * Real.exp (- (10 / (1-t)))

lemma gaussianFrameConstant_pos (t : ℝ) : 0 < gaussianFrameConstant t := by
  unfold gaussianFrameConstant
  positivity

lemma upper_net_numeric_bound : (25:ℝ) * (128 * Real.exp (1-128)) ≤ Real.exp (-1) := by
  have hex : (64:ℝ) ≤ Real.exp 63 := by linarith [Real.add_one_le_exp (63:ℝ)]
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 64) hex 2
  rw [← Real.exp_nat_mul] at hs
  norm_num at hs
  have hmul := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-127)).le
  have he : Real.exp 126 * Real.exp (-127) = Real.exp (-1) := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hmul
  norm_num
  nlinarith [Real.exp_pos (-127)]

lemma matrixGaussian_lowerFrame_failure_real (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t < 1)
    (hdim : (Fintype.card D : ℝ) ≤ t * Fintype.card E) :
    (matrixGaussian E D).real
      {G | ¬ LowerFrame (gaussianFrameConstant t * Real.sqrt (Fintype.card E)) G} ≤
        2 * Real.exp (-(Fintype.card E : ℝ)) := by
  let q : ℝ := 10/(1-t)
  let ε : ℝ := Real.exp (-q)
  let d : ℝ := (32*ε)^2
  have hq : 0 < q := div_pos (by norm_num) (sub_pos.mpr ht1)
  have hε : 0 < ε := Real.exp_pos _
  have hd : 0 < d := by dsimp [d]; positivity
  have hqeq : q*(1-t)=10 := div_mul_cancel₀ _ (sub_pos.mpr ht1).ne'
  have hbound := matrixGaussian_lowerFrame_failure (E := E) (D := D)
    128 d ε (by norm_num) hd hε
  have hcoef : gaussianFrameConstant t * Real.sqrt (Fintype.card E) ≤
      Real.sqrt (d * Fintype.card E) - ε * (2 * Real.sqrt (128 * Fintype.card E)) := by
    rw [Real.sqrt_mul hd.le, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 128)]
    have hs : Real.sqrt d = 32*ε := by
      dsimp [d]
      rw [Real.sqrt_sq (by positivity)]
    have h128 : Real.sqrt 128 ≤ 12 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    rw [hs]
    change 8*ε * Real.sqrt (Fintype.card E) ≤ _
    nlinarith [Real.sqrt_nonneg (Fintype.card E),
      mul_le_mul_of_nonneg_right h128 (by positivity : 0 ≤ ε * Real.sqrt (Fintype.card E))]
  have hmono : (matrixGaussian E D).real
      {G | ¬ LowerFrame (gaussianFrameConstant t * Real.sqrt (Fintype.card E)) G} ≤
      (matrixGaussian E D).real
        {G | ¬ LowerFrame
          (Real.sqrt (d * Fintype.card E) - ε * (2 * Real.sqrt (128 * Fintype.card E))) G} := by
    exact measureReal_mono (fun G hG h => hG (h.mono hcoef))
  have hdimN : Fintype.card D ≤ Fintype.card E := by
    have hn : (Fintype.card D : ℝ) ≤ Fintype.card E :=
      hdim.trans (mul_le_of_le_one_left (Nat.cast_nonneg _) ht1.le)
    exact_mod_cast hn
  have hupper : (5:ℝ)^(2*Fintype.card D) *
        (128 * Real.exp (1-128))^Fintype.card E ≤ Real.exp (-(Fintype.card E : ℝ)) := by
    calc
      _ ≤ (25:ℝ)^Fintype.card E * (128 * Real.exp (1-128))^Fintype.card E := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [pow_mul]
        norm_num only [show (5:ℝ)^2=25 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) hdimN
      _ = (25 * (128 * Real.exp (1-128)))^Fintype.card E := (mul_pow ..).symm
      _ ≤ (Real.exp (-1))^Fintype.card E :=
        pow_le_pow_left₀ (by positivity) upper_net_numeric_bound _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hbase : 1+2/ε ≤ Real.exp (2+q) := by
    have heq : ε⁻¹ = Real.exp q := by dsimp [ε]; rw [Real.exp_neg, inv_inv]
    have h1 : (1:ℝ) ≤ Real.exp q := Real.one_le_exp hq.le
    have h3 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
    rw [div_eq_mul_inv, heq, Real.exp_add]
    nlinarith [Real.exp_pos q]
  have h1024 : (1024:ℝ) ≤ Real.exp 10 := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 10
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hdexp : d = 1024 * Real.exp (-2*q) := by
    dsimp [d, ε]
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num
  have htailbase : Real.exp 1 * d ≤ Real.exp (11-2*q) := by
    calc
      _ = 1024 * Real.exp (1-2*q) := by
        rw [hdexp, mul_left_comm, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp 10 * Real.exp (1-2*q) :=
        mul_le_mul_of_nonneg_right h1024 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlower : (1+2/ε)^(2*Fintype.card D) * (Real.exp 1*d)^Fintype.card E ≤
      Real.exp (-(Fintype.card E : ℝ)) := by
    calc
      _ ≤ (Real.exp (2+q))^(2*Fintype.card D) *
          (Real.exp (11-2*q))^Fintype.card E := by
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase _)
          (pow_le_pow_left₀ (by positivity) htailbase _) (by positivity) (by positivity)
      _ = Real.exp ((2*Fintype.card D : ℝ)*(2+q) +
          (Fintype.card E : ℝ)*(11-2*q)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        rfl
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hs := mul_le_mul_of_nonneg_right hdim (by positivity : 0 ≤ 2*(2+q))
        have ht : t*(2*(2+q))+(11-2*q) ≤ -1 := by nlinarith
        have hn := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (Fintype.card E) : (0:ℝ) ≤ _)
        nlinarith
  apply hmono.trans
  apply hbound.trans
  calc
    _ ≤ Real.exp (-(Fintype.card E : ℝ)) + Real.exp (-(Fintype.card E : ℝ)) :=
      add_le_add hupper hlower
    _ = _ := by ring

/-- Gaussian rectangular matrices have a dimension-uniform positive lower
frame with an exponentially small exceptional set whenever the aspect ratio
is bounded strictly below one. -/
theorem matrixGaussian_lowerFrame_failure_exp (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hdim : (Fintype.card D : ℝ) ≤ t * Fintype.card E) :
    matrixGaussian E D
      {G | ¬ LowerFrame (gaussianFrameConstant t * Real.sqrt (Fintype.card E)) G} ≤
        ENNReal.ofReal (2 * Real.exp (-(Fintype.card E : ℝ))) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact matrixGaussian_lowerFrame_failure_real t ht0 ht1 hdim


/-- Coordinate form of the good-event estimate, directly on the radial
Gaussian used by the Gaussian concentration theorem. -/
theorem radialGaussian_lowerFrame_failure_exp (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hdim : (Fintype.card D : ℝ) ≤ t * Fintype.card E) :
    radialGaussian (EuclideanSpace ℂ (E × D))
      {x | ¬ LowerFrame (gaussianFrameConstant t * Real.sqrt (Fintype.card E))
        (matrixCoordinates E D x)} ≤
        ENNReal.ofReal (2 * Real.exp (-(Fintype.card E : ℝ))) := by
  have h := matrixGaussian_lowerFrame_failure_exp (E := E) (D := D) t ht0 ht1 hdim
  change ((radialGaussian _).map (matrixCoordinates E D)) _ ≤ _ at h
  have hm : MeasurableSet {G : Matrix E D ℂ |
      ¬ LowerFrame (gaussianFrameConstant t * Real.sqrt (Fintype.card E)) G} :=
    (isClosed_lowerFrame _).measurableSet.compl
  rw [Measure.map_apply (matrixCoordinates E D).continuous.measurable hm] at h
  exact h

end ProjectionChannels.GaussConcentration

#print axioms ProjectionChannels.GaussConcentration.matrixGaussian_lowerFrame_failure_exp


#print axioms ProjectionChannels.GaussConcentration.radialGaussian_lowerFrame_failure_exp
