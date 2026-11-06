import Entropy.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Deterministic support convergence for the output-space theorem

The actual random matrix spectral limit and the matrix support-function
identifications are not assumptions disguised as conclusions: they are the
explicit inputs `hconv`, `hthreshold`, `hratio`, and `hlimit` below. This file
proves the strict sign argument needed to pass from spectral convergence to
normalized output support convergence, and the compact finite-net step.
-/

open Filter Set
open scoped Topology

namespace OutputSpaceVerification

/-- A positive denominator turns a maximum of ratios into strict sign
brackets for the corresponding family of unnormalized linear objectives. -/
theorem ratio_support_brackets
    {X : Type*} (D : Set X) (a b : X → ℝ) (f : ℝ → ℝ) (r m : ℝ)
    (hm : 0 < m) (hb : ∀ x ∈ D, m ≤ b x)
    (hratio : IsGreatest ((fun x => a x / b x) '' D) r)
    (hlimit : ∀ z, IsGreatest ((fun x => a x - z * b x) '' D) (f z))
    {ε : ℝ} (hε : 0 < ε) :
    f (r + ε) ≤ -ε * m ∧ ε * m ≤ f (r - ε) := by
  obtain ⟨u, hu, hur⟩ := hratio.1
  have hbpos : ∀ x ∈ D, 0 < b x := fun x hx => hm.trans_le (hb x hx)
  have hupper : ∀ x ∈ D, a x ≤ r * b x := by
    intro x hx
    exact (div_le_iff₀ (hbpos x hx)).mp (hratio.2 ⟨x, hx, rfl⟩)
  have heq : a u = r * b u := (div_eq_iff (hbpos u hu).ne').mp hur
  constructor
  · obtain ⟨v, hv, hvf⟩ := (hlimit (r + ε)).1
    rw [← hvf]
    dsimp only
    nlinarith [hupper v hv, mul_le_mul_of_nonneg_left (hb v hv) hε.le]
  · have hlo := (hlimit (r - ε)).2 (show a u - (r - ε) * b u ∈
        (fun x => a x - (r - ε) * b x) '' D from ⟨u, hu, rfl⟩)
    nlinarith [hb u hu]

/-- Pointwise convergence at the two strict brackets forces convergence
of the generalized-eigenvalue threshold. Unlike an interchange of infimum
and limit, this theorem needs no uniform convergence in the threshold. -/
theorem threshold_tendsto_of_strict_brackets
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (h : ℕ → ℝ) (r : ℝ)
    (hthreshold : ∀ n z, h n ≤ z ↔ f n z ≤ 0)
    (hconv : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z)))
    (hbracket : ∀ ε > 0, g (r + ε) < 0 ∧ 0 < g (r - ε)) :
    Tendsto h atTop (𝓝 r) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  obtain ⟨hplus, hminus⟩ := hbracket (ε / 2) he
  have hp : ∀ᶠ n in atTop, f n (r + ε / 2) < 0 :=
    (hconv (r + ε / 2)).eventually (gt_mem_nhds hplus)
  have hm : ∀ᶠ n in atTop, 0 < f n (r - ε / 2) :=
    (hconv (r - ε / 2)).eventually (lt_mem_nhds hminus)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hp.and hm)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hpn, hmn⟩ := hN n hn
  have hu : h n ≤ r + ε / 2 := (hthreshold n _).mpr hpn.le
  have hl : r - ε / 2 < h n := by
    by_contra h
    have := (hthreshold n _).mp (le_of_not_gt h)
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The deterministic diagonal step of the output-space theorem. Set
`a u = ∑ i, hᵢ uᵢ`, `b u = ∑ i, uᵢ`, `D = 𝒟_{k,t}`, and let `f n z`
be the top eigenvalue of `Sₙ(h-z1)`. The maximum of ratios is the limiting
support function. -/
theorem normalized_support_tendsto
    {X : Type*} (D : Set X) (a b : X → ℝ)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (h : ℕ → ℝ) (r m : ℝ)
    (hm : 0 < m) (hb : ∀ x ∈ D, m ≤ b x)
    (hratio : IsGreatest ((fun x => a x / b x) '' D) r)
    (hlimit : ∀ z, IsGreatest ((fun x => a x - z * b x) '' D) (g z))
    (hthreshold : ∀ n z, h n ≤ z ↔ f n z ≤ 0)
    (hconv : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) :
    Tendsto h atTop (𝓝 r) := by
  apply threshold_tendsto_of_strict_brackets f g h r hthreshold hconv
  intro ε hε
  obtain ⟨hp, hn⟩ := ratio_support_brackets D a b g r m hm hb hratio hlimit hε
  constructor <;> nlinarith [mul_pos hε hm]

/-- Common Lipschitz bounds extend pointwise convergence from a dense
parameter set. The space can in particular be the operator-norm unit ball. -/
theorem pointwise_tendsto_of_dense
    {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hdense : Dense s)
    (hf : ∀ n x y, dist (f n x) (f n y) ≤ dist x y)
    (hg : ∀ x y, dist (g x) (g y) ≤ dist x y)
    (hconv : ∀ q ∈ s, Tendsto (fun n => f n q) atTop (𝓝 (g q)))
    (x : X) : Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨q, hqs, hq⟩ := hdense.exists_dist_lt x (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv q hqs) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hmiddle := hN n hn
  have hleft := hf n x q
  have hright := hg q x
  have hqx : dist q x < ε / 3 := by simpa [dist_comm] using hq
  calc
    dist (f n x) (g x) ≤ dist (f n x) (f n q) + dist (f n q) (g x) :=
      dist_triangle _ _ _
    _ ≤ dist (f n x) (f n q) + (dist (f n q) (g q) + dist (g q) (g x)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε := by linarith

/-- Pointwise convergence of uniformly 1-Lipschitz functions on a compact
set is uniform. This is precisely the finite-net argument in Step 4. -/
theorem uniform_tendsto_on_compact
    {X : Type*} [PseudoMetricSpace X] (K : Set X) (hK : IsCompact K)
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (hf : ∀ n, ∀ x ∈ K, ∀ y ∈ K, dist (f n x) (f n y) ≤ dist x y)
    (hg : ∀ x ∈ K, ∀ y ∈ K, dist (g x) (g y) ≤ dist x y)
    (hconv : ∀ x ∈ K, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ K, |f n x - g x| < ε := by
  intro ε hε
  obtain ⟨t, htK, htfin, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 3 by positivity)
  have hpoint : ∀ q ∈ t, ∀ᶠ n in atTop, dist (f n q) (g q) < ε / 3 := by
    intro q hq
    exact (hconv q (htK hq)).eventually (Metric.ball_mem_nhds _ (by positivity))
  have hall : ∀ᶠ n in atTop, ∀ q ∈ t, dist (f n q) (g q) < ε / 3 :=
    (eventually_all_finite htfin).mpr hpoint
  obtain ⟨N, hN⟩ := eventually_atTop.1 hall
  refine ⟨N, fun n hn x hx => ?_⟩
  obtain ⟨q, hqt, hqx⟩ := mem_iUnion₂.mp (hcover hx)
  have hdist : dist x q < ε / 3 := hqx
  have hleft := hf n x hx q (htK hqt)
  have hright := hg q (htK hqt) x hx
  have hmiddle := hN n hn q hqt
  rw [dist_comm q x] at hright
  rw [← Real.dist_eq]
  calc
    dist (f n x) (g x) ≤ dist (f n x) (f n q) + dist (f n q) (g x) :=
      dist_triangle _ _ _
    _ ≤ dist (f n x) (f n q) + (dist (f n q) (g q) + dist (g q) (g x)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε := by linarith

/-- Uniformly continuous objectives have convergent attained minima under
Hausdorff convergence of nonempty compact feasible sets. No convexity is
needed for this step. -/
theorem attained_minimum_tendsto_of_hausdorff
    {X : Type*} [PseudoMetricSpace X] (D K : Set X) (C : ℕ → Set X)
    (F : X → ℝ) (m : ℕ → ℝ) (v : ℝ)
    (hK : IsCompact K) (hC : ∀ n, IsCompact (C n))
    (hKD : K ⊆ D) (hCD : ∀ n, C n ⊆ D)
    (hF : UniformContinuousOn F D)
    (hm : ∀ n, IsLeast (F '' C n) (m n))
    (hv : IsLeast (F '' K) v)
    (hhaus : Tendsto (fun n => Metric.hausdorffDist (C n) K) atTop (𝓝 0)) :
    Tendsto m atTop (𝓝 v) := by
  obtain ⟨y, hy, hyv⟩ := hv.1
  have hneK : K.Nonempty := ⟨y, hy⟩
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hF ε hε
  have hh : ∀ᶠ n in atTop, Metric.hausdorffDist (C n) K < δ :=
    hhaus.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hh
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨x, hx, hxm⟩ := (hm n).1
  have hfin := Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded
    (show (C n).Nonempty from ⟨x, hx⟩) hneK (hC n).isBounded hK.isBounded
  obtain ⟨y', hy', hxy'⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hx (hN n hn) hfin
  obtain ⟨x', hx', hx'y⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hy (hN n hn) hfin
  have hlow := hv.2 (show F y' ∈ F '' K from ⟨y', hy', rfl⟩)
  have hupp := (hm n).2 (show F x' ∈ F '' C n from ⟨x', hx', rfl⟩)
  have hab1 := hmod x (hCD n hx) y' (hKD hy') hxy'
  have hab2 := hmod x' (hCD n hx') y (hKD hy) hx'y
  rw [Real.dist_eq, abs_lt] at hab1 hab2 ⊢
  rw [hxm] at hab1
  rw [hyv] at hab2
  constructor <;> linarith

/-- The entropy-corollary mechanism stated directly for the infimum of
an objective. Compactness and continuity prove that these infima are
attained; minimum attainment is not assumed. -/
theorem minimum_value_tendsto_of_hausdorff
    {X : Type*} [PseudoMetricSpace X] (D K : Set X) (C : ℕ → Set X)
    (F : X → ℝ)
    (hK : IsCompact K) (hneK : K.Nonempty)
    (hC : ∀ n, IsCompact (C n)) (hneC : ∀ n, (C n).Nonempty)
    (hKD : K ⊆ D) (hCD : ∀ n, C n ⊆ D)
    (hF : UniformContinuousOn F D)
    (hhaus : Tendsto (fun n => Metric.hausdorffDist (C n) K) atTop (𝓝 0)) :
    Tendsto (fun n => sInf (F '' C n)) atTop (𝓝 (sInf (F '' K))) := by
  apply attained_minimum_tendsto_of_hausdorff D K C F _ _ hK hC hKD hCD hF
  · intro n
    exact ((hC n).image_of_continuousOn (hF.continuousOn.mono (hCD n))).isLeast_sInf
      ((hneC n).image F)
  · exact (hK.image_of_continuousOn (hF.continuousOn.mono hKD)).isLeast_sInf
      (hneK.image F)
  · exact hhaus

/-- The countable probability-one intersection and the dense/compact
extension are performed in Lean. No uncountable intersection of events is
used. This is the final almost-sure uniformity step of the paper. -/
theorem ae_uniform_tendsto_on_compact_of_dense
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (μ : MeasureTheory.Measure Ω) (s K : Set X)
    (hcount : s.Countable) (hdense : Dense s) (hK : IsCompact K)
    (f : Ω → ℕ → X → ℝ) (g : X → ℝ)
    (hf : ∀ ω n x y, dist (f ω n x) (f ω n y) ≤ dist x y)
    (hg : ∀ x y, dist (g x) (g y) ≤ dist x y)
    (hconv : ∀ q ∈ s, ∀ᵐ ω ∂μ,
      Tendsto (fun n => f ω n q) atTop (𝓝 (g q))) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ K, |f ω n x - g x| < ε := by
  letI : Countable s := hcount.to_subtype
  have hsim : ∀ᵐ ω ∂μ, ∀ q : s,
      Tendsto (fun n => f ω n q) atTop (𝓝 (g q)) :=
    MeasureTheory.ae_all_iff.2 (fun q => hconv q q.property)
  filter_upwards [hsim] with ω hω
  apply uniform_tendsto_on_compact K hK (f ω) g
  · exact fun n x _ y _ => hf ω n x y
  · exact fun x _ y _ => hg x y
  · intro x _
    exact pointwise_tendsto_of_dense s (f ω) g hdense (hf ω) hg
      (fun q hq => hω ⟨q, hq⟩) x

/-- Uniform support convergence forces the Hausdorff distance to zero
once the norm-dual support representation of that distance is established.
The geometric duality identity is stated explicitly as `hdual`. -/
theorem support_distance_tendsto_of_uniform
    {X : Type*} (K : Set X) (hne : K.Nonempty)
    (f : ℕ → X → ℝ) (g : X → ℝ) (d : ℕ → ℝ)
    (hdual : ∀ n, d n = sSup ((fun x => |f n x - g x|) '' K))
    (hu : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ K, |f n x - g x| < ε) :
    Tendsto d atTop (𝓝 0) := by
  obtain ⟨x₀, hx₀⟩ := hne
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := hu (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hnonempty : ((fun x => |f n x - g x|) '' K).Nonempty :=
    ⟨|f n x₀ - g x₀|, x₀, hx₀, rfl⟩
  have hbdd : BddAbove ((fun x => |f n x - g x|) '' K) := by
    refine ⟨ε / 2, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hN n hn x hx).le
  have hlo : 0 ≤ d n := by
    rw [hdual n]
    exact (abs_nonneg _).trans (le_csSup hbdd ⟨x₀, hx₀, rfl⟩)
  have hhi : d n ≤ ε / 2 := by
    rw [hdual n]
    apply csSup_le hnonempty
    rintro _ ⟨x, hx, rfl⟩
    exact (hN n hn x hx).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

/-- Complete deterministic/probabilistic support argument, conditional on
the separately identified support-distance duality. -/
theorem ae_support_distance_tendsto_of_dense
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (μ : MeasureTheory.Measure Ω) (s K : Set X)
    (hcount : s.Countable) (hdense : Dense s)
    (hK : IsCompact K) (hne : K.Nonempty)
    (f : Ω → ℕ → X → ℝ) (g : X → ℝ) (d : Ω → ℕ → ℝ)
    (hf : ∀ ω n x y, dist (f ω n x) (f ω n y) ≤ dist x y)
    (hg : ∀ x y, dist (g x) (g y) ≤ dist x y)
    (hconv : ∀ q ∈ s, ∀ᵐ ω ∂μ,
      Tendsto (fun n => f ω n q) atTop (𝓝 (g q)))
    (hdual : ∀ ω n, d ω n = sSup ((fun x => |f ω n x - g x|) '' K)) :
    ∀ᵐ ω ∂μ, Tendsto (d ω) atTop (𝓝 0) := by
  filter_upwards [ae_uniform_tendsto_on_compact_of_dense
    μ s K hcount hdense hK f g hf hg hconv] with ω hω
  exact support_distance_tendsto_of_uniform K hne (f ω) g (d ω) (hdual ω) hω

end OutputSpaceVerification
