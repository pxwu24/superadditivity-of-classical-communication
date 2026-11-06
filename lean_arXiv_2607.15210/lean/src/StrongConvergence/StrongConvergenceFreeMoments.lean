import StrongConvergence.StrongConvergenceFreePeel
import StrongConvergence.StrongConvergenceFreeCumulant

/-! Cycle weights and products of geodesic permutation intervals. -/
open Equiv Equiv.Perm
open scoped BigOperators
noncomputable section
namespace ProjectionChannels.FreeMoments
open ProjectionChannels.TensorHaar
variable {α β : Type*} [Fintype α] [Fintype β]

abbrev OrbitClasses (σ : Perm α) := Quotient (SameCycle.setoid σ)
noncomputable instance orbitClassesFintype (σ : Perm α) : Fintype (OrbitClasses σ) :=
  Fintype.ofFinite _

def orbitCount (σ : Perm α) : ℕ := Fintype.card (OrbitClasses σ)
def absoluteLength (σ : Perm α) : ℕ := Fintype.card α - orbitCount σ
def absoluteLE (σ τ : Perm α) : Prop :=
  absoluteLength σ + absoluteLength (τ * σ.symm) = absoluteLength τ

lemma orbitCount_le (σ : Perm α) : orbitCount σ ≤ Fintype.card α :=
  Fintype.card_le_of_surjective (Quotient.mk _ : α → OrbitClasses σ) Quotient.mk_surjective

def orbitClassesFinEquiv {n : ℕ} (σ : Perm (Fin n)) :
    OrbitClasses σ ≃ CycleClasses σ :=
  Quotient.congrRight (fun x y => (cycleRelation_iff_sameCycle σ x y).symm)

@[simp] lemma orbitCount_fin {n : ℕ} (σ : Perm (Fin n)) : orbitCount σ = cycleCount σ :=
  Fintype.card_congr (orbitClassesFinEquiv σ)

@[simp] lemma absoluteLength_fin {n : ℕ} (σ : Perm (Fin n)) :
    absoluteLength σ = permutationLength σ := by simp [absoluteLength, permutationLength]

@[simp] lemma absoluteLE_fin {n : ℕ} (σ τ : Perm (Fin n)) :
    absoluteLE σ τ ↔ PermutationAbsoluteLE σ τ := by
  simp [absoluteLE, PermutationAbsoluteLE]

def permutationTransport (e : α ≃ β) : Perm α →* Perm β where
  toFun := e.permCongr
  map_one' := by ext x; simp [Equiv.Perm.one_def]
  map_mul' σ τ := by ext x; simp [Equiv.Perm.mul_apply]

@[simp] lemma permutationTransport_apply (e : α ≃ β) (σ : Perm α) :
    permutationTransport e σ = e.permCongr σ := rfl

lemma sameCycle_transport (e : α ≃ β) (σ : Perm α) (x y : α) :
    (e.permCongr σ).SameCycle (e x) (e y) ↔ σ.SameCycle x y := by
  unfold SameCycle
  have hp (i : ℤ) : (e.permCongr σ) ^ i = e.permCongr (σ ^ i) :=
    (map_zpow (permutationTransport e) σ i).symm
  simp only [hp, Equiv.permCongr_apply, e.symm_apply_apply, e.injective.eq_iff]

def orbitClassesTransport (e : α ≃ β) (σ : Perm α) :
    OrbitClasses σ ≃ OrbitClasses (e.permCongr σ) :=
  Quotient.congr e (fun x y => (sameCycle_transport e σ x y).symm)

@[simp] lemma orbitCount_transport (e : α ≃ β) (σ : Perm α) :
    orbitCount (e.permCongr σ) = orbitCount σ :=
  (Fintype.card_congr (orbitClassesTransport e σ)).symm

@[simp] lemma absoluteLength_transport (e : α ≃ β) (σ : Perm α) :
    absoluteLength (e.permCongr σ) = absoluteLength σ := by
  rw [absoluteLength, orbitCount_transport, ← Fintype.card_congr e]
  rfl

lemma transport_mul (e : α ≃ β) (σ τ : Perm α) :
    e.permCongr (σ * τ) = e.permCongr σ * e.permCongr τ :=
  (permutationTransport e).map_mul σ τ

lemma transport_symm (e : α ≃ β) (σ : Perm α) :
    e.permCongr σ.symm = (e.permCongr σ).symm :=
  (permutationTransport e).map_inv σ

@[simp] lemma absoluteLE_transport (e : α ≃ β) (σ τ : Perm α) :
    absoluteLE (e.permCongr σ) (e.permCongr τ) ↔ absoluteLE σ τ := by
  unfold absoluteLE
  rw [← transport_symm, ← transport_mul]
  simp only [absoluteLength_transport]

lemma absoluteLength_mul_le (σ τ : Perm α) :
    absoluteLength (σ * τ) ≤ absoluteLength σ + absoluteLength τ := by
  let e := Fintype.equivFin α
  have h := permutationLength_mul_le (e.permCongr σ) (e.permCongr τ)
  simpa only [← absoluteLength_fin, ← transport_mul, absoluteLength_transport] using h

lemma sameCycle_apply_of_absoluteLE {σ τ : Perm α} (h : absoluteLE σ τ) (a : α) :
    τ.SameCycle a (σ a) := by
  let e := Fintype.equivFin α
  have hh : PermutationAbsoluteLE (e.permCongr σ) (e.permCongr τ) :=
    (absoluteLE_fin _ _).mp ((absoluteLE_transport e σ τ).mpr h)
  have hc := TensorHaar.sameCycle_apply_of_absoluteLE hh (e a)
  apply (sameCycle_transport e τ a (σ a)).mp
  simpa only [Equiv.permCongr_apply, e.symm_apply_apply] using hc

lemma sumCongr_zpow (σ : Perm α) (τ : Perm β) (i : ℤ) :
    (Perm.sumCongr σ τ) ^ i = Perm.sumCongr (σ ^ i) (τ ^ i) := by
  exact (map_zpow (Perm.sumCongrHom α β) (σ,τ) i).symm

@[simp] lemma sameCycle_sumCongr_inl (σ : Perm α) (τ : Perm β) (x y : α) :
    (Perm.sumCongr σ τ).SameCycle (Sum.inl x) (Sum.inl y) ↔ σ.SameCycle x y := by
  simp only [SameCycle, sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl, Sum.inl.injEq]

@[simp] lemma sameCycle_sumCongr_inr (σ : Perm α) (τ : Perm β) (x y : β) :
    (Perm.sumCongr σ τ).SameCycle (Sum.inr x) (Sum.inr y) ↔ τ.SameCycle x y := by
  simp only [SameCycle, sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inr, Sum.inr.injEq]

@[simp] lemma not_sameCycle_sumCongr_inl_inr (σ : Perm α) (τ : Perm β) (x : α) (y : β) :
    ¬(Perm.sumCongr σ τ).SameCycle (Sum.inl x) (Sum.inr y) := by
  simp [SameCycle, sumCongr_zpow, Perm.sumCongr_apply]

@[simp] lemma not_sameCycle_sumCongr_inr_inl (σ : Perm α) (τ : Perm β) (x : β) (y : α) :
    ¬(Perm.sumCongr σ τ).SameCycle (Sum.inr x) (Sum.inl y) := by
  simp [SameCycle, sumCongr_zpow, Perm.sumCongr_apply]

/-- Cycles in a block sum are the disjoint union of the cycles in its blocks. -/
def orbitClassesSumEquiv (σ : Perm α) (τ : Perm β) :
    OrbitClasses (Perm.sumCongr σ τ) ≃ OrbitClasses σ ⊕ OrbitClasses τ where
  toFun := Quotient.lift (Sum.elim (fun x => Sum.inl (Quotient.mk _ x))
    (fun y => Sum.inr (Quotient.mk _ y))) (by
      intro x y h
      cases x with
      | inl x => cases y with
        | inl y => exact congrArg Sum.inl (Quotient.sound ((sameCycle_sumCongr_inl σ τ x y).mp h))
        | inr y => exact False.elim (not_sameCycle_sumCongr_inl_inr σ τ x y h)
      | inr x => cases y with
        | inl y => exact False.elim (not_sameCycle_sumCongr_inr_inl σ τ x y h)
        | inr y => exact congrArg Sum.inr (Quotient.sound ((sameCycle_sumCongr_inr σ τ x y).mp h)))
  invFun := Sum.elim
    (Quotient.map Sum.inl (fun x y h => (sameCycle_sumCongr_inl σ τ x y).mpr h))
    (Quotient.map Sum.inr (fun x y h => (sameCycle_sumCongr_inr σ τ x y).mpr h))
  left_inv q := by
    induction q using Quotient.inductionOn with | h q =>
      cases q <;> rfl
  right_inv q := by
    cases q with
    | inl q => induction q using Quotient.inductionOn; rfl
    | inr q => induction q using Quotient.inductionOn; rfl

@[simp] lemma orbitCount_sumCongr (σ : Perm α) (τ : Perm β) :
    orbitCount (Perm.sumCongr σ τ) = orbitCount σ + orbitCount τ := by
  rw [orbitCount, Fintype.card_congr (orbitClassesSumEquiv σ τ), Fintype.card_sum]
  rfl

@[simp] lemma absoluteLength_sumCongr (σ : Perm α) (τ : Perm β) :
    absoluteLength (Perm.sumCongr σ τ) = absoluteLength σ + absoluteLength τ := by
  have hs := orbitCount_le σ
  have ht := orbitCount_le τ
  simp only [absoluteLength, Fintype.card_sum, orbitCount_sumCongr]
  omega

@[simp] theorem absoluteLE_sumCongr_iff (σ₁ τ₁ : Perm α) (σ₂ τ₂ : Perm β) :
    absoluteLE (Perm.sumCongr σ₁ σ₂) (Perm.sumCongr τ₁ τ₂) ↔
      absoluteLE σ₁ τ₁ ∧ absoluteLE σ₂ τ₂ := by
  have h₁ := absoluteLength_mul_le (τ₁ * σ₁.symm) σ₁
  have h₂ := absoluteLength_mul_le (τ₂ * σ₂.symm) σ₂
  simp only [mul_assoc, Perm.symm_mul, mul_one] at h₁ h₂
  simp only [absoluteLE, Perm.sumCongr_symm, Perm.sumCongr_mul, absoluteLength_sumCongr]
  omega

/-- Every lower permutation of a block sum preserves each block. -/
theorem absoluteLE_sumCongr_exists (σ : Perm (α ⊕ β)) (ρ₁ : Perm α) (ρ₂ : Perm β)
    (h : absoluteLE σ (Perm.sumCongr ρ₁ ρ₂)) :
    ∃ σ₁ : Perm α, ∃ σ₂ : Perm β,
      σ = Perm.sumCongr σ₁ σ₂ ∧ absoluteLE σ₁ ρ₁ ∧ absoluteLE σ₂ ρ₂ := by
  have hmaps : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨a,rfl⟩
    have hc := sameCycle_apply_of_absoluteLE h (Sum.inl a)
    cases he : σ (Sum.inl a) with
    | inl b => exact ⟨b,rfl⟩
    | inr b => rw [he] at hc; exact False.elim (not_sameCycle_sumCongr_inl_inr ρ₁ ρ₂ a b hc)
  obtain ⟨⟨σ₁,σ₂⟩,he⟩ := Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
  change Perm.sumCongr σ₁ σ₂ = σ at he
  refine ⟨σ₁,σ₂,he.symm,?_⟩
  rw [← he] at h
  exact (absoluteLE_sumCongr_iff _ _ _ _).mp h


local instance orbitClassesDecidableEq (σ : Perm α) : DecidableEq (OrbitClasses σ) :=
  Classical.decEq _
local instance sameCycleDecidableRel (σ : Perm α) : DecidableRel σ.SameCycle :=
  Classical.decRel _

/-- Cardinality of one orbit, including one for a fixed point. -/
def orbitSize (σ : Perm α) (q : OrbitClasses σ) : ℕ :=
  Fintype.card {x : α // (Quotient.mk _ x : OrbitClasses σ) = q}

lemma orbitSize_mk (σ : Perm α) (a : α) :
    orbitSize σ (Quotient.mk _ a) = Fintype.card {x : α // σ.SameCycle x a} := by
  classical
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x : α =>
    (Quotient.eq : (Quotient.mk _ x : OrbitClasses σ) = Quotient.mk _ a ↔ σ.SameCycle x a)))

/-- Equivariant relabelling preserves the size of each cycle. -/
lemma orbitSize_transport (e : α ≃ β) (σ : Perm α) (q : OrbitClasses σ) :
    orbitSize (e.permCongr σ) (orbitClassesTransport e σ q) = orbitSize σ q := by
  classical
  induction q using Quotient.inductionOn with | h a =>
    change orbitSize (e.permCongr σ) (Quotient.mk _ (e a)) = orbitSize σ (Quotient.mk _ a)
    rw [orbitSize_mk, orbitSize_mk]
    symm
    apply Fintype.card_congr
    exact e.subtypeEquiv (fun x => (sameCycle_transport e σ x a).symm)

lemma orbitSize_sum_left (σ : Perm α) (τ : Perm β) (q : OrbitClasses σ) :
    orbitSize (Perm.sumCongr σ τ) ((orbitClassesSumEquiv σ τ).symm (Sum.inl q)) =
      orbitSize σ q := by
  classical
  induction q using Quotient.inductionOn with | h a =>
    change orbitSize (Perm.sumCongr σ τ) (Quotient.mk _ (Sum.inl a)) =
      orbitSize σ (Quotient.mk _ a)
    rw [orbitSize_mk, orbitSize_mk, Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
    simp only [sameCycle_sumCongr_inl, not_sameCycle_sumCongr_inr_inl]
    simp

lemma orbitSize_sum_right (σ : Perm α) (τ : Perm β) (q : OrbitClasses τ) :
    orbitSize (Perm.sumCongr σ τ) ((orbitClassesSumEquiv σ τ).symm (Sum.inr q)) =
      orbitSize τ q := by
  classical
  induction q using Quotient.inductionOn with | h a =>
    change orbitSize (Perm.sumCongr σ τ) (Quotient.mk _ (Sum.inr a)) =
      orbitSize τ (Quotient.mk _ a)
    rw [orbitSize_mk, orbitSize_mk, Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
    simp only [sameCycle_sumCongr_inr, not_sameCycle_sumCongr_inl_inr]
    simp

variable {R : Type*}
section CycleWeights
variable [CommMonoid R]
/-- Product of an arbitrary cycle-size weight over every cycle. -/
def cycleWeight (f : ℕ → R) (σ : Perm α) : R := ∏ q : OrbitClasses σ, f (orbitSize σ q)

lemma cycleWeight_transport (f : ℕ → R) (e : α ≃ β) (σ : Perm α) :
    cycleWeight f (e.permCongr σ) = cycleWeight f σ := by
  symm
  apply Fintype.prod_equiv (orbitClassesTransport e σ)
  intro q
  rw [orbitSize_transport]

lemma cycleWeight_sumCongr (f : ℕ → R) (σ : Perm α) (τ : Perm β) :
    cycleWeight f (Perm.sumCongr σ τ) = cycleWeight f σ * cycleWeight f τ := by
  have h := Fintype.prod_equiv (orbitClassesSumEquiv σ τ).symm
    (Sum.elim (fun q => f (orbitSize σ q)) (fun q => f (orbitSize τ q)))
    (fun q => f (orbitSize (Perm.sumCongr σ τ) q)) (by
      intro q
      cases q with
      | inl q => simp only [Sum.elim_inl, orbitSize_sum_left]
      | inr q => simp only [Sum.elim_inr, orbitSize_sum_right])
  rw [Fintype.prod_sum_type] at h
  exact h.symm

/-- The lower interval of a direct sum is the product of its lower intervals. -/
@[irreducible] def absoluteIntervalSumEquiv (ρ₁ : Perm α) (ρ₂ : Perm β) :
    {σ : Perm (α ⊕ β) // absoluteLE σ (Perm.sumCongr ρ₁ ρ₂)} ≃
      {σ : Perm α // absoluteLE σ ρ₁} × {σ : Perm β // absoluteLE σ ρ₂} := by
  classical
  let g : ({σ : Perm α // absoluteLE σ ρ₁} × {σ : Perm β // absoluteLE σ ρ₂}) →
      {σ : Perm (α ⊕ β) // absoluteLE σ (Perm.sumCongr ρ₁ ρ₂)} := fun p =>
    ⟨Perm.sumCongr p.1.val p.2.val, (absoluteLE_sumCongr_iff _ _ _ _).mpr ⟨p.1.property,p.2.property⟩⟩
  apply (Equiv.ofBijective g ?_).symm
  constructor
  · intro x y h
    have he : (x.1.val,x.2.val) = (y.1.val,y.2.val) :=
      Perm.sumCongrHom_injective (congrArg Subtype.val h)
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst he)
    · exact Subtype.ext (congrArg Prod.snd he)
  · intro σ
    obtain ⟨σ₁,σ₂,he,h₁,h₂⟩ := absoluteLE_sumCongr_exists σ.val ρ₁ ρ₂ σ.property
    exact ⟨(⟨σ₁,h₁⟩,⟨σ₂,h₂⟩), Subtype.ext he.symm⟩


lemma absoluteIntervalSumEquiv_symm_val (ρ₁ : Perm α) (ρ₂ : Perm β)
    (p : {σ : Perm α // absoluteLE σ ρ₁} × {σ : Perm β // absoluteLE σ ρ₂}) :
    ((absoluteIntervalSumEquiv ρ₁ ρ₂).symm p).val = Perm.sumCongr p.1.val p.2.val := by
  unfold absoluteIntervalSumEquiv
  rfl

end CycleWeights

section WeightedIntervals
variable [CommSemiring R]

local instance (priority := 2000) absoluteIntervalFintype (ρ : Perm α) :
    Fintype {σ : Perm α // absoluteLE σ ρ} :=
  @Subtype.fintype (Perm α) (fun σ => absoluteLE σ ρ)
    (fun _ => Classical.propDecidable _) (@Equiv.instFintype α α
      (Classical.decEq α) (Classical.decEq α) inferInstance inferInstance)

/-- Sum of cycle weights over a complete lower geodesic interval. -/
def weightedInterval (f : ℕ → R) (ρ : Perm α) : R := by
  classical
  exact ∑ σ : {σ : Perm α // absoluteLE σ ρ}, cycleWeight f σ.val

/-- Arbitrary cycle weights factor over independent permutation blocks. -/
theorem weightedInterval_sumCongr (f : ℕ → R) (ρ₁ : Perm α) (ρ₂ : Perm β) :
    weightedInterval f (Perm.sumCongr ρ₁ ρ₂) = weightedInterval f ρ₁ * weightedInterval f ρ₂ := by
  classical
  have h := Fintype.sum_equiv (absoluteIntervalSumEquiv ρ₁ ρ₂).symm
    (fun p => cycleWeight f p.1.val * cycleWeight f p.2.val)
    (fun σ => cycleWeight f σ.val) (by
      intro p
      dsimp only
      rw [absoluteIntervalSumEquiv_symm_val, cycleWeight_sumCongr])
  rw [Fintype.sum_prod_type] at h
  dsimp only at h
  rw [← Finset.sum_mul_sum] at h
  exact h.symm

def absoluteIntervalTransport (e : α ≃ β) (ρ : Perm α) :
    {σ : Perm α // absoluteLE σ ρ} ≃
      {τ : Perm β // absoluteLE τ (e.permCongr ρ)} :=
  e.permCongr.subtypeEquiv (fun σ => (absoluteLE_transport e σ ρ).symm)

theorem weightedInterval_transport (f : ℕ → R) (e : α ≃ β) (ρ : Perm α) :
    weightedInterval f (e.permCongr ρ) = weightedInterval f ρ := by
  classical
  unfold weightedInterval
  rw [← Equiv.sum_comp (absoluteIntervalTransport e ρ)]
  apply Finset.sum_congr rfl
  intro σ _
  change cycleWeight f (e.permCongr σ.val) = cycleWeight f σ.val
  exact cycleWeight_transport f e σ.val

end WeightedIntervals

#print axioms cycleWeight_sumCongr
#print axioms weightedInterval_sumCongr
#print axioms absoluteLE_sumCongr_exists
end ProjectionChannels.FreeMoments
