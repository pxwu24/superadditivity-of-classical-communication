import Antisymmetric.RevisionAntisymmetricTransport

/-! Full diagonalization of the actual antisymmetric compression.

`shuffling_eigenbasis` exhibits a genuine basis of the alternating tensor
subspace, not merely a collection of eigenvectors. Its eigenvalues are exactly
`AppendixB.shuffle`, which connects Proposition V.2 to Proposition B.1.
-/
noncomputable section
open Finset Equiv
namespace AntisymmetricVerification
variable {k r : ℕ}

def alternatingSpace (k r : ℕ) : Submodule ℂ (TensorVector k r) where
  carrier := {f | alternating f}
  zero_mem' := by
    intro σ
    ext x
    simp [permute]
  add_mem' := by
    intro f g hf hg σ
    ext x
    have hfx := congrFun (hf σ) x
    have hgx := congrFun (hg σ) x
    simp only [permute, Pi.smul_apply, smul_eq_mul] at hfx hgx
    simp only [permute, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, hfx, hgx]
  smul_mem' := by
    intro c f hf σ
    ext x
    have hfx := congrFun (hf σ) x
    simp only [permute, Pi.smul_apply, smul_eq_mul] at hfx ⊢
    rw [hfx]
    ring

def eigenSlater {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian)
    (I : SubsetIndex k r) : TensorVector k r :=
  slater (fun j b => hX.eigenvectorBasis (subsetEnum I j) b)

lemma eigenSlater_alternating {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian)
    (I : SubsetIndex k r) : alternating (eigenSlater hX I) := slater_alternating _

lemma eigenSlater_linearIndependent {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) :
    LinearIndependent ℂ (eigenSlater (r := r) hX) := by
  have h := transformedSlater_linearIndependent (r := r)
    (hX.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)
    (star hX.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)
    (unitary.coe_star_mul_self hX.eigenvectorUnitary)
  simpa only [Matrix.IsHermitian.eigenvectorUnitary_apply, eigenSlater] using h

lemma eigenSlater_span {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian)
    {f : TensorVector k r} (hf : alternating f) :
    ∃ c : SubsetIndex k r → ℂ, f = ∑ I, c I • eigenSlater hX I := by
  have h := transformedSlater_expansion (r := r)
    (hX.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)
    (star hX.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)
    (unitary.coe_mul_star_self hX.eigenvectorUnitary) hf
  refine ⟨fun I => ((tensorMatrix (star hX.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)).mulVec f)
    (subsetEnum I), ?_⟩
  simpa only [Matrix.IsHermitian.eigenvectorUnitary_apply, eigenSlater] using h

/-- Equation (62) for the actual eigenbasis supplied by the Hermitian spectral
 theorem, with no extra diagonalization hypothesis. -/
theorem postprocess_eigenSlater (hr : 1 ≤ r) (hrk : r ≤ k)
    {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) (i : Fin r)
    (I : SubsetIndex k r) :
    postprocess X i (eigenSlater hX I) =
      (AppendixB.shuffle k r hX.eigenvalues I.val : ℂ) • eigenSlater hX I := by
  apply subset_shuffling_eigenvector hr hrk X _ hX.eigenvalues _ I.val I.property i
  intro a
  simpa only [RCLike.real_smul_eq_coe_smul] using hX.mulVec_eigenvectorBasis a

/-- A Slater vector as an element of the actual alternating subspace. -/
def eigenSlaterInSpace {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian)
    (I : SubsetIndex k r) : alternatingSpace k r :=
  ⟨eigenSlater hX I, eigenSlater_alternating hX I⟩

lemma eigenSlaterInSpace_linearIndependent {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) : LinearIndependent ℂ (eigenSlaterInSpace (r := r) hX) := by
  apply LinearIndependent.of_comp (alternatingSpace k r).subtype
  exact eigenSlater_linearIndependent hX

lemma eigenSlaterInSpace_spans {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) :
    ⊤ ≤ Submodule.span ℂ (Set.range (eigenSlaterInSpace (r := r) hX)) := by
  intro f hf
  obtain ⟨c, hc⟩ := eigenSlater_span hX f.property
  have heq : f = ∑ I : SubsetIndex k r, c I • eigenSlaterInSpace hX I := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, eigenSlaterInSpace] using hc
  rw [heq]
  apply Submodule.sum_mem
  intro I hI
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨I, rfl⟩

def eigenSlaterBasis {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) :
    Basis (SubsetIndex k r) ℂ (alternatingSpace k r) :=
  Basis.mk (eigenSlaterInSpace_linearIndependent hX) (eigenSlaterInSpace_spans hX)

lemma eigenSlaterBasis_apply {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian)
    (I : SubsetIndex k r) : (eigenSlaterBasis hX I).val = eigenSlater hX I := by
  simp only [eigenSlaterBasis, Basis.mk_apply, eigenSlaterInSpace]

/-- Proposition V.2: a complete eigenbasis indexed by the `r`-subsets, with
 precisely the eigenvalue shuffling used by the entropy formalization. -/
theorem shuffling_eigenbasis (hr : 1 ≤ r) (hrk : r ≤ k)
    {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) (i : Fin r) :
    ∃ b : Basis (SubsetIndex k r) ℂ (alternatingSpace k r),
      ∀ I, postprocess X i (b I).val =
        (AppendixB.shuffle k r hX.eigenvalues I.val : ℂ) • (b I).val := by
  refine ⟨eigenSlaterBasis hX, ?_⟩
  intro I
  simp only [eigenSlaterBasis_apply]
  exact postprocess_eigenSlater hr hrk hX i I

lemma card_subsetIndex : Fintype.card (SubsetIndex k r) = Nat.choose k r := by
  classical
  calc
    Fintype.card (SubsetIndex k r) = Fintype.card ↥(AppendixB.subsets k r) := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun I => by simp [AppendixB.subsets, Finset.mem_powersetCard])
    _ = (AppendixB.subsets k r).card := Fintype.card_coe _
    _ = Nat.choose k r := AppendixB.card_subsets k r

/-- The alternating output space has exactly the paper's output dimension. -/
theorem finrank_alternatingSpace : Module.finrank ℂ (alternatingSpace k r) = Nat.choose k r := by
  have hX : (0 : Matrix (Fin k) (Fin k) ℂ).IsHermitian := Matrix.isHermitian_zero
  rw [Module.finrank_eq_card_basis (eigenSlaterBasis (r := r) hX), card_subsetIndex]

lemma antisymmetrize_add (f g : TensorVector k r) :
    antisymmetrize (f + g) = antisymmetrize f + antisymmetrize g := by
  ext x
  simp [antisymmetrize, permute, mul_add, Finset.sum_add_distrib]

lemma oneLeg_add (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r)
    (f g : TensorVector k r) : oneLeg X i (f + g) = oneLeg X i f + oneLeg X i g := by
  ext x
  simp [oneLeg, mul_add, Finset.sum_add_distrib]

lemma postprocess_add (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r)
    (f g : TensorVector k r) : postprocess X i (f + g) = postprocess X i f + postprocess X i g := by
  simp only [postprocess, antisymmetrize_add, oneLeg_add, smul_add]

lemma postprocess_alternating (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r)
    (f : TensorVector k r) : alternating (postprocess X i f) :=
  (alternatingSpace k r).smul_mem _ (antisymmetrize_alternating _)

/-- The actual compressed operator restricted to the alternating output space. -/
def postprocessRestriction (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin r) :
    (alternatingSpace k r) →ₗ[ℂ] (alternatingSpace k r) where
  toFun f := ⟨postprocess X i f, postprocess_alternating X i f⟩
  map_add' f g := Subtype.ext (postprocess_add X i f g)
  map_smul' c f := Subtype.ext (postprocess_smul X i c f)

lemma postprocessRestriction_basis (hr : 1 ≤ r) (hrk : r ≤ k)
    {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) (i : Fin r)
    (I : SubsetIndex k r) :
    postprocessRestriction X i (eigenSlaterBasis hX I) =
      (AppendixB.shuffle k r hX.eigenvalues I.val : ℂ) • eigenSlaterBasis hX I := by
  apply Subtype.ext
  change postprocess X i (eigenSlaterBasis hX I).val =
    (AppendixB.shuffle k r hX.eigenvalues I.val : ℂ) • (eigenSlaterBasis hX I).val
  simp only [eigenSlaterBasis_apply]
  exact postprocess_eigenSlater hr hrk hX i I

/-- The complete matrix form of Proposition V.2: in the constructed basis,
 the actual restricted output operator is diagonal with the shuffled entries.
 Consequently repetitions of a shuffled value retain their subset multiplicity. -/
theorem postprocess_matrix_diagonal (hr : 1 ≤ r) (hrk : r ≤ k)
    {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) (i : Fin r) :
    LinearMap.toMatrix (eigenSlaterBasis hX) (eigenSlaterBasis hX)
      (postprocessRestriction X i) =
      Matrix.diagonal (fun I : SubsetIndex k r =>
        (AppendixB.shuffle k r hX.eigenvalues I.val : ℂ)) := by
  classical
  ext I J
  rw [LinearMap.toMatrix_apply, postprocessRestriction_basis hr hrk hX i J]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, Matrix.diagonal_apply]
  by_cases h : I = J
  · subst I
    simp
  · simp [h, Ne.symm h]

end AntisymmetricVerification
