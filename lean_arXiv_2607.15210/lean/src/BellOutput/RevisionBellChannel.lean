import Preliminaries.PreliminariesChoi
import Entropy.BellMatrixIdentities
import Entropy.BellLimitCoefficients
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
The actual finite matrix tensor-channel calculation and the deterministic
passage from the normalized Choi mixed moments (Proposition A.3) to the Bell
limit (Theorem IV.1). The analytic mixed-moment limit is an explicit hypothesis;
it is not proved or disguised as a definition in this module.
-/

open Finset Filter
open scoped BigOperators Matrix.L2OpNorm
noncomputable section
namespace RevisionBell

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The normalized rank-one Bell state, in the prescribed product basis. -/
def bellState (A : Type*) [Fintype A] [DecidableEq A] :
    Matrix (A × A) (A × A) ℂ :=
  fun ac bd => if ac.1 = ac.2 ∧ bd.1 = bd.2 then 1 / (Fintype.card A : ℂ) else 0

/-- The tensor product of two matrix maps, evaluated by matrix-unit expansion.
For linear maps this is their usual tensor product. -/
def tensorMap
    (Φ Ψ : Matrix A A ℂ → Matrix B B ℂ)
    (X : Matrix (A × A) (A × A) ℂ) : Matrix (B × B) (B × B) ℂ :=
  fun ip jq => ∑ a, ∑ b, ∑ c, ∑ d,
    X (a,c) (b,d) * Φ (PreliminariesMatrix.matrixUnit a b) ip.1 jq.1 *
      Ψ (PreliminariesMatrix.matrixUnit c d) ip.2 jq.2

/-- This matrix-unit definition is the ordinary tensor product: on every
simple tensor of input matrices it acts by applying the two linear maps. -/
theorem tensorMap_kronecker
    (Φ Ψ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (X Y : Matrix A A ℂ) :
    tensorMap Φ Ψ (Matrix.kronecker X Y) = Matrix.kronecker (Φ X) (Ψ Y) := by
  have hexp (F : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (Z : Matrix A A ℂ) (i j : B) :
      F Z i j = ∑ a, ∑ b, Z a b * F (PreliminariesMatrix.matrixUnit a b) i j := by
    have h := congrArg (fun V => F V i j) (ProjectionChannels.matrixUnit_expansion Z)
    simpa only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h.symm
  ext ⟨i,p⟩ ⟨j,q⟩
  change tensorMap Φ Ψ (Matrix.kronecker X Y) (i,p) (j,q) = Φ X i j * Ψ Y p q
  rw [hexp Φ X i j, hexp Ψ Y p q]
  simp only [tensorMap, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Applying a map and its conjugate to the actual Bell matrix gives the
Choi contraction, before using Hermiticity. -/
theorem tensor_conjugate_bell_entry
    (Φ : Matrix A A ℂ → Matrix B B ℂ) (i p j q : B) :
    tensorMap Φ (ProjectionChannels.conjugateMap Φ) (bellState A) (i,p) (j,q) =
      BellLimitVerification.bellEntry (ProjectionChannels.choiInput Φ) i p j q := by
  classical
  simp only [tensorMap, bellState, ProjectionChannels.conjugateMap,
    ProjectionChannels.conjugate_matrixUnit, ProjectionChannels.entrywiseConjugate,
    BellLimitVerification.bellEntry, ProjectionChannels.choiInput]
  simp only [ite_and, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true]
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, if_true]
  simp only [mul_sum, mul_assoc]
  rfl

/-- The actual Bell output of a Choi-defined map. -/
def bellOutput (J : Matrix (A × B) (A × B) ℂ) : Matrix (B × B) (B × B) ℂ :=
  tensorMap (PreliminariesMatrix.channel J)
    (ProjectionChannels.conjugateMap (PreliminariesMatrix.channel J)) (bellState A)

theorem choiInput_channel (J : Matrix (A × B) (A × B) ℂ) :
    ProjectionChannels.choiInput (PreliminariesMatrix.channel J) = J := by
  ext ⟨a,i⟩ ⟨b,j⟩
  exact PreliminariesMatrix.choi_recovery J a b i j

/-- Equation (38) of the draft, for the actual tensor-product output. -/
theorem bellOutput_entry (J : Matrix (A × B) (A × B) ℂ)
    (hJ : ∀ x y, star (J x y) = J y x) (i p j q : B) :
    bellOutput J (i,p) (j,q) = (1 / (Fintype.card A : ℂ)) *
      Matrix.trace (BellLimitVerification.choiBlock J i j *
        BellLimitVerification.choiBlock J q p) := by
  rw [bellOutput, tensor_conjugate_bell_entry, choiInput_channel]
  exact BellLimitVerification.bellEntry_eq_block_trace J hJ i p j q

/-- The isotropic matrix appearing in Theorem IV.1. -/
def isotropic (B : Type*) [Fintype B] [DecidableEq B] (r : ℝ) :
    Matrix (B × B) (B × B) ℂ :=
  (r : ℂ) • bellState B +
    (((1-r) / (Fintype.card B : ℝ)^2 : ℝ) : ℂ) • 1

theorem isotropic_entry (r : ℝ) (i p j q : B) :
    isotropic B r (i,p) (j,q) =
      ((1-r) / (Fintype.card B : ℝ)^2 : ℂ) * (if i=j ∧ p=q then 1 else 0) +
      ((r / Fintype.card B : ℝ) : ℂ) * (if i=p ∧ j=q then 1 else 0) := by
  classical
  simp only [isotropic, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    bellState, Matrix.one_apply, Prod.mk.injEq]
  push_cast
  split_ifs <;> simp_all <;> ring

/-- Entrywise convergence of finite matrices is convergence in the genuine
Euclidean operator norm, not merely in an entrywise surrogate norm. -/
theorem operator_norm_tendsto_zero_of_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (h : ∀ i j, Tendsto (fun n => M n i j) atTop (nhds (L i j))) :
    Tendsto (fun n => ‖M n - L‖) atTop (nhds 0) := by
  have hM : Tendsto M atTop (nhds L) := tendsto_pi_nhds.mpr fun i =>
    tendsto_pi_nhds.mpr fun j => h i j
  simpa using (hM.sub (tendsto_const_nhds (x := L))).norm

/-- The Hessian coefficients of Lemma A.2 give exactly the isotropic matrix,
with no representation-theoretic commutant assumption. -/
theorem hessian_entry_eq_isotropic (t : ℝ)
    (hk : (Fintype.card B : ℝ) ≠ 0)
    (hd : BellLimitVerification.denominator (Fintype.card B) t ≠ 0)
    (i p j q : B) :
    (-(BellLimitVerification.hessianC0 (Fintype.card B) t : ℝ) : ℂ) *
        (if i=j ∧ p=q then 1 else 0) +
      (-(BellLimitVerification.hessianC1 (Fintype.card B) t : ℝ) : ℂ) *
        (if i=p ∧ j=q then 1 else 0) =
      isotropic B (BellLimitVerification.mixing (Fintype.card B) t) (i,p) (j,q) := by
  have ha := BellLimitVerification.hessian_bell_coefficients hk hd
  have hb := BellLimitVerification.bell_spectrum_identities hk hd
  have hc0 : -(BellLimitVerification.hessianC0 (Fintype.card B) t : ℂ) =
      (((1-BellLimitVerification.mixing (Fintype.card B) t) /
        (Fintype.card B : ℝ)^2 : ℝ) : ℂ) := by
    exact_mod_cast ha.1.trans hb.1
  have hc1 : -(BellLimitVerification.hessianC1 (Fintype.card B) t : ℂ) =
      ((BellLimitVerification.mixing (Fintype.card B) t /
        (Fintype.card B : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast ha.2.1
  rw [isotropic_entry, hc0, hc1]
  push_cast
  rfl

/-- Theorem IV.1 from the actual mixed Choi-block moment limit (A.3).
The input spaces may vary with `n`; the fixed output dimension is crucial.
The conclusion uses the Euclidean operator norm on matrices. -/
theorem bell_operator_norm_limit_of_mixed_moments
    (A : ℕ → Type*) [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
    (J : ∀ n, Matrix (A n × B) (A n × B) ℂ) (t : ℝ)
    (hJ : ∀ n x y, star (J n x y) = J n y x)
    (hk : (Fintype.card B : ℝ) ≠ 0)
    (hd : BellLimitVerification.denominator (Fintype.card B) t ≠ 0)
    (hmoment : ∀ i j p q,
      Tendsto (fun n => (1 / (Fintype.card (A n) : ℂ)) *
        Matrix.trace (BellLimitVerification.choiBlock (J n) i j *
          BellLimitVerification.choiBlock (J n) q p)) atTop
        (nhds ((-(BellLimitVerification.hessianC0 (Fintype.card B) t : ℝ) : ℂ) *
          (if i=j ∧ p=q then 1 else 0) +
          (-(BellLimitVerification.hessianC1 (Fintype.card B) t : ℝ) : ℂ) *
          (if i=p ∧ j=q then 1 else 0)))) :
    Tendsto (fun n => ‖bellOutput (J n) -
      isotropic B (BellLimitVerification.mixing (Fintype.card B) t)‖)
      atTop (nhds 0) := by
  apply operator_norm_tendsto_zero_of_entries
  intro ⟨i,p⟩ ⟨j,q⟩
  simp_rw [bellOutput_entry (J _) (hJ _)]
  rw [← hessian_entry_eq_isotropic t hk hd i p j q]
  exact hmoment i j p q

/-- Proposition A.4 from A.3: summing the mixed moments gives the exact Choi
purity coefficient. This is a limit of genuine full-matrix traces. -/
theorem choi_purity_limit_of_mixed_moments
    (A : ℕ → Type*) [∀ n, Fintype (A n)]
    (J : ∀ n, Matrix (A n × B) (A n × B) ℂ) (t : ℝ)
    (hk : (Fintype.card B : ℝ) ≠ 0)
    (hd : BellLimitVerification.denominator (Fintype.card B) t ≠ 0)
    (hmoment : ∀ i j,
      Tendsto (fun n => (1 / (Fintype.card (A n) : ℂ)) *
        Matrix.trace (BellLimitVerification.choiBlock (J n) i j *
          BellLimitVerification.choiBlock (J n) j i)) atTop
        (nhds ((-(BellLimitVerification.hessianC0 (Fintype.card B) t : ℝ) : ℂ) *
          (if i=j then 1 else 0) -
          (BellLimitVerification.hessianC1 (Fintype.card B) t : ℂ)))) :
    Tendsto (fun n => Matrix.trace (J n * J n) /
      ((Fintype.card (A n) : ℂ) * (Fintype.card B : ℂ))) atTop
      (nhds (BellLimitVerification.bellAlpha (Fintype.card B) t : ℂ)) := by
  classical
  have hsum := tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_finset_sum Finset.univ (fun j _ => hmoment i j))
  have hscaled := hsum.div_const (Fintype.card B : ℂ)
  have heq : (fun n =>
      (∑ i : B, ∑ j : B, (1 / (Fintype.card (A n) : ℂ)) *
        Matrix.trace (BellLimitVerification.choiBlock (J n) i j *
          BellLimitVerification.choiBlock (J n) j i)) / (Fintype.card B : ℂ)) =
      (fun n => Matrix.trace (J n * J n) /
        ((Fintype.card (A n) : ℂ) * (Fintype.card B : ℂ))) := by
    funext n
    simp only [← mul_sum, BellLimitVerification.sum_block_trace_eq_trace_square]
    ring
  rw [heq] at hscaled
  have hkC : (Fintype.card B : ℂ) ≠ 0 := by exact_mod_cast hk
  have hcoef := (BellLimitVerification.hessian_bell_coefficients hk hd).2.2
  have hlimit :
      (∑ i : B, ∑ j : B,
        ((-(BellLimitVerification.hessianC0 (Fintype.card B) t : ℝ) : ℂ) *
          (if i=j then 1 else 0) -
          (BellLimitVerification.hessianC1 (Fintype.card B) t : ℂ))) /
          (Fintype.card B : ℂ) =
        (BellLimitVerification.bellAlpha (Fintype.card B) t : ℂ) := by
    simp only [sum_sub_distrib, mul_ite, mul_one, mul_zero,
      sum_ite_eq, mem_univ, if_true, sum_const, card_univ, nsmul_eq_mul]
    rw [← hcoef]
    push_cast
    field_simp
    ring
  rwa [hlimit] at hscaled

end RevisionBell
