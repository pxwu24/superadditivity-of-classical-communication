import BellOutput.RevisionBellPolarization
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! Almost-sure complex polarization with only finitely many test events
intersected for every requested pair of observables. -/

open Filter MeasureTheory
open scoped BigOperators
noncomputable section
namespace RevisionBell

section Polarization
variable {Ω V : Type*} [MeasurableSpace Ω] [AddCommGroup V] [Module ℂ V]
  [StarAddMonoid V] [StarModule ℂ V]

theorem ae_bilinear_tendsto_of_selfAdjoint_diagonal
    (μ : Measure Ω)
    (b : Ω → ℕ → V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (l : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hb : ∀ ω n x y, b ω n x y = b ω n y x)
    (hl : ∀ x y, l x y = l y x)
    (hq : ∀ x, IsSelfAdjoint x →
      ∀ᵐ ω ∂μ, Tendsto (fun n => b ω n x x) atTop (nhds (l x x)))
    (x y : V) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => b ω n x y) atTop (nhds (l x y)) := by
  have hherm : ∀ x y, IsSelfAdjoint x → IsSelfAdjoint y →
      ∀ᵐ ω ∂μ, Tendsto (fun n => b ω n x y) atTop (nhds (l x y)) := by
    intro x y hx hy
    filter_upwards [hq (x+y) (hx.add hy),hq x hx,hq y hy] with ω hxy hx hy
    have hh := ((hxy.sub hx).sub hy).div_const (2 : ℂ)
    simpa only [← bilinear_polarization _ (hb ω _), ← bilinear_polarization _ hl] using hh
  have hfirst : ∀ x y, IsSelfAdjoint x →
      ∀ᵐ ω ∂μ, Tendsto (fun n => b ω n x y) atTop (nhds (l x y)) := by
    intro x y hx
    filter_upwards [hherm x (realPart y : V) hx selfAdjoint.isSelfAdjoint,
      hherm x (imaginaryPart y : V) hx selfAdjoint.isSelfAdjoint] with ω hr hi
    have h := hr.add (hi.const_mul Complex.I)
    have heq (v : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) :
        v x (realPart y : V) + Complex.I * v x (imaginaryPart y : V) = v x y := by
      conv_rhs => rw [← realPart_add_I_smul_imaginaryPart y]
      simp only [map_add, map_smul, smul_eq_mul]
    simpa only [heq] using h
  filter_upwards [hfirst (realPart x : V) y selfAdjoint.isSelfAdjoint,
    hfirst (imaginaryPart x : V) y selfAdjoint.isSelfAdjoint] with ω hr hi
  have h := hr.add (hi.const_mul Complex.I)
  have heq (v : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) :
      v (realPart x : V) y + Complex.I * v (imaginaryPart x : V) y = v x y := by
    conv_rhs => rw [← realPart_add_I_smul_imaginaryPart x]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  simpa only [heq] using h
end Polarization

variable {Ω B : Type*} [MeasurableSpace Ω] [Fintype B]

theorem ae_mixed_trace_limit_of_hermitian_square_limits
    (μ : Measure Ω) (A : ℕ → Type*) [∀ n, Fintype (A n)]
    (C : Ω → ∀ n, Matrix B B ℂ →ₗ[ℂ] Matrix (A n) (A n) ℂ)
    (c0 c1 : ℂ)
    (hq : ∀ H : Matrix B B ℂ, H.IsHermitian →
      ∀ᵐ ω ∂μ, Tendsto
        (fun n => (1 / (Fintype.card (A n) : ℂ)) * Matrix.trace (C ω n H * C ω n H))
        atTop (nhds (-c0 * Matrix.trace H * Matrix.trace H - c1 * Matrix.trace (H*H))))
    (X Y : Matrix B B ℂ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (1 / (Fintype.card (A n) : ℂ)) * Matrix.trace (C ω n X * C ω n Y))
      atTop (nhds (-c0 * Matrix.trace X * Matrix.trace Y - c1 * Matrix.trace (X*Y))) := by
  exact ae_bilinear_tendsto_of_selfAdjoint_diagonal μ
    (fun ω n => normalizedTraceForm (C ω n)) (hessianTraceForm c0 c1)
    (fun ω n => normalizedTraceForm_symmetric (C ω n)) (hessianTraceForm_symmetric c0 c1)
    hq X Y

theorem ae_choi_mixed_moments_of_hermitian_square_limits [DecidableEq B]
    (μ : Measure Ω) (A : ℕ → Type*) [∀ n, Fintype (A n)]
    (J : Ω → ∀ n, Matrix (A n × B) (A n × B) ℂ) (c0 c1 : ℂ)
    (hq : ∀ H : Matrix B B ℂ, H.IsHermitian →
      ∀ᵐ ω ∂μ, Tendsto (fun n => (1 / (Fintype.card (A n) : ℂ)) *
        Matrix.trace (choiAdjoint (J ω n) H * choiAdjoint (J ω n) H)) atTop
        (nhds (-c0 * Matrix.trace H * Matrix.trace H - c1 * Matrix.trace (H*H))))
    (i j p q : B) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (1 / (Fintype.card (A n) : ℂ)) *
      Matrix.trace (BellLimitVerification.choiBlock (J ω n) i j *
        BellLimitVerification.choiBlock (J ω n) q p)) atTop
      (nhds (-c0 * (if i=j ∧ p=q then 1 else 0) -
        c1 * (if i=p ∧ j=q then 1 else 0))) := by
  have h := ae_mixed_trace_limit_of_hermitian_square_limits μ A
    (fun ω n => choiAdjoint (J ω n)) c0 c1 hq
    (PreliminariesMatrix.matrixUnit j i) (PreliminariesMatrix.matrixUnit p q)
  filter_upwards [h] with ω hω
  simp_rw [choiAdjoint_matrixUnit, matrixUnit_trace, matrixUnit_mul_trace] at hω
  have heq : -c0 * (if j=i then 1 else 0) * (if p=q then 1 else 0) =
      -c0 * (if i=j ∧ p=q then 1 else 0) := by
    by_cases hij : i=j <;> by_cases hpq : p=q <;> simp [hij, hpq, eq_comm]
  rwa [heq] at hω

end RevisionBell
