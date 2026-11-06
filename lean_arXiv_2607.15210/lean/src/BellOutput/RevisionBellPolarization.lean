import BellOutput.RevisionBellChannel

/-! The real-polarization/complex-linearity step of Proposition A.3, including
its application to normalized traces of actual matrix maps. -/

open Filter
open scoped BigOperators
noncomputable section
namespace RevisionBell

section Polarization
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [StarAddMonoid V] [StarModule ℂ V]

lemma bilinear_polarization
    (b : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hs : ∀ x y, b x y = b y x) (x y : V) :
    b x y = (b (x+y) (x+y) - b x x - b y y) / 2 := by
  simp only [map_add, LinearMap.add_apply]
  rw [hs y x]
  ring

/-- Symmetric complex bilinear forms are determined, including for limits, by
their quadratic values on the self-adjoint subspace. -/
theorem bilinear_tendsto_of_selfAdjoint_diagonal
    (b : ℕ → V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (l : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hb : ∀ n x y, b n x y = b n y x)
    (hl : ∀ x y, l x y = l y x)
    (hq : ∀ x, IsSelfAdjoint x → Tendsto (fun n => b n x x) atTop (nhds (l x x)))
    (x y : V) :
    Tendsto (fun n => b n x y) atTop (nhds (l x y)) := by
  have hherm : ∀ x y, IsSelfAdjoint x → IsSelfAdjoint y →
      Tendsto (fun n => b n x y) atTop (nhds (l x y)) := by
    intro x y hx hy
    have hh := (((hq (x+y) (hx.add hy)).sub (hq x hx)).sub (hq y hy)).div_const (2 : ℂ)
    simpa only [← bilinear_polarization _ (hb _), ← bilinear_polarization _ hl] using hh
  have hfirst : ∀ x y, IsSelfAdjoint x →
      Tendsto (fun n => b n x y) atTop (nhds (l x y)) := by
    intro x y hx
    have hr := hherm x (realPart y : V) hx selfAdjoint.isSelfAdjoint
    have hi := hherm x (imaginaryPart y : V) hx selfAdjoint.isSelfAdjoint
    have h := hr.add (hi.const_mul Complex.I)
    have heq (v : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) :
        v x (realPart y : V) + Complex.I * v x (imaginaryPart y : V) = v x y := by
      conv_rhs => rw [← realPart_add_I_smul_imaginaryPart y]
      simp only [map_add, map_smul, smul_eq_mul]
    simpa only [heq] using h
  have hr := hfirst (realPart x : V) y selfAdjoint.isSelfAdjoint
  have hi := hfirst (imaginaryPart x : V) y selfAdjoint.isSelfAdjoint
  have h := hr.add (hi.const_mul Complex.I)
  have heq (v : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) :
      v (realPart x : V) y + Complex.I * v (imaginaryPart x : V) y = v x y := by
    conv_rhs => rw [← realPart_add_I_smul_imaginaryPart x]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  simpa only [heq] using h
end Polarization

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The normalized trace bilinear form of a complex-linear matrix map. -/
def normalizedTraceForm (C : Matrix B B ℂ →ₗ[ℂ] Matrix A A ℂ) :
    Matrix B B ℂ →ₗ[ℂ] Matrix B B ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun X Y => (1 / (Fintype.card A : ℂ)) * Matrix.trace (C X * C Y))
    (by intros; simp [map_add, Matrix.add_mul, Matrix.trace_add, mul_add])
    (by intros; simp [map_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; ring)
    (by intros; simp [map_add, Matrix.mul_add, Matrix.trace_add, mul_add])
    (by intros; simp [map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring)

@[simp] theorem normalizedTraceForm_apply
    (C : Matrix B B ℂ →ₗ[ℂ] Matrix A A ℂ) (X Y : Matrix B B ℂ) :
    normalizedTraceForm C X Y =
      (1 / (Fintype.card A : ℂ)) * Matrix.trace (C X * C Y) := rfl

theorem normalizedTraceForm_symmetric
    (C : Matrix B B ℂ →ₗ[ℂ] Matrix A A ℂ) (X Y : Matrix B B ℂ) :
    normalizedTraceForm C X Y = normalizedTraceForm C Y X := by
  simp only [normalizedTraceForm_apply, Matrix.trace_mul_comm (C X) (C Y)]

/-- The limiting bilinear form in Proposition A.3. -/
def hessianTraceForm (c0 c1 : ℂ) :
    Matrix B B ℂ →ₗ[ℂ] Matrix B B ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun X Y => -c0 * Matrix.trace X * Matrix.trace Y - c1 * Matrix.trace (X*Y))
    (by intros; simp [Matrix.trace_add, Matrix.add_mul]; ring)
    (by intros; simp [Matrix.trace_smul, Matrix.smul_mul, smul_eq_mul]; ring)
    (by intros; simp [Matrix.trace_add, Matrix.mul_add]; ring)
    (by intros; simp [Matrix.trace_smul, Matrix.mul_smul, smul_eq_mul]; ring)

@[simp] theorem hessianTraceForm_apply (c0 c1 : ℂ) (X Y : Matrix B B ℂ) :
    hessianTraceForm c0 c1 X Y = -c0 * Matrix.trace X * Matrix.trace Y -
      c1 * Matrix.trace (X*Y) := rfl

theorem hessianTraceForm_symmetric (c0 c1 : ℂ) (X Y : Matrix B B ℂ) :
    hessianTraceForm c0 c1 X Y = hessianTraceForm c0 c1 Y X := by
  simp only [hessianTraceForm_apply, Matrix.trace_mul_comm X Y]
  ring

/-- All complex mixed moments follow from the Hermitian quadratic limits.
No convergence on non-Hermitian test matrices is assumed. -/
theorem mixed_trace_limit_of_hermitian_square_limits
    (A : ℕ → Type*) [∀ n, Fintype (A n)]
    (C : ∀ n, Matrix B B ℂ →ₗ[ℂ] Matrix (A n) (A n) ℂ)
    (c0 c1 : ℂ)
    (hq : ∀ H : Matrix B B ℂ, H.IsHermitian →
      Tendsto (fun n => (1 / (Fintype.card (A n) : ℂ)) * Matrix.trace (C n H * C n H))
        atTop (nhds (-c0 * Matrix.trace H * Matrix.trace H - c1 * Matrix.trace (H*H))))
    (X Y : Matrix B B ℂ) :
    Tendsto (fun n => (1 / (Fintype.card (A n) : ℂ)) * Matrix.trace (C n X * C n Y))
      atTop (nhds (-c0 * Matrix.trace X * Matrix.trace Y - c1 * Matrix.trace (X*Y))) := by
  exact bilinear_tendsto_of_selfAdjoint_diagonal
    (fun n => normalizedTraceForm (C n)) (hessianTraceForm c0 c1)
    (fun n => normalizedTraceForm_symmetric (C n)) (hessianTraceForm_symmetric c0 c1)
    hq X Y

/-- The block map `H ↦ ∑ H_{ji} J_{ij}`. For normalized Choi matrices it is
the adjoint channel, up to the input transpose. -/
def choiAdjoint (J : Matrix (A × B) (A × B) ℂ) :
    Matrix B B ℂ →ₗ[ℂ] Matrix A A ℂ where
  toFun H := fun a b => ∑ i, ∑ j, H j i * J (a,i) (b,j)
  map_add' H K := by
    ext a b
    simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' z H := by
    ext a b
    simp [Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem choiAdjoint_matrixUnit [DecidableEq B]
    (J : Matrix (A × B) (A × B) ℂ) (i j : B) :
    choiAdjoint J (PreliminariesMatrix.matrixUnit j i) =
      BellLimitVerification.choiBlock J i j := by
  ext a b
  simp [choiAdjoint, PreliminariesMatrix.matrixUnit,
    BellLimitVerification.choiBlock, ite_and]

theorem matrixUnit_trace [DecidableEq B] (i j : B) :
    Matrix.trace (PreliminariesMatrix.matrixUnit i j : Matrix B B ℂ) =
      if i=j then 1 else 0 := by
  classical
  simp [Matrix.trace, Matrix.diag, PreliminariesMatrix.matrixUnit, ite_and]

theorem matrixUnit_mul_trace [DecidableEq B] (i j p q : B) :
    Matrix.trace ((PreliminariesMatrix.matrixUnit j i : Matrix B B ℂ) *
      PreliminariesMatrix.matrixUnit p q) = if i=p ∧ j=q then 1 else 0 := by
  classical
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    PreliminariesMatrix.matrixUnit, ite_and]
  by_cases hip : i=p <;> by_cases hjq : j=q <;> simp_all [eq_comm]

/-- Equation (100) from equation (104), with the full complex polarization
step checked. The square-moment limit is the only analytic input. -/
theorem choi_mixed_moments_of_hermitian_square_limits [DecidableEq B]
    (A : ℕ → Type*) [∀ n, Fintype (A n)]
    (J : ∀ n, Matrix (A n × B) (A n × B) ℂ) (c0 c1 : ℂ)
    (hq : ∀ H : Matrix B B ℂ, H.IsHermitian →
      Tendsto (fun n => (1 / (Fintype.card (A n) : ℂ)) *
        Matrix.trace (choiAdjoint (J n) H * choiAdjoint (J n) H)) atTop
        (nhds (-c0 * Matrix.trace H * Matrix.trace H - c1 * Matrix.trace (H*H))))
    (i j p q : B) :
    Tendsto (fun n => (1 / (Fintype.card (A n) : ℂ)) *
      Matrix.trace (BellLimitVerification.choiBlock (J n) i j *
        BellLimitVerification.choiBlock (J n) q p)) atTop
      (nhds (-c0 * (if i=j ∧ p=q then 1 else 0) -
        c1 * (if i=p ∧ j=q then 1 else 0))) := by
  have h := mixed_trace_limit_of_hermitian_square_limits A
    (fun n => choiAdjoint (J n)) c0 c1 hq
    (PreliminariesMatrix.matrixUnit j i) (PreliminariesMatrix.matrixUnit p q)
  simp_rw [choiAdjoint_matrixUnit, matrixUnit_trace, matrixUnit_mul_trace] at h
  have heq : -c0 * (if j=i then 1 else 0) * (if p=q then 1 else 0) =
      -c0 * (if i=j ∧ p=q then 1 else 0) := by
    by_cases hij : i=j <;> by_cases hpq : p=q <;> simp [hij, hpq, eq_comm]
  rwa [heq] at h

end RevisionBell
