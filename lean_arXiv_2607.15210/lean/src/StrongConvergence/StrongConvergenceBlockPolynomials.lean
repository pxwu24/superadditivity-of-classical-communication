import RandomCompression.BlockModification
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Deterministic polynomial closure for strong block modification

This file does not assume or prove any Haar asymptotic-freeness theorem.
It formalizes the deterministic step in Nechita (2018), Theorem 5.2:
a fixed block modification is a fixed noncommutative star polynomial in
the original matrix and the tensor matrix units. Strong joint convergence
therefore passes to the modified matrix, by genuine polynomial substitution.

The remaining probabilistic joint convergence and free-law identification
are stated nowhere as axioms and are not claimed to be proved here.
-/
open Matrix Finset Filter PreliminariesMatrix ProjectionChannelsCP
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergenceBlock

/-- Syntax for arbitrary complex noncommutative star polynomials. -/
inductive StarPolynomial (ι : Type*) where
  | scalar : ℂ → StarPolynomial ι
  | var : ι → StarPolynomial ι
  | add : StarPolynomial ι → StarPolynomial ι → StarPolynomial ι
  | mul : StarPolynomial ι → StarPolynomial ι → StarPolynomial ι
  | adjoint : StarPolynomial ι → StarPolynomial ι

namespace StarPolynomial
variable {ι κ : Type*}

def eval {A : Type*} [Ring A] [Algebra ℂ A] [Star A] (x : ι → A) : StarPolynomial ι → A
  | scalar c => algebraMap ℂ A c
  | var i => x i
  | add p q => eval x p + eval x q
  | mul p q => eval x p * eval x q
  | adjoint p => star (eval x p)

def substitute (q : κ → StarPolynomial ι) : StarPolynomial κ → StarPolynomial ι
  | scalar c => scalar c
  | var i => q i
  | add p r => add (substitute q p) (substitute q r)
  | mul p r => mul (substitute q p) (substitute q r)
  | adjoint p => adjoint (substitute q p)

theorem eval_substitute {A : Type*} [Ring A] [Algebra ℂ A] [Star A]
    (x : ι → A) (q : κ → StarPolynomial ι) (p : StarPolynomial κ) :
    eval x (substitute q p)=eval (fun i => eval x (q i)) p := by
  induction p <;> simp_all only [substitute,eval]

def listSum (l : List (StarPolynomial ι)) : StarPolynomial ι :=
  l.foldr add (scalar 0)

theorem eval_listSum {A : Type*} [Ring A] [Algebra ℂ A] [Star A]
    (x : ι → A) (l : List (StarPolynomial ι)) :
    eval x (listSum l)=(l.map (eval x)).sum := by
  induction l with
  | nil => simp [listSum,eval]
  | cons p l ih => simpa [listSum,eval] using congrArg (fun z => eval x p+z) ih

def sum {δ : Type*} (s : Finset δ) (q : δ → StarPolynomial ι) : StarPolynomial ι :=
  listSum (s.toList.map q)

theorem eval_sum {δ A : Type*} [Ring A] [Algebra ℂ A] [Star A]
    (x : ι → A) (s : Finset δ) (q : δ → StarPolynomial ι) :
    eval x (sum s q)=∑ i∈s,eval x (q i) := by
  rw [sum,eval_listSum,List.map_map]
  exact Finset.sum_map_toList s (fun i => eval x (q i))

end StarPolynomial

/-- Standard joint strong convergence: every star polynomial has convergent
normalized traces and norms. The traces may live on varying algebras. -/
def StronglyConverges {ι : Type*} {A : ℕ → Type*} {B : Type*}
    [∀ n,NormedRing (A n)] [∀ n,NormedAlgebra ℂ (A n)] [∀ n,StarRing (A n)]
    [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]
    (τ : ∀ n,A n → ℂ) (σ : B → ℂ) (x : ∀ n,ι → A n) (y : ι → B) : Prop :=
  ∀ p : StarPolynomial ι,
    Tendsto (fun n => τ n (p.eval (x n))) atTop (nhds (σ (p.eval y))) ∧
    Tendsto (fun n => ‖p.eval (x n)‖) atTop (nhds ‖p.eval y‖)

/-- Strong convergence is closed under fixed noncommutative star-polynomial
maps. This is the precise deterministic substitution step, not a new input. -/
theorem StronglyConverges.polynomial_map
    {ι κ : Type*} {A : ℕ → Type*} {B : Type*}
    [∀ n,NormedRing (A n)] [∀ n,NormedAlgebra ℂ (A n)] [∀ n,StarRing (A n)]
    [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]
    {τ : ∀ n,A n → ℂ} {σ : B → ℂ} {x : ∀ n,ι → A n} {y : ι → B}
    (h : StronglyConverges τ σ x y) (q : κ → StarPolynomial ι) :
    StronglyConverges τ σ (fun n i => (q i).eval (x n)) (fun i => (q i).eval y) := by
  intro p
  simpa only [StarPolynomial.eval_substitute] using h (p.substitute q)

end StrongConvergenceBlock
