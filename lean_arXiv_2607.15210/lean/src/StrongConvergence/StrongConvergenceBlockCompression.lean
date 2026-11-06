import StrongConvergence.StrongConvergenceBlockMatrixUnits

/-! The precise weighted-compression norm and moment conclusions obtained
from joint strong convergence. The conclusions name an actual algebra
polynomial; identifying its Bernoulli free-sum law and establishing the Haar
joint strong convergence are separate remaining theorems, not new axioms. -/
open Matrix Finset Filter PreliminariesMatrix ProjectionChannels ProjectionChannelsCP
open scoped Topology BigOperators Matrix.L2OpNorm
noncomputable section
namespace StrongConvergenceBlock

namespace StarPolynomial
variable {ι : Type*}
def power (p : StarPolynomial ι) : ℕ → StarPolynomial ι
  | 0 => .scalar 1
  | n+1 => .mul (power p n) p

lemma eval_power {A : Type*} [Ring A] [Algebra ℂ A] [Star A]
    (x : ι → A) (p : StarPolynomial ι) (m : ℕ) :
    (power p m).eval x=(p.eval x)^m := by
  induction m with
  | zero => simp [power,eval]
  | succ m ih => simp only [power,eval,ih,pow_succ]
end StarPolynomial

variable {K : Type} [Fintype K] [DecidableEq K]

/-- The actual algebra element obtained by the weighted block polynomial. -/
def compressionLimit {B : Type*} [Ring B] [Algebra ℂ B] [Star B]
    (a : K → ℝ) (y : Option (K×K) → B) : B :=
  (blockModificationPolynomial (diagonalTraceLinearMap a)).eval y

/-- Norm convergence of every real shift of the amplified diagonal compression,
with exactly the normalization used in FullBlockModifiedStrongInput. -/
theorem shifted_compression_norm_limit
    (I : ℕ → Type) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]
    (σ : B → ℂ) (X : ∀ n,Matrix (I n×K) (I n×K) ℂ) (y : Option (K×K) → B)
    (h : StronglyConverges (fun n => @matrixTrace (I n×K) _) σ
      (fun n => blockVariables (X n)) y) (a : K → ℝ) (c : ℝ) :
    Tendsto (fun n => ‖(c:ℂ) • (1 : Matrix (I n×K) (I n×K) ℂ)+
      amplify (diagonalTraceLinearMap a) (X n)‖) atTop
      (nhds ‖algebraMap ℂ B (c:ℂ)+compressionLimit a y‖) := by
  have hh := stronglyConverges_blockModification I _ σ X y h (diagonalTraceLinearMap a)
  have hp := hh (StarPolynomial.add (.scalar (c:ℂ)) (.var ()))
  simpa only [StarPolynomial.eval,compressionLimit,Algebra.algebraMap_eq_smul_one] using hp.2

/-- Convergence of every actual normalized compression moment. -/
theorem compression_moment_limit
    (I : ℕ → Type) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]
    (σ : B → ℂ) (X : ∀ n,Matrix (I n×K) (I n×K) ℂ) (y : Option (K×K) → B)
    (h : StronglyConverges (fun n => @matrixTrace (I n×K) _) σ
      (fun n => blockVariables (X n)) y) (a : K → ℝ) (m : ℕ) :
    Tendsto (fun n => matrixTrace ((amplify (diagonalTraceLinearMap a) (X n))^m)) atTop
      (nhds (σ ((compressionLimit a y)^m))) := by
  have hh := stronglyConverges_blockModification I _ σ X y h (diagonalTraceLinearMap a)
  have hp := hh (StarPolynomial.power (.var ()) m)
  simpa only [StarPolynomial.eval_power,StarPolynomial.eval,compressionLimit] using hp.1

lemma matrixTrace_tensor_identity {A : Type} [Fintype A] [DecidableEq A]
    [Nonempty A] [Nonempty K] (M : Matrix A A ℂ) :
    matrixTrace (Matrix.kronecker M (1 : Matrix K K ℂ))=matrixTrace M := by
  have hK : (Fintype.card K:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  unfold matrixTrace
  rw [Matrix.kronecker,Matrix.trace_kronecker,Matrix.trace_one,Fintype.card_prod,Nat.cast_mul]
  field_simp
  ring

/-- Amplification leaves every normalized empirical moment unchanged. -/
lemma amplified_compression_moment {A : Type} [Fintype A] [DecidableEq A]
    [Nonempty A] [Nonempty K] (a : K → ℝ)
    (X : Matrix (A×K) (A×K) ℂ) (m : ℕ) :
    matrixTrace ((amplify (diagonalTraceLinearMap a) X)^m)=
      matrixTrace ((blockCompression (diagonalBlock X) a)^m) := by
  rw [amplified_diagonalTrace]
  have hh := (matrixTensorIdentity (n:=A) (k:=K)).map_pow
    (blockCompression (diagonalBlock X) a) m
  change Matrix.kronecker ((blockCompression (diagonalBlock X) a)^m) (1 : Matrix K K ℂ)=
    (Matrix.kronecker (blockCompression (diagonalBlock X) a) (1 : Matrix K K ℂ))^m at hh
  rw [← hh,matrixTrace_tensor_identity]

/-- The moment limit holds for the actual n-dimensional block compression,
not only its tensor amplification. -/
theorem unamplified_compression_moment_limit [Nonempty K]
    (I : ℕ → Type) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]
    (σ : B → ℂ) (X : ∀ n,Matrix (I n×K) (I n×K) ℂ) (y : Option (K×K) → B)
    (h : StronglyConverges (fun n => @matrixTrace (I n×K) _) σ
      (fun n => blockVariables (X n)) y) (a : K → ℝ) (m : ℕ) :
    Tendsto (fun n => matrixTrace ((blockCompression (diagonalBlock (X n)) a)^m)) atTop
      (nhds (σ ((compressionLimit a y)^m))) := by
  simpa only [amplified_compression_moment] using
    compression_moment_limit I σ X y h a m

end StrongConvergenceBlock
