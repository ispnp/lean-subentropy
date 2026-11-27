module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# A sharp lower bound on quantum state discrimination error from conditional subentropy

Theorem 1 and the inverse bound following it in Section 1.2 of Pratik Patil,
*Quantum Subentropy: Subadditivity and Sharp Bounds on Discrimination Error* (arXiv:2611.30220v1).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ComplexOrder

namespace SubentropySharpGuessing

/-- A normalized ensemble of density matrices with labels in `Fin n`. Priors may vanish. -/
structure Ensemble (n : ℕ) (B : Type*) [Fintype B] where
  prior : Fin n → ℝ
  prior_nonneg : ∀ x, 0 ≤ prior x
  prior_sum : ∑ x, prior x = 1
  signal : Fin n → Matrix B B ℂ
  signal_pos : ∀ x, (signal x).PosSemidef
  signal_trace : ∀ x, (signal x).trace = 1

/-- The determinant integral of Lemma 3 gives the subentropy of a density matrix,
including when some eigenvalues coincide or vanish. -/
def subentropy {D : Type*} [Fintype D] [DecidableEq D] (A : Matrix D D ℂ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t / (1 + t) - ((1 + (t⁻¹ : ℝ) • A).det.re)⁻¹

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

/-- The joint classical–quantum state has diagonal blocks `p x • ρ x`. -/
def jointState (E : Ensemble n B) : Matrix (Fin n × B) (Fin n × B) ℂ :=
  fun i j ↦ if i.1 = j.1 then (E.prior i.1 : ℂ) * E.signal i.1 i.2 j.2 else 0

/-- Conditional subentropy is the subentropy of the joint state minus that of the average signal. -/
def conditionalSubentropy (E : Ensemble n B) : ℝ :=
  subentropy (jointState E) - subentropy (∑ x, E.prior x • E.signal x)

/-- These are the success probabilities of measurements with one positive effect per
label and effects summing to the identity. -/
def successProbabilities (E : Ensemble n B) : Set ℝ :=
  {a | ∃ M : Fin n → Matrix B B ℂ, (∀ x, (M x).PosSemidef) ∧ ∑ x, M x = 1 ∧
    a = ∑ x, E.prior x * ((M x * E.signal x).trace).re}

/-- The sharp guessing bound below includes attainment of this supremum. -/
def pGuess (E : Ensemble n B) : ℝ := sSup (successProbabilities E)

def error (E : Ensemble n B) : ℝ := 1 - pGuess E

def maxError (n : ℕ) : ℝ := 1 - 1 / (n : ℝ)

/-- One label has mass `1 - e` and each of the other labels has mass `e / (n - 1)`. -/
def extremalPrior (n k : ℕ) (e : ℝ) (x : Fin n) : ℝ :=
  if x.val = k then 1 - e else e / ((n : ℝ) - 1)

/-- For two or more labels, the distinguished coordinate of the curve is label zero. -/
def phi (n : ℕ) (e : ℝ) : ℝ :=
  subentropy (Matrix.diagonal (fun x : Fin n ↦ (extremalPrior n 0 e x : ℂ)))

/-- The inverse is used on the range of the admissible branch, including both endpoints. -/
def phiInverse (n : ℕ) (q : ℝ) : ℝ :=
  sInf {e : ℝ | e ∈ Icc 0 (maxError n) ∧ phi n e = q}

/-- Only signals with positive priors enter the perfect-discrimination criterion.
For positive matrices their supports are orthogonal exactly when their product vanishes. -/
def orthogonalSupports (E : Ensemble n B) : Prop :=
  ∀ x y, x ≠ y → 0 < E.prior x → 0 < E.prior y → E.signal x * E.signal y = 0

/-- The optimal measurement attains its success probability, and the full chain of bounds holds. -/
theorem sharp_guessing_bound (hn : 2 ≤ n) (E : Ensemble n B) :
    let e := error E
    let q := conditionalSubentropy E
    IsGreatest (successProbabilities E) (pGuess E) ∧ e ∈ Icc 0 (maxError n) ∧
      0 ≤ q ∧ q ≤ phi n e ∧ phi n e ≤ e ∧ e ≤ -Real.log (pGuess E) := by
  sorry

/-- At positive error, equality requires the stated prior and a common pure signal.
At the uniform endpoint any label can serve as the distinguished label. -/
theorem positive_error_equality (hn : 2 ≤ n) (E : Ensemble n B) (he : 0 < error E) :
    conditionalSubentropy E = phi n (error E) ↔
      (∃ k : Fin n, E.prior = extremalPrior n k.val (error E)) ∧
      ∃ v : B → ℂ, (∑ b, star (v b) * v b) = 1 ∧
        ∀ x, E.signal x = Matrix.vecMulVec v (star v) := by
  sorry

/-- Zero conditional subentropy, perfect discrimination, and orthogonality on the support
of the prior are equivalent. -/
theorem zero_error_equality (hn : 2 ≤ n) (E : Ensemble n B) :
    (conditionalSubentropy E = 0 ↔ error E = 0) ∧ (error E = 0 ↔ orthogonalSupports E) := by
  sorry

/-- Every admissible error attains the sharp curve in every positive signal dimension. -/
theorem curve_attainable (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B]
    (hn : 2 ≤ n) (e : ℝ) (he : e ∈ Icc 0 (maxError n)) :
    ∃ E : Ensemble n B, error E = e ∧ conditionalSubentropy E = phi n e := by
  sorry

/-- The curve is strictly below the linear bound at every positive admissible error. -/
theorem curve_lt_error (hn : 2 ≤ n) (e : ℝ) (he : 0 < e) (hmax : e ≤ maxError n) :
    phi n e < e := by
  sorry

/-- One is the smallest coefficient valid for all ensembles with these fixed dimensions. -/
theorem optimal_linear_coefficient (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B]
    (hn : 2 ≤ n) (c : ℝ) :
    (∀ E : Ensemble n B, conditionalSubentropy E ≤ c * error E) ↔ 1 ≤ c := by
  sorry

/-- With one label both quantities vanish, for every signal state. -/
theorem single_label (E : Ensemble 1 B) : error E = 0 ∧ conditionalSubentropy E = 0 := by
  sorry

/-- The curve is strictly increasing on its admissible interval. Each value between the
two endpoint values has a unique preimage there, given by `phiInverse`. -/
theorem inverse_on_branch (hn : 2 ≤ n) :
    StrictMonoOn (phi n) (Icc 0 (maxError n)) ∧ phi n 0 = 0 ∧
    phi n (maxError n) = Real.log (n : ℝ) - (harmonic n : ℝ) + 1 ∧
    ∀ q ∈ Icc 0 (phi n (maxError n)),
      phiInverse n q ∈ Icc 0 (maxError n) ∧ phi n (phiInverse n q) = q := by
  sorry

/-- The inverse bounds the error of each ensemble and is the attained minimum error at
each admissible conditional subentropy, even when the signal dimension is fixed. -/
theorem optimal_inverse_bound (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B]
    (hn : 2 ≤ n) :
    (∀ E : Ensemble n B, conditionalSubentropy E ∈ Icc 0 (phi n (maxError n)) ∧
      phiInverse n (conditionalSubentropy E) ≤ error E) ∧
    ∀ q ∈ Icc 0 (phi n (maxError n)),
      IsLeast {r : ℝ | ∃ E : Ensemble n B, conditionalSubentropy E = q ∧ error E = r}
        (phiInverse n q) := by
  sorry

end SubentropySharpGuessing
