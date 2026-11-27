module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Definitions for the sharp guessing solution

These definitions use the challenge's Mathlib imports so that Comparator can check their
elaborated terms before the companion's additional matrix instances enter scope.
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

end SubentropySharpGuessing
