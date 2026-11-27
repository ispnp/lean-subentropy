module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Definitions for the sharp continuity bounds for conditional subentropy. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace SubentropyConditionalContinuity

/-- A classical–quantum state with n labels and quantum dimension m is a family
of positive semidefinite blocks whose traces add to one. Individual blocks may vanish. -/
structure CQState (n m : ℕ) where
  block : Fin n → Matrix (Fin m) (Fin m) ℂ
  pos : ∀ x, (block x).PosSemidef
  trace_one : (∑ x, block x).trace = 1

variable {n m : ℕ}

def joint (ρ : CQState n m) := blockDiagonal ρ.block

def marginal (ρ : CQState n m) := ∑ x, ρ.block x

/-- This is the determinant formula of Lemma 3 after the substitution t ↦ 1/t.
It applies to density matrices with repeated or zero eigenvalues. -/
def subentropy {D : Type*} [Fintype D] [DecidableEq D] (M : Matrix D D ℂ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t / (1 + t) - ((1 + (t⁻¹ : ℝ) • M).det.re)⁻¹

def conditionalSubentropy (ρ : CQState n m) : ℝ := subentropy (joint ρ) - subentropy (marginal ρ)

/-- The joint trace distance is half the sum of the absolute eigenvalues of the joint difference. -/
def traceDistance (ρ σ : CQState n m) : ℝ :=
  let hρ : (joint ρ).IsHermitian := isHermitian_blockDiagonal_iff.mpr fun x ↦ (ρ.pos x).isHermitian
  let hσ : (joint σ).IsHermitian := isHermitian_blockDiagonal_iff.mpr fun x ↦ (σ.pos x).isHermitian
  (∑ i, |(hρ.sub hσ).eigenvalues i|) / 2

/-- The determinant integral for K in equation (27). -/
def spatialSign (M : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ∫ t in Ioi (0 : ℝ), ((1 + t • M).det.re)⁻¹ • (M * (1 + t • M)⁻¹)

/-- The norm in κ is the operator norm for the Euclidean norm on the quantum space. -/
def kappa (M : Matrix (Fin m) (Fin m) ℂ) : ℝ := ‖spatialSign M‖

end SubentropyConditionalContinuity
