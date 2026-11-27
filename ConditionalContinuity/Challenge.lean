module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Sharp trace-distance continuity bounds for conditional subentropy

Theorem 14 and Corollary 15 in Section 4.2 of Pratik Patil,
*Quantum Subentropy: Subadditivity and Sharp Bounds on Discrimination Error* (arXiv:2611.30220v1).
-/

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

/-- Theorem 14, equation (28), with the quantum marginal interpolated along the segment. -/
theorem weighted_path_bound (ρ σ : CQState n m) :
    let d := traceDistance ρ σ
    let w := ∫ s in (0 : ℝ)..1, kappa ((1 - s) • marginal ρ + s • marginal σ)
    |conditionalSubentropy σ - conditionalSubentropy ρ| ≤ d * w ∧ d * w ≤ d := by
  sorry

/-- For distinct joint states the bound with coefficient one is strict. -/
theorem strict_global_bound (ρ σ : CQState n m) (h : joint ρ ≠ joint σ) :
    |conditionalSubentropy σ - conditionalSubentropy ρ| < traceDistance ρ σ := by
  sorry

/-- One is the least valid coefficient in each fixed pair of admissible dimensions. -/
theorem optimal_global_coefficient (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    IsLeast {c : ℝ | ∀ ρ σ : CQState n m,
      |conditionalSubentropy σ - conditionalSubentropy ρ| ≤ c * traceDistance ρ σ} 1 := by
  sorry

/-- With one label the conditional subentropy vanishes for every state. -/
theorem single_label (ρ : CQState 1 m) : conditionalSubentropy ρ = 0 := by
  sorry

/-- Corollary 15, equation (30), for two states with a common quantum marginal. -/
theorem fixed_marginal_bound (ρ σ : CQState n m) (τ : Matrix (Fin m) (Fin m) ℂ)
    (hρ : marginal ρ = τ) (hσ : marginal σ = τ) :
    |conditionalSubentropy σ - conditionalSubentropy ρ| ≤ kappa τ * traceDistance ρ σ := by
  sorry

/-- Within each fixed marginal τ, including singular τ, κ(τ) is the least valid coefficient. -/
theorem optimal_fixed_marginal_coefficient (n : ℕ) (hn : 2 ≤ n)
    (τ : Matrix (Fin m) (Fin m) ℂ) (hτ : τ.PosSemidef) (ht : τ.trace = 1) :
    IsLeast {c : ℝ | ∀ ρ σ : CQState n m, marginal ρ = τ → marginal σ = τ →
      |conditionalSubentropy σ - conditionalSubentropy ρ| ≤ c * traceDistance ρ σ} (kappa τ) := by
  sorry

/-- The maximally mixed marginal has coefficient 1/m. -/
theorem kappa_maximally_mixed (m : ℕ) (hm : 1 ≤ m) :
    kappa ((1 / (m : ℂ)) • (1 : Matrix (Fin m) (Fin m) ℂ)) = 1 / (m : ℝ) := by
  sorry

/-- A pure marginal has coefficient one. -/
theorem kappa_pure (τ : Matrix (Fin m) (Fin m) ℂ) (hτ : τ.PosSemidef) (ht : τ.trace = 1)
    (hp : τ.rank = 1) : kappa τ = 1 := by
  sorry

/-- A mixed marginal has coefficient strictly less than one. -/
theorem kappa_mixed (τ : Matrix (Fin m) (Fin m) ℂ) (hτ : τ.PosSemidef) (ht : τ.trace = 1)
    (hmix : 1 < τ.rank) : kappa τ < 1 := by
  sorry

end SubentropyConditionalContinuity
