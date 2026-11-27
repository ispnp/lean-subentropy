module

public import SubentropyCertificates.PositiveBlockSegment
public import SubentropyCertificates.DiagonalTraceDistance
public import SubentropyCertificates.QuantumEquality

/-! A fixed pure coordinate signal embeds the classical simplex into CQ states. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.ConditionalContinuity
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.QuantumEquality (pointMass pointMass_probability pointMass_subentropy)
open SubentropyCertificates.Continuity (totalVariation)
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.SpectralContinuity (diagonalDensity diagonalDensity_traceDistance)

variable {X D : Type*} [DecidableEq D] [Fintype D] [Fintype X] [DecidableEq X]

private def paddedPrior (j : D) (p : X → ℝ) (u : D × X) : ℝ :=
  if u.1 = j then p u.2 else 0

/-- The block for label x is its probability times the coordinate projection at j. -/
def pureLabelBlocks (j : D) (p : X → ℝ) (x : X) : Matrix D D ℂ :=
  diagonal (fun i ↦ ((if i = j then p x else 0 : ℝ) : ℂ))

omit [Fintype D] [DecidableEq X] in
theorem pureLabelBlocks_posSemidef (j : D) (p : X → ℝ) (hp : p ∈ probabilitySimplex X)
    (x : X) : (pureLabelBlocks j p x).PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  by_cases hi : i = j <;> simp [hi, Complex.le_def, hp.1 x]

omit [Fintype D] [DecidableEq X] in
private theorem marginal_eq_point (j : D) (p : X → ℝ) (hp : p ∈ probabilitySimplex X) :
    ∑ x, pureLabelBlocks j p x = diagonal (fun i ↦ (pointMass j i : ℂ)) := by
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases ha : a = j <;> simp [Matrix.sum_apply, pureLabelBlocks, pointMass, ha,
      ← Complex.ofReal_sum, hp.2]
  · simp [Matrix.sum_apply, pureLabelBlocks, Matrix.diagonal_apply_ne _ hab]

omit [DecidableEq X] in
theorem pureLabelBlocks_trace (j : D) (p : X → ℝ) (hp : p ∈ probabilitySimplex X) :
    (∑ x, pureLabelBlocks j p x).trace = 1 := by
  rw [marginal_eq_point j p hp]
  exact (diagonal_density (pointMass_probability j)).2

omit [Fintype D] [Fintype X] in
private theorem joint_eq_diagonal (j : D) (p : X → ℝ) :
    blockDiagonal (pureLabelBlocks j p) = diagonal (fun u ↦ (paddedPrior j p u : ℂ)) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  by_cases hab : a = b <;> by_cases hxy : x = y <;>
    simp [blockDiagonal_apply', pureLabelBlocks, Matrix.diagonal, paddedPrior, hab, hxy]

omit [DecidableEq X] in
private theorem padded_simplex (j : D) (p : X → ℝ) (hp : p ∈ probabilitySimplex X) :
    paddedPrior j p ∈ probabilitySimplex (D × X) := by
  refine ⟨fun u ↦ ?_, ?_⟩
  · unfold paddedPrior
    split <;> simp [hp.1]
  · rw [Fintype.sum_prod_type]
    calc
      _ = ∑ x, paddedPrior j p (j, x) := Finset.sum_eq_single j
        (fun i _ hi ↦ by simp [paddedPrior, hi]) (by simp)
      _ = 1 := by simpa [paddedPrior] using hp.2

private theorem padded_subentropy (j : D) (p : X → ℝ) :
    classicalSubentropy (paddedPrior j p) = classicalSubentropy p := by
  unfold classicalSubentropy matrixSubentropy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [kernel_diagonal _ t ht.ne', kernel_diagonal _ t ht.ne']
  congr 1
  rw [Fintype.prod_prod_type]
  calc
    _ = ∏ x, t / (t + paddedPrior j p (j, x)) := Finset.prod_eq_single j
      (fun i _ hi ↦ by simp [paddedPrior, hi, ht.ne']) (by simp)
    _ = _ := by simp [paddedPrior]

/-- A common pure signal leaves precisely the subentropy of the label distribution. -/
theorem pureLabelBlocks_conditionalQ (j : D) (p : X → ℝ) (hp : p ∈ probabilitySimplex X) :
    blockConditionalQ (pureLabelBlocks j p) = classicalSubentropy p := by
  rw [blockConditionalQ, joint_eq_diagonal, marginal_eq_point j p hp]
  change classicalSubentropy (paddedPrior j p) - classicalSubentropy (pointMass j) = _
  rw [padded_subentropy, pointMass_subentropy, sub_zero]

private theorem joint_density_eq (j : D) (p : X → ℝ) (hp : p ∈ probabilitySimplex X) :
    blockDensity (pureLabelBlocks j p) (pureLabelBlocks_posSemidef j p hp)
      (pureLabelBlocks_trace j p hp) = diagonalDensity _ (padded_simplex j p hp) :=
  Subtype.ext (congrArg CStarMatrix.ofMatrix (joint_eq_diagonal j p))

/-- Joint trace distance in the fixed pure signal embedding is exactly total variation. -/
theorem pureLabelBlocks_traceDistance (j : D) (p q : X → ℝ)
    (hp : p ∈ probabilitySimplex X) (hq : q ∈ probabilitySimplex X) :
    traceDistance
      (blockDensity (pureLabelBlocks j p) (pureLabelBlocks_posSemidef j p hp)
        (pureLabelBlocks_trace j p hp))
      (blockDensity (pureLabelBlocks j q) (pureLabelBlocks_posSemidef j q hq)
        (pureLabelBlocks_trace j q hq)) = totalVariation p q := by
  rw [joint_density_eq j p hp, joint_density_eq j q hq, diagonalDensity_traceDistance]
  unfold totalVariation
  congr 1
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x, |paddedPrior j p (j, x) - paddedPrior j q (j, x)| := Finset.sum_eq_single j
      (fun i _ hi ↦ by simp [paddedPrior, hi]) (by simp)
    _ = _ := by simp [paddedPrior]

end SubentropyCertificates.ConditionalContinuity

