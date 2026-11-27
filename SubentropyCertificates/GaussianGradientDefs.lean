module

public import SubentropyCertificates.SpatialSignOrder
public import SubentropyCertificates.RepresentationTheorem

/-! Gaussian functions used in the gradient of conditional subentropy. -/
@[expose] public section
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The quadratic form of a diagonal matrix in the circular Gaussian coordinates. -/
def diagonalEnergy (w : D → ℝ) (g : V D) : ℝ := ∑ j, w j * Complex.normSq (g j)

/-- The unnormalized outer product of a complex vector with itself. -/
def gaussianOuter (g : V D) : Matrix D D ℂ := vecMulVec (fun i ↦ g i) (fun i ↦ star (g i))

/-- The normalized outer product in the spatial sign formula. -/
def gaussianSign (M : Matrix D D ℂ) (g : V D) : Matrix D D ℂ :=
  (quadraticForm M g)⁻¹ • gaussianOuter (Matrix.toEuclideanLin (CFC.sqrt M) g)

/-- The logarithmic moment at the current matrix. -/
def gaussianLogMean (M : Matrix D D ℂ) : ℝ :=
  ∫ g, Real.log (quadraticForm M g) ∂circularGaussian D

/-- The Gaussian functional F(M) = E[T log T]. -/
def gaussianF (M : Matrix D D ℂ) : ℝ :=
  ∫ g, quadraticForm M g * Real.log (quadraticForm M g) ∂circularGaussian D

/-- The Gaussian matrix moment appearing when differentiating F. -/
def gaussianSlope (M : Matrix D D ℂ) : Matrix D D ℂ :=
  ∫ g, (1 + Real.log (quadraticForm M g)) • gaussianOuter g ∂circularGaussian D

end SubentropyCertificates.ConditionalContinuity
