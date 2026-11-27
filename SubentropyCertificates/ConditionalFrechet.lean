module

public import SubentropyCertificates.ConditionalGaussianGradient
public import SubentropyCertificates.GaussianFrechet

/-! The real Fréchet derivative of conditional subentropy's Gaussian extension. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open D5.S3.Quantum.Subentropy.Basic

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

private abbrev marginalBlockMap : (X → Matrix D D ℂ) →L[ℝ] Matrix D D ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H ↦ ∑ x, H x
      map_add' := fun _ _ ↦ by simp [Finset.sum_add_distrib]
      map_smul' := fun _ _ ↦ by simp [Finset.smul_sum] }

private abbrev jointBlockMap : (X → Matrix D D ℂ) →L[ℝ] Matrix (D × X) (D × X) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := blockDiagonal
      map_add' := blockDiagonal_add
      map_smul' := blockDiagonal_smul }

/-- The real-linear functional obtained by pairing each perturbation with its block gradient. -/
def conditionalGradientCLM (A : X → Matrix D D ℂ) : (X → Matrix D D ℂ) →L[ℝ] ℝ :=
  ∑ x, (gradientPairingCLM
    (commonLogMean A • 1 + (spatialSign (∑ y, A y) - blockSpatialSign A x))).comp
      (ContinuousLinearMap.proj x)

@[simp] theorem conditionalGradientCLM_apply (A H : X → Matrix D D ℂ) :
    conditionalGradientCLM A H =
      ∑ x, (((commonLogMean A • 1 + (spatialSign (∑ y, A y) - blockSpatialSign A x)) *
        H x).trace).re := by
  simp [conditionalGradientCLM]

/-- At positive definite blocks the Gaussian extension is Fréchet differentiable with
respect to all blocks simultaneously. Its derivative acts by the stated block trace pairings. -/
theorem conditionalGaussianF_hasFDerivAt [Nonempty X] (A : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosDef) :
    HasFDerivAt conditionalGaussianF (conditionalGradientCLM A) A := by
  have hm := (gaussianF_hasFDerivAt (sum_blocks_posDef A ha)).comp A marginalBlockMap.hasFDerivAt
  have hj := (gaussianF_hasFDerivAt (blocks_posDef A ha)).comp A jointBlockMap.hasFDerivAt
  apply (hm.sub hj).congr_fderiv
  ext H
  change ((gaussianSlope (∑ x, A x) * ∑ x, H x).trace).re -
    ((gaussianSlope (blockDiagonal A) * blockDiagonal H).trace).re = conditionalGradientCLM A H
  rw [gaussianSlope_eq (sum_blocks_posDef A ha), gaussianSlope_eq (blocks_posDef A ha),
    conditionalGradientCLM_apply]
  exact conditional_pairing A H (fun x ↦ (ha x).posSemidef)

/-- On normalized positive semidefinite blocks, conditional subentropy has the same
Fréchet derivative within the state space at every family of positive definite blocks. -/
theorem conditionalSubentropy_hasFDerivWithinAt [Nonempty X] (A : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosDef) (ht : (∑ x, A x).trace = 1) :
    HasFDerivWithinAt
      (fun B : X → Matrix D D ℂ ↦ matrixSubentropy (blockDiagonal B) - matrixSubentropy (∑ x, B x))
      (conditionalGradientCLM A) {B | (∀ x, (B x).PosSemidef) ∧ (∑ x, B x).trace = 1} A := by
  apply (conditionalGaussianF_hasFDerivAt A ha).hasFDerivWithinAt.congr'
  · exact fun B hB ↦ (conditionalGaussianF_eq_subentropy B hB.1 hB.2).symm
  · exact ⟨fun x ↦ (ha x).posSemidef, ht⟩

end SubentropyCertificates.ConditionalContinuity
