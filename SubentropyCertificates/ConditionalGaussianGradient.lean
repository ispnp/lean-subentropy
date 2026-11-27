module

public import SubentropyCertificates.ConditionalGradientChain
public import SubentropyCertificates.GaussianSpatialSign
public import SubentropyCertificates.GaussianFrechet

/-! The conditional gradient in Appendix B, including the trace-one constraint. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace SubentropyCertificates.ConditionalContinuity
open D5.S3.Quantum.Subentropy.Basic

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- The derivative matrix of the Gaussian entropy functional at a positive definite matrix. -/
theorem gaussianSlope_eq {M : Matrix D D ℂ} (hM : M.PosDef) :
    gaussianSlope M = (1 + gaussianLogMean M) • 1 + spatialSign M :=
  gaussianSlope_eq_of_integrable hM (gaussianSlope_integrable hM)

/-- Along any matrix direction, the derivative is given by pairing with the spatial sign
matrix plus the scalar logarithmic moment. -/
theorem gaussianF_gradient {M : Matrix D D ℂ} (hM : M.PosDef) (H : Matrix D D ℂ) :
    HasDerivAt (fun s : ℝ ↦ gaussianF (M + s • H))
      ((((1 + gaussianLogMean M) • 1 + spatialSign M) * H).trace.re) 0 := by
  rw [← gaussianSlope_eq hM]
  exact gaussianF_hasDerivAt hM H

/-- The derivative of the Gaussian extension of conditional subentropy for perturbations
of all the positive definite blocks simultaneously. -/
theorem conditionalGaussianF_hasDerivAt [Nonempty X] (A H : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosDef) :
    HasDerivAt (fun s : ℝ ↦ conditionalGaussianF (fun x ↦ A x + s • H x))
      (∑ x, (((commonLogMean A • 1 + (spatialSign (∑ y, A y) - blockSpatialSign A x)) *
        H x).trace).re) 0 := by
  rw [← conditional_pairing A H (fun x ↦ (ha x).posSemidef)]
  have h := (gaussianF_gradient (sum_blocks_posDef A ha) (∑ x, H x)).sub
    (gaussianF_gradient (blocks_posDef A ha) (blockDiagonal H))
  convert h using 1
  funext s
  have hb : blockDiagonal (fun x ↦ A x + s • H x) =
      blockDiagonal A + s • blockDiagonal H := by
    exact (blockDiagonal_add A (s • H)).trans (by rw [blockDiagonal_smul])
  simp only [conditionalGaussianF, Finset.sum_add_distrib, ← Finset.smul_sum, hb, Pi.sub_apply]

/-- On the trace-one slice the scalar term disappears. This differentiates the paper's
conditional subentropy itself along every Hermitian direction of zero total trace. -/
theorem conditionalSubentropy_gradient [Nonempty X] (A H : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosDef) (ht : (∑ x, A x).trace = 1)
    (hh : ∀ x, (H x).IsHermitian) (hz : (∑ x, H x).trace = 0) :
    HasDerivAt (fun s : ℝ ↦
      matrixSubentropy (blockDiagonal (fun x ↦ A x + s • H x)) -
      matrixSubentropy (∑ x, (A x + s • H x)))
      (∑ x, (((spatialSign (∑ y, A y) - blockSpatialSign A x) * H x).trace).re) 0 := by
  have h := conditionalGaussianF_hasDerivAt A H ha
  rw [common_scalar_cancels _ _ H hz] at h
  apply h.congr_of_eventuallyEq
  have hp : ∀ᶠ s : ℝ in 𝓝 0, ∀ x, (A x + s • H x).PosDef :=
    Filter.eventually_all.mpr (fun x ↦ eventually_posDef_line (ha x) (hh x))
  filter_upwards [hp] with s hs
  apply (conditionalGaussianF_eq_subentropy _ (fun x ↦ (hs x).posSemidef) _).symm
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, trace_add, trace_smul, ht, hz, smul_zero, add_zero]

end SubentropyCertificates.ConditionalContinuity
