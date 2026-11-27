module

public import SubentropyCertificates.GaussianGradientDefs
public import SubentropyCertificates.SpatialSignBlockDiagonal

/-! The common scalar and the block trace pairings in the conditional gradient. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations
open D5.S3.Quantum.Subentropy.Basic

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- The Gaussian extension of conditional subentropy to positive blocks. -/
def conditionalGaussianF (A : X → Matrix D D ℂ) := gaussianF (∑ x, A x) - gaussianF (blockDiagonal A)

/-- The scalar shared by every block gradient. -/
def commonLogMean (A : X → Matrix D D ℂ) := gaussianLogMean (∑ x, A x) - gaussianLogMean (blockDiagonal A)

/-- The Gaussian extension agrees with conditional subentropy on the trace-one slice. -/
theorem conditionalGaussianF_eq_subentropy (A : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef)
    (ht : (∑ x, A x).trace = 1) :
    conditionalGaussianF A = matrixSubentropy (blockDiagonal A) - matrixSubentropy (∑ x, A x) := by
  have hs : (∑ x, A x).PosSemidef := (Finset.sum_nonneg fun x _ ↦ (ha x).nonneg).posSemidef
  have hb : (blockDiagonal A).trace = 1 := by simpa only [trace_blockDiagonal, trace_sum] using ht
  rw [(gaussian_representation _ (blocks_posSemidef A ha) hb).2,
    (gaussian_representation _ hs ht).2]
  unfold conditionalGaussianF gaussianF
  ring

private theorem expanded_pairing (r : ℝ) (K H : Matrix D D ℂ) :
    (((r • (1 : Matrix D D ℂ) + K) * H).trace).re = r * H.trace.re + (K * H).trace.re := by
  simp [Matrix.add_mul, Matrix.trace_add, Matrix.trace_smul, Complex.real_smul]

/-- Subtracting the marginal and joint gradient pairings gives the same scalar I
for each label and the block correction K(A) - K_x(R). -/
theorem conditional_pairing (A H : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef) :
    let M := ∑ x, A x
    let R := blockDiagonal A
    let total := (∑ x, H x)
    (((1 + gaussianLogMean M) • 1 + spatialSign M) * total).trace.re -
      (((1 + gaussianLogMean R) • 1 + spatialSign R) * blockDiagonal H).trace.re =
      ∑ x, (((commonLogMean A • 1 + (spatialSign M - blockSpatialSign A x)) * H x).trace).re := by
  dsimp only
  rw [expanded_pairing, expanded_pairing, spatialSign_blockDiagonal A ha, ← blockDiagonal_mul,
    trace_blockDiagonal, trace_blockDiagonal, trace_sum, Complex.re_sum, Complex.re_sum,
    Matrix.mul_sum, trace_sum, Complex.re_sum]
  simp only [expanded_pairing, Matrix.sub_mul, trace_sub, Complex.sub_re,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, commonLogMean]
  ring

omit [DecidableEq X] in
/-- Along total-trace-zero directions the common scalar contributes zero. -/
theorem common_scalar_cancels (c : ℝ) (K H : X → Matrix D D ℂ) (ht : (∑ x, H x).trace = 0) :
    (∑ x, (((c • 1 + K x) * H x).trace).re) = ∑ x, ((K x * H x).trace).re := by
  have hr := congrArg Complex.re ht
  simp only [trace_sum, Complex.re_sum, Complex.zero_re] at hr
  simp only [expanded_pairing, Finset.sum_add_distrib, ← Finset.mul_sum, hr, mul_zero, zero_add]

end SubentropyCertificates.ConditionalContinuity
