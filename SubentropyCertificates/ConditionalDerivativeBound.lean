module

public import SubentropyCertificates.HalfTracePairing
public import SubentropyCertificates.PositiveBlockSegment
public import SubentropyCertificates.ProjectionAlignment

/-! A trace-zero perturbation of a normalized CQ state gains a factor of one half. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.SpectralContinuity (traceDistance_comm)

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- The trace pairing with the conditional gradient costs at most κ times half the trace norm
of the joint perturbation. Only the total trace of all the blocks must vanish. -/
theorem conditionalGradient_pairing_bound (A H : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hh : ∀ x, (H x).IsHermitian) (hz : (∑ x, H x).trace = 0) :
    |∑ x, (((spatialSign (∑ y, A y) - blockSpatialSign A x) * H x).trace).re| ≤
      ‖spatialSign (∑ x, A x)‖ * ((∑ i, |(blockHermitian H hh).eigenvalues i|) / 2) := by
  apply block_pairing_half_bound _ H _ (norm_nonneg _) _ _ hh hz
  · exact fun x ↦ (spatialSign_block_gradient_order A ha x).1
  · exact fun x ↦ (spatialSign_block_gradient_order A ha x).2.1.trans
      (spatialSign_block_gradient_order A ha x).2.2

/-- The derivative of conditional subentropy itself at a positive definite normalized family,
in an arbitrary Hermitian direction of total trace zero. -/
theorem conditionalSubentropy_derivative_bound [Nonempty X] (A H : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosDef) (ht : (∑ x, A x).trace = 1)
    (hh : ∀ x, (H x).IsHermitian) (hz : (∑ x, H x).trace = 0) :
    |deriv (fun s : ℝ ↦ blockConditionalQ (fun x ↦ A x + s • H x)) 0| ≤
      ‖spatialSign (∑ x, A x)‖ * ((∑ i, |(blockHermitian H hh).eigenvalues i|) / 2) := by
  unfold blockConditionalQ
  rw [(conditionalSubentropy_gradient A H ha ht hh hz).deriv]
  exact conditionalGradient_pairing_bound A H (fun x ↦ (ha x).posSemidef) hh hz

private theorem sum_abs_congr {J : Type*} [Fintype J] [DecidableEq J] {M N : Matrix J J ℂ}
    (hm : M.IsHermitian) (hn : N.IsHermitian) (he : M = N) :
    (∑ i, |hm.eigenvalues i|) = ∑ i, |hn.eigenvalues i| := by
  subst N
  rfl

/-- For the direction from A to B, half the trace norm of the joint perturbation is the
project's trace distance between the two CQ density states. -/
theorem blockDifference_half_eq_traceDistance (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1) :
    (∑ i, |(blockHermitian (fun x ↦ B x - A x)
      (fun x ↦ (hb x).isHermitian.sub (ha x).isHermitian)).eigenvalues i|) / 2 =
      traceDistance (blockDensity A ha hta) (blockDensity B hb htb) := by
  rw [traceDistance_comm]
  unfold traceDistance
  congr 1
  apply sum_abs_congr
  exact blockDiagonal_sub B A

end SubentropyCertificates.ConditionalContinuity
