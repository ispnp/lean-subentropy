module

public import SubentropyCertificates.CQPathBound
public import SubentropyCertificates.QuantumLipschitz

/-! Strictness of conditional subentropy when the two quantum marginals agree. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.SpectralContinuity (subentropy_lt_traceDistance)
open D5.S3.Quantum.Subentropy.Basic (matrixSubentropy)

/-- This includes the common pure marginal case of Theorem 14. The equal marginal
terms cancel, leaving the ordinary subentropy difference of the two joint states. -/
theorem cq_strict_of_same_marginal {X D : Type*} [Fintype X] [DecidableEq X]
    [Fintype D] [DecidableEq D] (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1)
    (he : (∑ x, A x) = ∑ x, B x) (hne : blockDensity A ha hta ≠ blockDensity B hb htb) :
    |blockConditionalQ B - blockConditionalQ A| <
      traceDistance (blockDensity A ha hta) (blockDensity B hb htb) := by
  have h := subentropy_lt_traceDistance _ _ hne
  change |matrixSubentropy (blockDiagonal A) - matrixSubentropy (blockDiagonal B)| < _ at h
  rw [blockConditionalQ, blockConditionalQ, he, sub_sub_sub_cancel_right, abs_sub_comm]
  exact h

end SubentropyCertificates.ConditionalContinuity
