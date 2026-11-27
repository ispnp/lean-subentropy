module

public import SubentropyCertificates.CQContinuityTheorem

/-! Specializing the CQ continuity inequality to a prescribed quantum marginal. -/
@[expose] public section
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.MixedQubit (traceDistance)

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- The admissible joint trace distance coefficients on the set of states with marginal M. -/
def fixedMarginalCoefficients (X : Type*) [Fintype X] [DecidableEq X] (M : Matrix D D ℂ) :
    Set ℝ :=
  {c | ∀ (A B : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1),
    (∑ x, A x) = M → (∑ x, B x) = M →
    |blockConditionalQ B - blockConditionalQ A| ≤
      c * traceDistance (blockDensity A ha hta) (blockDensity B hb htb)}

/-- The marginal is constant along the affine segment, so the path integral in Theorem 14
reduces to the operator norm of K(M), including when M is singular. -/
theorem cq_fixed_marginal_bound (X : Type*) [Fintype X] [DecidableEq X] (M : Matrix D D ℂ) :
    ‖spatialSign M‖ ∈ fixedMarginalCoefficients X M := by
  intro A B ha hb hta htb hA hB
  have hs (s : ℝ) : (∑ x, blockSegment A B s x) = M := by
    simp only [blockSegment, Finset.sum_add_distrib, ← Finset.smul_sum, hA, hB, ← add_smul,
      sub_add_cancel, one_smul]
  have h := ((cq_continuity_theorem X D).1 A B ha hb hta htb).1
  simpa only [hs, intervalIntegral.integral_const, sub_zero, one_smul, mul_comm] using h

end SubentropyCertificates.ConditionalContinuity
