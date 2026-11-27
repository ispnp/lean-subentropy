module

public import SubentropyCertificates.CQOptimalCoefficient
public import SubentropyCertificates.OneLabelConditional

/-! The complete statement of Theorem 14 for finite classical-quantum states. -/
@[expose] public section
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.MixedQubit (traceDistance)

/-- Theorem 14. The integral of the marginal spatial sign norm bounds the change in
conditional subentropy relative to joint trace distance. The coefficient one is strict
for distinct states and is optimal in each stated pair of dimensions. Conditional
subentropy vanishes identically for a one-label alphabet. -/
theorem cq_continuity_theorem (X D : Type*) [Fintype X] [DecidableEq X]
    [Fintype D] [DecidableEq D] :
    (∀ (A B : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef)
      (hb : ∀ x, (B x).PosSemidef) (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1),
      let ρ := blockDensity A ha hta
      let σ := blockDensity B hb htb
      let d := traceDistance ρ σ
      let w := ∫ s in (0 : ℝ)..1, ‖spatialSign (∑ x, blockSegment A B s x)‖
      |blockConditionalQ B - blockConditionalQ A| ≤ d * w ∧ d * w ≤ d ∧
        (ρ ≠ σ → |blockConditionalQ B - blockConditionalQ A| < d)) ∧
    (2 ≤ Fintype.card X → 1 ≤ Fintype.card D → IsLeast (cqLipschitzCoefficients X D) 1) ∧
    (Fintype.card X = 1 → ∀ A : X → Matrix D D ℂ, blockConditionalQ A = 0) := by
  refine ⟨?_, fun hn hm ↦ cq_lipschitz_constant_isLeast hn hm,
    fun hn A ↦ blockConditionalQ_eq_zero_of_card_one A hn⟩
  intro A B ha hb hta htb
  have h := cq_path_bound A B ha hb hta htb
  exact ⟨h.1, h.2, cq_subentropy_lt_traceDistance A B ha hb hta htb⟩

end SubentropyCertificates.ConditionalContinuity
