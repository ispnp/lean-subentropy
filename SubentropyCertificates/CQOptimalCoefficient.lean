module

public import SubentropyCertificates.CQStrictBound
public import SubentropyCertificates.PureSignalBlockEmbedding
public import SubentropyCertificates.BinarySharpPriors
public import SubentropyCertificates.LinearDiscrimination

/-! Sharpness of the coefficient one in every fixed pair of admissible dimensions. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.ClassicalCurve (phi uniformError_mem)
open SubentropyCertificates.QuantumEquality (pointMass)
open SubentropyCertificates.Discrimination (smaller_coefficient_fails_near_zero)

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- The real coefficients that bound the conditional subentropy difference by the joint
trace distance, with the label and quantum coordinate spaces fixed. -/
def cqLipschitzCoefficients (X D : Type*) [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D] :
    Set ℝ :=
  {c | ∀ (A B : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1),
    |blockConditionalQ B - blockConditionalQ A| ≤
      c * traceDistance (blockDensity A ha hta) (blockDensity B hb htb)}

/-- The paper's sharpness pair uses a single pure signal at j and transfers mass e
from label a to label b. The joint distance is e, and the conditional
subentropies are zero and the binary curve, respectively. -/
theorem cq_binary_sharpness_pair (j : D) (a b : X) (hab : a ≠ b) {e : ℝ} (he : e ∈ Icc 0 1) :
    let A := pureLabelBlocks j (pointMass a)
    let B := pureLabelBlocks j (binaryPrior a b e)
    ∃ (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
      (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1),
      traceDistance (blockDensity A ha hta) (blockDensity B hb htb) = e ∧
      blockConditionalQ A = 0 ∧ blockConditionalQ B = phi 0 e := by
  obtain ⟨hp, hq, hd, hzero, hcurve⟩ := binaryPrior_pair a b hab he
  refine ⟨pureLabelBlocks_posSemidef j _ hp, pureLabelBlocks_posSemidef j _ hq,
    pureLabelBlocks_trace j _ hp, pureLabelBlocks_trace j _ hq, ?_⟩
  exact ⟨(pureLabelBlocks_traceDistance j _ _ hp hq).trans hd,
    (pureLabelBlocks_conditionalQ j _ hp).trans hzero,
    (pureLabelBlocks_conditionalQ j _ hq).trans hcurve⟩

/-- Every coefficient below one fails at arbitrarily small positive joint trace distance.
The witnesses use a fixed pure signal in the prescribed quantum space. -/
theorem cq_lipschitz_sharp_near_zero (hn : 2 ≤ Fintype.card X) (hm : 1 ≤ Fintype.card D)
    {c δ : ℝ} (hc : c < 1) (hδ : 0 < δ) :
    ∃ (A B : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
      (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1),
      let d := traceDistance (blockDensity A ha hta) (blockDensity B hb htb)
      0 < d ∧ d < δ ∧ c * d < |blockConditionalQ B - blockConditionalQ A| := by
  obtain ⟨j⟩ : Nonempty D := Fintype.card_pos_iff.mp hm
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hn
  obtain ⟨e, hpos, hsmall, hadm, hgap⟩ := smaller_coefficient_fails_near_zero 0 hc hδ
  obtain ⟨ha, hb, hta, htb, hd, hzero, hcurve⟩ := cq_binary_sharpness_pair j a b hab
    (show e ∈ Icc (0 : ℝ) 1 from ⟨hpos.le, hadm.trans (uniformError_mem 0).2⟩)
  refine ⟨_, _, ha, hb, hta, htb, ?_⟩
  dsimp only
  rw [hd, hzero, hcurve, sub_zero]
  exact ⟨hpos, hsmall, hgap.trans_le (le_abs_self _)⟩

/-- One is the least admissible coefficient when there are at least two labels and the
quantum system has dimension at least one. -/
theorem cq_lipschitz_constant_isLeast (hn : 2 ≤ Fintype.card X) (hm : 1 ≤ Fintype.card D) :
    IsLeast (cqLipschitzCoefficients X D) 1 := by
  constructor
  · intro A B ha hb hta htb
    have h := cq_path_bound A B ha hb hta htb
    simpa only [one_mul] using h.1.trans h.2
  · intro c hbound
    by_contra! hc
    obtain ⟨A, B, ha, hb, hta, htb, _, _, hgap⟩ :=
      cq_lipschitz_sharp_near_zero hn hm hc (δ := 1) zero_lt_one
    exact (hbound A B ha hb hta htb).not_gt hgap

end SubentropyCertificates.ConditionalContinuity
