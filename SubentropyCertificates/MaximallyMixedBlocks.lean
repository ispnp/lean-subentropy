module

public import SubentropyCertificates.PositiveBlockSegment
public import SubentropyCertificates.SubentropyMaximum

/-! Mixing CQ blocks with the maximally mixed joint state. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.BinarySpectra (densityMatrix)
open SubentropyCertificates.SpectralContinuity (maximallyMixed maximallyMixed_matrix)

/-- Each label receives the same block of the maximally mixed joint state. -/
def uniformBlocks (X D : Type*) [Fintype X] [Fintype D] [DecidableEq D] : X → Matrix D D ℂ :=
  fun _ ↦ (1 / (Fintype.card (D × X) : ℝ)) • 1

variable (X D : Type*) [Fintype X] [Fintype D] [DecidableEq X] [DecidableEq D]
  [Nonempty X] [Nonempty D]

omit [DecidableEq X] in
theorem uniformBlocks_posDef (x : X) : (uniformBlocks X D x).PosDef := by
  have hp : 0 < (Fintype.card (D × X) : ℝ) := by exact_mod_cast Fintype.card_pos
  exact Matrix.PosDef.one.smul (one_div_pos.mpr hp)

/-- The direct sum of the regularizing blocks is precisely the joint state I/(nm). -/
theorem uniformBlocks_blockDiagonal :
    blockDiagonal (uniformBlocks X D) = densityMatrix (maximallyMixed (D × X)) := by
  rw [maximallyMixed_matrix]
  change blockDiagonal ((1 / (Fintype.card (D × X) : ℝ)) • (1 : X → Matrix D D ℂ)) = _
  rw [blockDiagonal_smul, blockDiagonal_one]
  change ((1 / (Fintype.card (D × X) : ℝ) : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) = _
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]

theorem uniformBlocks_trace : (∑ x, uniformBlocks X D x).trace = 1 := by
  rw [trace_sum, ← trace_blockDiagonal, uniformBlocks_blockDiagonal]
  exact (maximallyMixed (D × X)).2.2

omit [DecidableEq X] in
/-- A positive mixing weight gives positive definite blocks, including at any zero input block. -/
theorem uniformMix_posDef (A : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef)
    {e : ℝ} (he : e ∈ Ioc 0 1) (x : X) :
    (blockSegment A (uniformBlocks X D) e x).PosDef :=
  Matrix.PosDef.posSemidef_add ((ha x).smul (sub_nonneg.mpr he.2))
    ((uniformBlocks_posDef X D x).smul he.1)

end SubentropyCertificates.ConditionalContinuity
