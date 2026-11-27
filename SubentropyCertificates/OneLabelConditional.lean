module

public import SubentropyCertificates.PositiveBlockSegment
import all SubentropyCertificates.MarginalEigenbasisTable

/-! Conditional subentropy on a one-label alphabet. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators

namespace SubentropyCertificates.ConditionalContinuity

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- With a single label, the joint matrix is a reindexing of the marginal matrix. -/
theorem blockConditionalQ_eq_zero_of_card_one (A : X → Matrix D D ℂ) (hX : Fintype.card X = 1) :
    blockConditionalQ A = 0 := by
  have ⟨u⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hX
  let e : D × X ≃ D := Equiv.prodUnique D X
  have h : blockDiagonal A = (A default).submatrix e e := by
    ext ⟨i, x⟩ ⟨j, y⟩
    rw [Subsingleton.elim x default, Subsingleton.elim y default, blockDiagonal_apply_eq]
    rfl
  rw [blockConditionalQ, h, QubitDeficit.reindex_subentropy, Fintype.sum_unique, sub_self]

end SubentropyCertificates.ConditionalContinuity
