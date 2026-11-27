module

public import SubentropyCertificates.SpatialSignSupport

/-! A mixed marginal has spatial sign norm strictly less than one. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A normalized positive semidefinite matrix of rank at least two has spectral norm below one. -/
theorem norm_lt_one_of_trace_one_of_rank {M : Matrix D D ℂ} (hM : M.PosSemidef)
    (ht : M.trace = 1) (hr : 1 < M.rank) : ‖M‖ < 1 := by
  let w := hM.isHermitian.eigenvalues
  have hc : 1 < Fintype.card {i // w i ≠ 0} := hM.isHermitian.rank_eq_card_non_zero_eigs ▸ hr
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hc
  have : Nonempty D := ⟨a.val⟩
  have hm := CStarAlgebra.norm_mem_spectrum_of_nonneg M hM.nonneg
  rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hm
  obtain ⟨i, hi⟩ := hm
  obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ 0 < w j := by
    by_cases ha : a.val = i
    · refine ⟨b.val, fun h ↦ hab (Subtype.ext (ha.trans h.symm)), ?_⟩
      exact lt_of_le_of_ne (hM.eigenvalues_nonneg b.val) b.property.symm
    · exact ⟨a.val, ha, lt_of_le_of_ne (hM.eigenvalues_nonneg a.val) a.property.symm⟩
  have hs : ∑ k, w k = 1 := by
    have h := hM.isHermitian.trace_eq_sum_eigenvalues
    rw [ht] at h
    simpa [w] using congrArg Complex.re h.symm
  have hle : w j ≤ ∑ k ∈ Finset.univ.erase i, w k :=
    Finset.single_le_sum (fun k _ ↦ hM.eigenvalues_nonneg k)
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  have he := Finset.sum_erase_add Finset.univ w (Finset.mem_univ i)
  change w i = ‖M‖ at hi
  linarith

/-- The spatial sign covariance of every matrix with at least two positive eigenvalues
has operator norm strictly less than one, including when the covariance is singular. -/
theorem spatialSign_norm_lt_one_of_rank {M : Matrix D D ℂ} (hM : M.PosSemidef)
    (hr : 1 < M.rank) : ‖spatialSign M‖ < 1 := by
  have hn : M ≠ 0 := by
    rintro rfl
    simp at hr
  exact norm_lt_one_of_trace_one_of_rank (spatialSign_posSemidef hM)
    (spatialSign_trace_one hM hn) ((spatialSign_rank hM).symm ▸ hr)

end SubentropyCertificates.ConditionalContinuity
