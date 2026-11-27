module

public import SubentropyCertificates.CommonMarginalStrict
public import SubentropyCertificates.MixedMarginalNorm
public import SubentropyCertificates.MixedSegmentRank

/-! Strictness of the trace distance bound in Theorem 14. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.CompactStability (traceDistance_nonneg)
open SubentropyCertificates.SpectralContinuity (traceDistance_eq_zero_iff)

/-- The integral of the marginal coefficient is strictly less than one if it is strictly
less than one at a single point of the segment, including an endpoint. -/
theorem pathWeight_lt_one_of_exists {X D : Type*} [Fintype X] [Fintype D] [DecidableEq D]
    (A B : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1)
    (hw : ∃ t ∈ Icc (0 : ℝ) 1, ‖spatialSign (∑ x, blockSegment A B t x)‖ < 1) :
    (∫ t in (0 : ℝ)..1, ‖spatialSign (∑ x, blockSegment A B t x)‖) < 1 := by
  let M (t : ℝ) := ∑ x, blockSegment A B t x
  have hp (t : ℝ) (ht : t ∈ Icc 0 1) : (M t).PosSemidef :=
    (Finset.sum_nonneg fun x _ ↦ (blockSegment_posSemidef A B ha hb ht x).nonneg).posSemidef
  have hc : Continuous M := by unfold M blockSegment; fun_prop
  have hk : ContinuousOn (fun t ↦ ‖spatialSign (M t)‖) (Icc 0 1) :=
    kappa_continuousOn_density.comp hc.continuousOn
      (fun t ht ↦ ⟨hp t ht, blockSegment_trace A B t hta htb⟩)
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (g := fun _ ↦ (1 : ℝ)) zero_lt_one hk continuousOn_const
    (fun t ht ↦ spatialSign_norm_le_one (hp t (Ioc_subset_Icc_self ht))) hw
  simpa using hi

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

omit [DecidableEq X] in
/-- An interior marginal has rank greater than one exactly when the endpoint marginals
differ or their common value is mixed. Trace one excludes rank zero. -/
theorem interior_marginal_rank_gt_one_iff (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1)
    {s : ℝ} (hs : s ∈ Ioo 0 1) :
    1 < (∑ x, blockSegment A B s x).rank ↔
      (∑ x, A x) ≠ (∑ x, B x) ∨ 1 < (∑ x, A x).rank := by
  have hm : (∑ x, blockSegment A B s x) = (1-s) • (∑ x, A x) + s • (∑ x, B x) := by
    simp only [blockSegment, Finset.sum_add_distrib, Finset.smul_sum]
  rw [hm]
  by_cases he : (∑ x, A x) = ∑ x, B x
  · rw [← he, ← add_smul, sub_add_cancel, one_smul]
    simp
  · have hp := segment_rank_gt_one_of_ne (∑ x, A x) (∑ x, B x)
      (Finset.sum_nonneg fun x _ ↦ (ha x).nonneg).posSemidef
      (Finset.sum_nonneg fun x _ ↦ (hb x).nonneg).posSemidef hta htb he hs
    exact ⟨fun _ ↦ Or.inl he, fun _ ↦ hp⟩

omit [DecidableEq X] in
/-- Unless both endpoint marginals are the same pure state, the path coefficient has
integral strictly below one. It suffices to use strictness at the midpoint and continuity. -/
theorem pathWeight_lt_one_of_mixed_interior (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1)
    (hmix : (∑ x, A x) ≠ (∑ x, B x) ∨ 1 < (∑ x, A x).rank) :
    (∫ s in (0 : ℝ)..1, ‖spatialSign (∑ x, blockSegment A B s x)‖) < 1 := by
  apply pathWeight_lt_one_of_exists A B ha hb hta htb
  have hs : (1/2 : ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
  have hc := Ioo_subset_Icc_self hs
  refine ⟨1/2, hc, spatialSign_norm_lt_one_of_rank ?_ ?_⟩
  · exact (Finset.sum_nonneg fun x _ ↦
      (blockSegment_posSemidef A B ha hb hc x).nonneg).posSemidef
  · exact (interior_marginal_rank_gt_one_iff A B ha hb hta htb hs).2 hmix

/-- Theorem 14: for any two distinct finite CQ states, conditional subentropy changes
by strictly less than their joint trace distance. Zero-probability blocks are allowed. -/
theorem cq_subentropy_lt_traceDistance (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1)
    (hne : blockDensity A ha hta ≠ blockDensity B hb htb) :
    |blockConditionalQ B - blockConditionalQ A| <
      traceDistance (blockDensity A ha hta) (blockDensity B hb htb) := by
  by_cases hmix : (∑ x, A x) ≠ (∑ x, B x) ∨ 1 < (∑ x, A x).rank
  · have hw := pathWeight_lt_one_of_mixed_interior A B ha hb hta htb hmix
    have hd := lt_of_le_of_ne (traceDistance_nonneg (blockDensity A ha hta) (blockDensity B hb htb))
      (fun hz ↦ hne ((traceDistance_eq_zero_iff _ _).mp hz.symm))
    exact (cq_path_bound A B ha hb hta htb).1.trans_lt (by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hw hd)
  · have he : (∑ x, A x) = ∑ x, B x := by
      by_contra h
      exact hmix (Or.inl h)
    exact cq_strict_of_same_marginal A B ha hb hta htb he hne

end SubentropyCertificates.ConditionalContinuity
