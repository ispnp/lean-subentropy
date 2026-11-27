module

public import SubentropyCertificates.CommonMixTraceDistance
public import SubentropyCertificates.SpatialSignContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Convergence of the marginal path weight when both endpoints are mixed with a common state. -/
@[expose] public section
noncomputable section
open Matrix Set Filter MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace SubentropyCertificates.ConditionalContinuity

variable {X D : Type*} [Fintype X] [Fintype D] [DecidableEq D]

/-- The marginal coefficient is continuous on density matrices, including singular states. -/
theorem kappa_continuousOn_density :
    ContinuousOn (fun M : Matrix D D ℂ ↦ ‖spatialSign M‖) {M | M.PosSemidef ∧ M.trace = 1} := by
  intro M hM
  have hn : M ≠ 0 := by
    intro hz
    simpa [hz] using hM.2
  exact ((spatialSign_continuousWithinAt_posSemidef hM.1 hn).mono fun _ h ↦ h.1).norm

/-- The integral of the marginal operator norm along the jointly mixed segment converges to
the original path weight as the common mixing parameter tends to zero from above. -/
theorem pathWeight_mix_tendsto (A B U : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef) (hu : ∀ x, (U x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1) (htu : (∑ x, U x).trace = 1) :
    Tendsto (fun e : ℝ ↦ ∫ s in (0 : ℝ)..1,
        ‖spatialSign (∑ x, blockSegment (blockSegment A U e) (blockSegment B U e) s x)‖)
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 (∫ s in (0 : ℝ)..1, ‖spatialSign (∑ x, blockSegment A B s x)‖)) := by
  let M (p : ℝ × ℝ) := ∑ x, blockSegment (blockSegment A U p.1) (blockSegment B U p.1) p.2 x
  have hm : Continuous M := by unfold M blockSegment; fun_prop
  let I := Icc (0 : ℝ) 1
  have hM : MapsTo M (I ×ˢ I) {N | N.PosSemidef ∧ N.trace = 1} := by
    intro p hp
    have hA := blockSegment_posSemidef A U ha hu hp.1
    have hB := blockSegment_posSemidef B U hb hu hp.1
    exact ⟨(Finset.sum_nonneg fun x _ ↦ (blockSegment_posSemidef _ _ hA hB hp.2 x).nonneg).posSemidef,
      blockSegment_trace _ _ _ (blockSegment_trace A U p.1 hta htu)
        (blockSegment_trace B U p.1 htb htu)⟩
  let F (e s : ℝ) := ‖spatialSign (M (e, s))‖
  have hc : ContinuousOn (fun p ↦ ‖spatialSign (M p)‖) (I ×ˢ I) :=
    kappa_continuousOn_density.comp hm.continuousOn hM
  have hz (s : ℝ) : F 0 s = ‖spatialSign (∑ x, blockSegment A B s x)‖ := by
    simp [F, M, blockSegment]
  change Tendsto (fun e ↦ ∫ s in (0 : ℝ)..1, F e s) _ _
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with e he
    have hc' : ContinuousOn (F e) I :=
      hc.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hs ↦ ⟨Ioc_subset_Icc_self he, hs⟩)
    rw [uIoc_of_le zero_le_one]
    exact (hc'.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with e he
    filter_upwards with s
    intro hs
    rw [uIoc_of_le zero_le_one] at hs
    have h := (hM (show (e, s) ∈ I ×ˢ I from ⟨Ioc_subset_Icc_self he, Ioc_subset_Icc_self hs⟩)).1
    exact (Real.norm_of_nonneg (norm_nonneg _)).le.trans (spatialSign_norm_le_one h)
  · exact intervalIntegrable_const
  · filter_upwards with s
    intro hs
    rw [uIoc_of_le zero_le_one] at hs
    have hc' : ContinuousOn (fun e ↦ F e s) I :=
      hc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ he ↦ ⟨he, Ioc_subset_Icc_self hs⟩)
    rw [← hz]
    exact (hc' 0 (show 0 ∈ I from ⟨le_rfl, zero_le_one⟩)).mono Ioc_subset_Icc_self

end SubentropyCertificates.ConditionalContinuity
