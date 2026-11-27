module

public import SubentropyCertificates.PositiveBlockSegment
public import SubentropyCertificates.CommonMixTraceDistance
public import D5.S3.Quantum.Subentropy.DensityKernel

/-! Continuity of conditional subentropy under common mixing, including at singular blocks. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace SubentropyCertificates.ConditionalContinuity
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- Along a segment of normalized positive semidefinite blocks, continuity of the joint
and marginal subentropies holds up to both endpoints. -/
theorem blockConditionalQ_segment_continuousOn (A U : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hu : ∀ x, (U x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htu : (∑ x, U x).trace = 1) :
    ContinuousOn (fun e ↦ blockConditionalQ (blockSegment A U e)) (Icc 0 1) := by
  have hj : Continuous (fun e : ℝ ↦ blockDiagonal (blockSegment A U e)) := by
    change Continuous (fun e : ℝ ↦ blockDiagonal ((1-e) • A + e • U))
    simp only [blockDiagonal_add, blockDiagonal_smul]
    fun_prop
  have hm : Continuous (fun e : ℝ ↦ ∑ x, blockSegment A U e x) := by
    unfold blockSegment
    fun_prop
  apply (continuousOn_matrixSubentropy.comp hj.continuousOn _).sub
    (continuousOn_matrixSubentropy.comp hm.continuousOn _)
  · intro e he
    refine ⟨blocks_posSemidef _ (blockSegment_posSemidef A U ha hu he), ?_⟩
    simpa only [trace_blockDiagonal, trace_sum] using blockSegment_trace A U e hta htu
  · intro e he
    exact ⟨(Finset.sum_nonneg fun x _ ↦ (blockSegment_posSemidef A U ha hu he x).nonneg).posSemidef,
      blockSegment_trace A U e hta htu⟩

/-- Removing a common admixture recovers the conditional subentropy of the endpoint. -/
theorem blockConditionalQ_mix_tendsto (A U : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hu : ∀ x, (U x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htu : (∑ x, U x).trace = 1) :
    Tendsto (fun e ↦ blockConditionalQ (blockSegment A U e)) (𝓝[Ioc (0 : ℝ) 1] 0)
      (𝓝 (blockConditionalQ A)) := by
  have hz : blockSegment A U 0 = A := by funext x; simp [blockSegment]
  have hc := (blockConditionalQ_segment_continuousOn A U ha hu hta htu 0
    (show (0 : ℝ) ∈ Icc 0 1 by simp)).mono Ioc_subset_Icc_self
  simpa only [hz] using hc.tendsto

end SubentropyCertificates.ConditionalContinuity
