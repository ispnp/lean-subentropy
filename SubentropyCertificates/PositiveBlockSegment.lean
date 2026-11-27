module

public import SubentropyCertificates.ConditionalFrechet
public import D5.S3.Quantum.Foundation.FiniteStateChannel

/-! Normalized CQ states and the derivative of conditional subentropy along their segment. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace SubentropyCertificates.ConditionalContinuity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.Basic
open SubentropyCertificates.Representations

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- The joint density with classical label x and subnormalized quantum blocks A x. -/
def blockDensity (A : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef)
    (ht : (∑ x, A x).trace = 1) : DensityState (D × X) :=
  ⟨CStarMatrix.ofMatrix (blockDiagonal A),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (blocks_posSemidef A ha).nonneg,
    by
      change (blockDiagonal A).trace = 1
      simpa only [trace_blockDiagonal, trace_sum] using ht⟩

/-- Conditional subentropy written in terms of the subnormalized quantum blocks. -/
def blockConditionalQ (A : X → Matrix D D ℂ) : ℝ :=
  matrixSubentropy (blockDiagonal A) - matrixSubentropy (∑ x, A x)

/-- The affine segment between two families of blocks. -/
def blockSegment (A B : X → Matrix D D ℂ) (s : ℝ) (x : X) : Matrix D D ℂ :=
  (1 - s) • A x + s • B x

omit [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D] in
theorem blockSegment_posDef (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosDef) (hb : ∀ x, (B x).PosDef)
    {s : ℝ} (hs : s ∈ Icc 0 1) (x : X) : (blockSegment A B s x).PosDef := by
  rcases eq_or_lt_of_le hs.1 with he | hp
  · subst s
    simpa [blockSegment] using ha x
  · exact Matrix.PosDef.posSemidef_add ((ha x).posSemidef.smul (sub_nonneg.mpr hs.2))
      ((hb x).smul hp)

omit [DecidableEq X] [DecidableEq D] in
theorem blockSegment_trace (A B : X → Matrix D D ℂ) (s : ℝ)
    (ha : (∑ x, A x).trace = 1) (hb : (∑ x, B x).trace = 1) :
    (∑ x, blockSegment A B s x).trace = 1 := by
  simp only [blockSegment, Finset.sum_add_distrib, ← Finset.smul_sum, trace_add, trace_smul,
    ha, hb, Complex.real_smul, mul_one, Complex.ofReal_sub, Complex.ofReal_one, sub_add_cancel]

omit [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D] in
private theorem segment_shift (A B : X → Matrix D D ℂ) (s t : ℝ) (x : X) :
    blockSegment A B s x + (t - s) • (B x - A x) = blockSegment A B t x := by
  simp only [blockSegment, sub_smul, smul_sub, one_smul]
  abel

/-- The derivative at parameter s uses the same Hermitian direction B−A for the full segment. -/
theorem blockSegment_hasDerivAt [Nonempty X] (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosDef) (hb : ∀ x, (B x).PosDef)
    (htrA : (∑ x, A x).trace = 1) (htrB : (∑ x, B x).trace = 1)
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    HasDerivAt (fun t ↦ blockConditionalQ (blockSegment A B t))
      (∑ x, (((spatialSign (∑ y, blockSegment A B s y) - blockSpatialSign (blockSegment A B s) x) *
        (B x - A x)).trace).re) s := by
  let H := fun x ↦ B x - A x
  have hz : (∑ x, H x).trace = 0 := by
    simp only [H, Finset.sum_sub_distrib, trace_sub, htrA, htrB, sub_self]
  have hd := conditionalSubentropy_gradient (blockSegment A B s) H
    (blockSegment_posDef A B ha hb hs) (blockSegment_trace A B s htrA htrB)
    (fun x ↦ (hb x).isHermitian.sub (ha x).isHermitian) hz
  have hs' : HasDerivAt (fun t : ℝ ↦ t - s) 1 s := (hasDerivAt_id s).sub_const s
  simpa only [Function.comp_def, H, segment_shift, mul_one, blockConditionalQ] using
    hd.comp_of_eq s hs' (sub_self s).symm

/-- The Gaussian normalized outer product has norm at most one, hence so does its expectation. -/
theorem spatialSign_norm_le_one {M : Matrix D D ℂ} (hm : M.PosSemidef) : ‖spatialSign M‖ ≤ 1 := by
  let : IsProbabilityMeasure (circularGaussian D) := by unfold circularGaussian; infer_instance
  rw [spatialSign_gaussian_expectation hm]
  calc
    _ ≤ ∫ g, ‖gaussianSign M g‖ ∂circularGaussian D := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : V D, (1 : ℝ) ∂circularGaussian D := integral_mono (gaussianSign_integrable hm).norm
      (integrable_const _) (gaussianSign_norm_le_one hm)
    _ = 1 := by simp

end SubentropyCertificates.ConditionalContinuity
