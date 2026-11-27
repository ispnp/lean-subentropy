module

public import SubentropyCertificates.ConditionalDerivativeBound
public import SubentropyCertificates.SpatialSignContinuity
public import SubentropyCertificates.PathIntegralComparison
public import SubentropyCertificates.TraceDistanceContinuity

/-! The path bound of Theorem 14 for CQ states with positive definite endpoint blocks. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.CompactStability (traceDistance_nonneg)

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D] [Nonempty X]

/-- The coefficient in Theorem 14 is continuous on the closed segment of positive definite
blocks. It uses only the quantum marginal at each parameter. -/
theorem blockSegment_kappa_continuousOn (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosDef) (hb : ∀ x, (B x).PosDef) :
    ContinuousOn (fun s : ℝ ↦ ‖spatialSign (∑ x, blockSegment A B s x)‖) (Icc 0 1) := by
  have hm : Continuous (fun s : ℝ ↦ ∑ x, blockSegment A B s x) := by
    unfold blockSegment
    fun_prop
  exact (spatialSign_continuousOn_posDef.comp hm.continuousOn
    (fun s hs ↦ sum_blocks_posDef _ (blockSegment_posDef A B ha hb hs))).norm

/-- The positive definite case of the two inequalities in the path bound. The distance is
the trace distance of the full CQ states; κ is evaluated at the marginal of each mixture. -/
theorem positiveDefinite_cq_path_bound (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosDef) (hb : ∀ x, (B x).PosDef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1) :
    let d := traceDistance (blockDensity A (fun x ↦ (ha x).posSemidef) hta)
      (blockDensity B (fun x ↦ (hb x).posSemidef) htb)
    let weight := ∫ s in (0 : ℝ)..1, ‖spatialSign (∑ x, blockSegment A B s x)‖
    |blockConditionalQ B - blockConditionalQ A| ≤ d * weight ∧ d * weight ≤ d := by
  let H := fun x ↦ B x - A x
  let k := fun s : ℝ ↦ ‖spatialSign (∑ x, blockSegment A B s x)‖
  let v := fun s : ℝ ↦ ∑ x, (((spatialSign (∑ y, blockSegment A B s y) -
    blockSpatialSign (blockSegment A B s) x) * H x).trace).re
  let f := fun s ↦ blockConditionalQ (blockSegment A B s)
  let d := traceDistance (blockDensity A (fun x ↦ (ha x).posSemidef) hta)
    (blockDensity B (fun x ↦ (hb x).posSemidef) htb)
  have hd : 0 ≤ d := traceDistance_nonneg _ _
  have hh : ∀ x, (H x).IsHermitian := fun x ↦ (hb x).isHermitian.sub (ha x).isHermitian
  have hz : (∑ x, H x).trace = 0 := by simp [H, Finset.sum_sub_distrib, hta, htb]
  have he : (∑ i, |(blockHermitian H hh).eigenvalues i|) / 2 = d :=
    blockDifference_half_eq_traceDistance A B _ _ hta htb
  have hk : ContinuousOn k (Icc 0 1) := blockSegment_kappa_continuousOn A B ha hb
  have hf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (v s) s :=
    fun _ hs ↦ blockSegment_hasDerivAt A B ha hb hta htb hs
  have hv (s : ℝ) (hs : s ∈ Icc 0 1) : |v s| ≤ k s * d := by
    rw [← he]
    exact conditionalGradient_pairing_bound _ H
      (fun x ↦ (blockSegment_posDef A B ha hb hs x).posSemidef) hh hz
  constructor
  · have hi := abs_sub_le_integral_of_deriv_bound f v k d hk hf hv
    have h₀ : blockSegment A B 0 = A := by funext x; simp [blockSegment]
    have h₁ : blockSegment A B 1 = B := by funext x; simp [blockSegment]
    simpa only [f, h₀, h₁] using hi
  · apply weighted_path_integral_le k hd hk
    intro s hs
    exact spatialSign_norm_le_one (sum_blocks_posDef _ (blockSegment_posDef A B ha hb hs)).posSemidef

end SubentropyCertificates.ConditionalContinuity
