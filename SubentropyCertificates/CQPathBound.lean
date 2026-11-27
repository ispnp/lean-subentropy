module

public import SubentropyCertificates.PositiveDefinitePathBound
public import SubentropyCertificates.MaximallyMixedBlocks
public import SubentropyCertificates.BlockSubentropyLimit
public import SubentropyCertificates.PathWeightLimit

/-! The weighted path bound for arbitrary finite CQ states (Theorem 14). -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.MixedQubit (traceDistance)

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

omit [DecidableEq X] [DecidableEq D] in
private theorem nonempty_of_total_trace_one (A : X → Matrix D D ℂ) (ht : (∑ x, A x).trace = 1) :
    Nonempty X ∧ Nonempty D := by
  constructor
  · cases isEmpty_or_nonempty X with
    | inl h => simp at ht
    | inr h => exact h
  · cases isEmpty_or_nonempty D with
    | inl h => simp [Matrix.trace] at ht
    | inr h => exact h

/-- Theorem 14, equation (cq-path-bound). Both endpoint families need only be positive
semidefinite and normalized. The integral uses the actual marginal at every point on the
original segment, and the distance is that of the full joint CQ states. -/
theorem cq_path_bound (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1) :
    let d := traceDistance (blockDensity A ha hta) (blockDensity B hb htb)
    let weight := ∫ s in (0 : ℝ)..1, ‖spatialSign (∑ x, blockSegment A B s x)‖
    |blockConditionalQ B - blockConditionalQ A| ≤ d * weight ∧ d * weight ≤ d := by
  obtain ⟨hX, hD⟩ := nonempty_of_total_trace_one A hta
  let U := uniformBlocks X D
  let mix (C : X → Matrix D D ℂ) (e : ℝ) := blockSegment C U e
  let w (C E : X → Matrix D D ℂ) := ∫ s in (0 : ℝ)..1, ‖spatialSign (∑ x, blockSegment C E s x)‖
  let d := traceDistance (blockDensity A ha hta) (blockDensity B hb htb)
  let l := 𝓝[Ioc (0 : ℝ) 1] 0
  have : NeBot l := by
    rw [show l = 𝓝[>] (0 : ℝ) from nhdsWithin_Ioc_eq_nhdsGT zero_lt_one]
    infer_instance
  have hu : ∀ x, (U x).PosSemidef := fun x ↦ (uniformBlocks_posDef X D x).posSemidef
  have htu : (∑ x, U x).trace = 1 := uniformBlocks_trace X D
  have hw : Tendsto (fun e ↦ w (mix A e) (mix B e)) l (𝓝 (w A B)) :=
    pathWeight_mix_tendsto A B U ha hb hu hta htb htu
  have hd : Tendsto (fun e : ℝ ↦ (1-e)*d) l (𝓝 d) := by
    have hc : Continuous (fun e : ℝ ↦ (1-e)*d) := by fun_prop
    simpa [l] using (hc.continuousAt (x := 0)).continuousWithinAt
      (s := Ioc (0 : ℝ) 1) |>.tendsto
  have hq := ((blockConditionalQ_mix_tendsto B U hb hu htb htu).sub
    (blockConditionalQ_mix_tendsto A U ha hu hta htu)).abs
  have hi : ∀ᶠ e in l,
      |blockConditionalQ (mix B e) - blockConditionalQ (mix A e)| ≤
        (1-e)*d * w (mix A e) (mix B e) ∧ (1-e)*d * w (mix A e) (mix B e) ≤ (1-e)*d := by
    filter_upwards [self_mem_nhdsWithin] with e he
    have hs := positiveDefinite_cq_path_bound (mix A e) (mix B e)
      (uniformMix_posDef X D A ha he) (uniformMix_posDef X D B hb he)
      (blockSegment_trace A U e hta htu) (blockSegment_trace B U e htb htu)
    have heq := commonMix_traceDistance A B U ha hb hu hta htb htu (Ioc_subset_Icc_self he)
    dsimp only at hs
    rw [heq] at hs
    exact hs
  exact ⟨le_of_tendsto_of_tendsto hq (hd.mul hw) (hi.mono fun _ h ↦ h.1),
    le_of_tendsto_of_tendsto (hd.mul hw) hd (hi.mono fun _ h ↦ h.2)⟩

end SubentropyCertificates.ConditionalContinuity
