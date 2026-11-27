module

public import SubentropyCertificates.FixedMarginalBound
public import SubentropyCertificates.FixedMarginalTable
public import SubentropyCertificates.FixedMarginalBlocks
public import SubentropyCertificates.FixedMarginalSlope
public import SubentropyCertificates.FixedMarginalSpectrum

/-! Corollary 15: the sharp trace distance coefficient with a prescribed quantum marginal. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set Filter MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.SpectralContinuity (maximallyMixed_matrix)

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- Transfer mass e along spectral coordinate i between two labels. The fixed marginal is
exact even at the boundary. The signed subentropy increment equals e times the split slope. -/
theorem fixedMarginal_split_pair {M : Matrix D D ℂ} (hM : M.PosSemidef) (ht : M.trace = 1)
    (a b : X) (hab : a ≠ b) (i : D) {e : ℝ} (he : e ∈ Icc 0 (hM.isHermitian.eigenvalues i)) :
    ∃ (A B : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
      (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1),
      (∑ x, A x) = M ∧ (∑ x, B x) = M ∧
      traceDistance (blockDensity A ha hta) (blockDensity B hb htb) = e ∧
      blockConditionalQ B - blockConditionalQ A = e * splitSlope hM.isHermitian.eigenvalues i e := by
  let w := hM.isHermitian.eigenvalues
  let U := hM.isHermitian.eigenvectorUnitary
  let p := splitTable a b w i
  have hw : w ∈ probabilitySimplex D := by
    refine ⟨hM.eigenvalues_nonneg, ?_⟩
    have hs := hM.isHermitian.trace_eq_sum_eigenvalues
    rw [ht] at hs
    simpa [w] using congrArg Complex.re hs.symm
  have hp {r : ℝ} (hr : r ∈ Icc 0 (w i)) :
      (fun z : D × X ↦ p r z.2 z.1) ∈ probabilitySimplex (D × X) :=
    splitPrior_probability a b hab hw i hr
  have h0 := hp (r := 0) ⟨le_rfl, hw.1 i⟩
  have h1 := hp he
  have hm (r : ℝ) : (∑ x, spectralBlocks U (p r) x) = M := by
    rw [spectralBlocks_sum]
    simp only [p, splitTable_column a b hab]
    exact hM.isHermitian.spectral_theorem.symm
  refine ⟨_, _, spectralBlocks_posSemidef U _ h0, spectralBlocks_posSemidef U _ h1,
    spectralBlocks_trace U _ h0, spectralBlocks_trace U _ h1, hm 0, hm e, ?_, ?_⟩
  · exact (spectralBlocks_traceDistance U _ _ h0 h1).trans (splitPrior_distance a b hab w i he.1)
  · rw [spectralBlocks_conditionalQ, spectralBlocks_conditionalQ, hm, hm, sub_sub_sub_cancel_right]
    exact splitPrior_increment a b hab hw i he

/-- Each smaller coefficient fails at arbitrarily small positive distance on the same
fixed-marginal set. The witnessing spectral coordinate always has positive mass. -/
theorem cq_fixed_marginal_sharp_near_zero (hn : 2 ≤ Fintype.card X) {M : Matrix D D ℂ}
    (hM : M.PosSemidef) (ht : M.trace = 1) {c δ : ℝ} (hc : c < ‖spatialSign M‖) (hδ : 0 < δ) :
    ∃ (A B : X → Matrix D D ℂ) (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
      (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1),
      let d := traceDistance (blockDensity A ha hta) (blockDensity B hb htb)
      (∑ x, A x) = M ∧ (∑ x, B x) = M ∧ 0 < d ∧ d < δ ∧
        c * d < |blockConditionalQ B - blockConditionalQ A| := by
  obtain ⟨a,b,hab⟩ := Fintype.one_lt_card_iff.mp hn
  obtain ⟨i, hi, htop⟩ := exists_spatialSign_top_coordinate hM ht
  let w := hM.isHermitian.eigenvalues
  have hlim := splitSlope_tendsto w hM.eigenvalues_nonneg i hi
  change (∫ t in Ioi (0:ℝ), w i / (1+t*w i) * ∏ j, (1+t*w j)⁻¹) = _ at htop
  rw [htop] at hlim
  have hnear : ∀ᶠ e : ℝ in 𝓝[>] 0, e ∈ Ioo 0 (min δ (w i)) :=
    Ioo_mem_nhdsGT_of_mem ⟨le_rfl,lt_min hδ hi⟩
  obtain ⟨e, he, hs⟩ := (hnear.and (hlim (Ioi_mem_nhds hc))).exists
  have hsmall := lt_min_iff.mp he.2
  obtain ⟨A,B,ha,hb,hta,htb,hA,hB,hd,hq⟩ :=
    fixedMarginal_split_pair hM ht a b hab i ⟨he.1.le,hsmall.2.le⟩
  refine ⟨A,B,ha,hb,hta,htb,hA,hB,hd ▸ he.1,hd ▸ hsmall.1,?_⟩
  rw [hd, hq, mul_comm e]
  exact (mul_lt_mul_of_pos_right hs he.1).trans_le (le_abs_self _)

/-- Corollary 15. On each fixed marginal the optimal coefficient is the norm of K(M).
The last three clauses evaluate or bound this norm for the maximally mixed, pure and mixed cases. -/
theorem cq_fixed_marginal_continuity (X : Type*) [Fintype X] [DecidableEq X]
    {M : Matrix D D ℂ} (hM : M.PosSemidef) (ht : M.trace = 1) :
    ‖spatialSign M‖ ∈ fixedMarginalCoefficients X M ∧
    (2 ≤ Fintype.card X → IsLeast (fixedMarginalCoefficients X M) ‖spatialSign M‖) ∧
    (M = (1 / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ) →
      ‖spatialSign M‖ = 1 / (Fintype.card D : ℝ)) ∧
    (M.rank = 1 → ‖spatialSign M‖ = 1) ∧ (1 < M.rank → ‖spatialSign M‖ < 1) := by
  have hu := cq_fixed_marginal_bound X M
  refine ⟨hu, ?_, ?_, spatialSign_norm_eq_one_of_rank_one hM, spatialSign_norm_lt_one_of_rank hM⟩
  · intro hn
    refine ⟨hu, ?_⟩
    intro c hbound
    by_contra! hc
    obtain ⟨A,B,ha,hb,hta,htb,hA,hB,_,_,hgap⟩ :=
      cq_fixed_marginal_sharp_near_zero hn hM ht hc (δ := 1) zero_lt_one
    exact (hbound A B ha hb hta htb hA hB).not_gt hgap
  · intro hm
    have : Nonempty D := by
      by_contra h
      have := not_nonempty_iff.mp h
      simp [Matrix.trace] at ht
    rw [hm, ← maximallyMixed_matrix D]
    exact spatialSign_norm_maximallyMixed D

end SubentropyCertificates.ConditionalContinuity
