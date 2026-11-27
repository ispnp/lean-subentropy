module

public import SubentropyCertificates.SpatialSignSupport
import all SubentropyCertificates.SpatialSignSupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Boundary derivative for splitting mass out of a positive eigenvalue. -/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace SubentropyCertificates.ConditionalContinuity

variable {D : Type*} [Fintype D]

/-- The subentropy difference quotient after moving mass `e` out of coordinate `i`. -/
def splitSlope (w : D → ℝ) (i : D) (e : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (w i - e) / ((1 + t * (w i - e)) * (1 + t * e)) *
    ∏ j, (1 + t * w j)⁻¹

/-- Along a positive spectral coordinate the boundary slope tends to its spatial sign
weight. Other spectral coordinates may be zero. -/
theorem splitSlope_tendsto (w : D → ℝ) (hw : ∀ j, 0 ≤ w j) (i : D) (hi : 0 < w i) :
    Tendsto (splitSlope w i) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), w i / (1 + t * w i) * ∏ j, (1 + t * w j)⁻¹)) := by
  classical
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f (e t : ℝ) := (w i - e) / ((1 + t * (w i - e)) * (1 + t * e)) *
    ∏ j, (1 + t * w j)⁻¹
  let g (t : ℝ) := w i / (1 + t * w i) * ∏ j, (1 + t * w j)⁻¹
  have hg : Integrable g μ :=
    Integrable.of_integral_ne_zero fun h ↦ hi.ne' ((signWeight_zero_iff w hw i).mp h)
  have hnear : ∀ᶠ e in 𝓝[>] (0 : ℝ), e ∈ Ioo 0 (w i) :=
    Ioo_mem_nhdsGT_of_mem ⟨le_rfl, hi⟩
  apply tendsto_integral_filter_of_dominated_convergence (μ := μ) (F := f) (f := g) g
  · exact .of_forall fun e ↦ by apply Measurable.aestronglyMeasurable; dsimp [f]; fun_prop
  · filter_upwards [hnear] with e he
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hd : 0 < 1 + t * (w i - e) := by nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr he.2.le)]
    have hd' : 0 < 1 + t * e := by nlinarith [mul_nonneg ht0.le he.1.le]
    have hdw : 0 < 1 + t * w i := by positivity
    have hp : 0 ≤ ∏ j, (1 + t * w j)⁻¹ :=
      Finset.prod_nonneg fun j _ ↦ inv_nonneg.mpr (by nlinarith [mul_nonneg ht0.le (hw j)])
    have ha := sub_nonneg.mpr he.2.le
    dsimp only [f, g]
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg ha (mul_pos hd hd').le) hp)]
    apply mul_le_mul_of_nonneg_right _ hp
    calc
      _ ≤ (w i - e) / (1 + t * (w i - e)) := by
        apply div_le_div_of_nonneg_left ha hd
        nlinarith [mul_nonneg hd.le (mul_nonneg ht0.le he.1.le)]
      _ ≤ w i / (1 + t * w i) := (div_le_div_iff₀ hd hdw).mpr (by nlinarith [he.1.le])
  · exact hg
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hden : 1 + t * w i ≠ 0 := ne_of_gt (by positivity)
    have hc : ContinuousAt (fun e ↦ f e t) 0 := by
      dsimp only [f]
      fun_prop (disch := simp [hden])
    simpa [f, g] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))

end SubentropyCertificates.ConditionalContinuity
