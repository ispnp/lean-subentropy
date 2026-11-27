module

public import SubentropyCertificates.GaussianEntropyDerivative
import all SubentropyCertificates.GaussianEntropyDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! The real Fréchet derivative of the Gaussian entropy functional. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology BigOperators

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The real linear functional induced by the trace pairing with `A`. -/
def gradientPairingCLM (A : Matrix D D ℂ) : Matrix D D ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H ↦ (A * H).trace.re
      map_add' := fun _ _ ↦ by simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun _ _ ↦ by simp [Matrix.trace_smul, Complex.real_smul] }

@[simp] theorem gradientPairingCLM_apply (A H : Matrix D D ℂ) :
    gradientPairingCLM A H = (A * H).trace.re := rfl

private def pairingAsMap :
    Matrix D D ℂ →L[ℝ] (Matrix D D ℂ →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := gradientPairingCLM
      map_add' := fun A B ↦ by ext H; simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun c A ↦ by ext H; simp [Matrix.trace_smul, Complex.real_smul] }

private theorem pairing_outer (g : V D) (H : Matrix D D ℂ) :
    gradientPairingCLM (gaussianOuter g) H = quadraticForm H g := outer_trace g H

private theorem pairing_outer_bound (g : V D) : ‖gradientPairingCLM (gaussianOuter g)‖ ≤ ‖g‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro H
  rw [pairing_outer, Real.norm_eq_abs, mul_comm]
  exact quadratic_bound H g

/-- At a positive definite matrix, the Gaussian functional is Fréchet differentiable
on the full real space of complex matrices. Its derivative pairs a perturbation with
the Gaussian slope by taking the real part of the trace. -/
theorem gaussianF_hasFDerivAt {M : Matrix D D ℂ} (hp : M.PosDef) :
    HasFDerivAt gaussianF (gradientPairingCLM (gaussianSlope M)) M := by
  obtain ⟨a, ha, hlow⟩ := quadratic_lower hp
  let r := a/2
  have hr : 0 < r := by dsimp [r]; positivity
  let b := ‖M‖+r
  have hball (N : Matrix D D ℂ) (hN : N ∈ Metric.ball M r) (g : V D) :
      r * ‖g‖^2 ≤ quadraticForm N g ∧ quadraticForm N g ≤ b * ‖g‖^2 := by
    have hd : ‖N-M‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hN
    have hq : quadraticForm (N-M) g = quadraticForm N g - quadraticForm M g := by
      simp only [← pairing_outer, map_sub]
    have hpq := quadratic_bound (N-M) g
    rw [hq] at hpq
    have hdiff := (abs_le.mp hpq).1
    have hN' : ‖N‖ ≤ b := by
      dsimp [b]
      have := norm_add_le (N-M) M
      rw [sub_add_cancel] at this
      linarith
    constructor
    · dsimp [r] at hd ⊢
      nlinarith only [hlow g, hdiff, mul_le_mul_of_nonneg_right hd.le (sq_nonneg ‖g‖)]
    · exact (le_abs_self _).trans ((quadratic_bound N g).trans
        (mul_le_mul_of_nonneg_right hN' (sq_nonneg _)))
  let f (N : Matrix D D ℂ) (g : V D) := quadraticForm N g * Real.log (quadraticForm N g)
  let z (N : Matrix D D ℂ) (g : V D) := (1+Real.log (quadraticForm N g)) •
    gradientPairingCLM (gaussianOuter g)
  have hm (N : Matrix D D ℂ) : Measurable (fun g : V D ↦ quadraticForm N g) := by
    unfold quadraticForm; fun_prop
  have hfm (N : Matrix D D ℂ) : Measurable (f N) :=
    (hm N).mul (Real.measurable_log.comp (hm N))
  have hmeas : AEStronglyMeasurable (z M) (circularGaussian D) := by
    have ho : Continuous (gaussianOuter (D := D)) := by unfold gaussianOuter Matrix.vecMulVec; fun_prop
    exact ((measurable_const.add (Real.measurable_log.comp (hm M))).smul
      ((pairingAsMap (D := D)).continuous.comp ho).measurable).aestronglyMeasurable
  have hprob := circular_probability (D := D)
  have hf : Integrable (f M) (circularGaussian D) := by
    apply ((integrable_const (1:ℝ)).add ((circular_pow 4 (D := D) (by decide)).const_mul
      (b^2))).mono' (hfm M).aestronglyMeasurable
    filter_upwards with g
    obtain ⟨hl,hu⟩ := hball M (Metric.mem_ball_self hr) g
    have hq : 0 ≤ quadraticForm M g := (mul_nonneg hr.le (sq_nonneg _)).trans hl
    change |quadraticForm M g * Real.log (quadraticForm M g)| ≤ 1 + b^2 * ‖g‖^4
    rw [abs_mul, abs_of_nonneg hq]
    nlinarith only [weighted_log_bound hq, pow_le_pow_left₀ hq hu 2]
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := circularGaussian D) (F := f) (F' := z) (bound := envelope r b)
    (Metric.ball_mem_nhds M hr) (.of_forall fun N ↦ (hfm N).aestronglyMeasurable) hf hmeas
    (by
      filter_upwards with g
      intro N hN
      obtain ⟨hl,hu⟩ := hball N hN g
      dsimp only [z]
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (pairing_outer_bound g) (abs_nonneg _)).trans
        (slope_bound hr g hl hu))
    (envelope_integrable r b) (by
      filter_upwards with g
      intro N hN
      by_cases hg : g = 0
      · subst g
        have ho : gaussianOuter (0 : V D) = 0 := by ext; simp [gaussianOuter, Matrix.vecMulVec]
        have hz : gradientPairingCLM (0 : Matrix D D ℂ) = 0 := by ext; simp
        simpa [f, z, quadraticForm, ho, hz] using
          (hasFDerivAt_const (c := (0 : ℝ)) N)
      · have hq : quadraticForm N g ≠ 0 := (lt_of_lt_of_le
          (mul_pos hr (sq_pos_of_pos (norm_pos_iff.mpr hg))) (hball N hN g).1).ne'
        have hquad : HasFDerivAt (fun U ↦ quadraticForm U g)
            (gradientPairingCLM (gaussianOuter g)) N := by
          simpa only [← pairing_outer] using (gradientPairingCLM (gaussianOuter g)).hasFDerivAt (x := N)
        simpa [f, z, Function.comp_def, add_comm] using
          (Real.hasDerivAt_mul_log hq).comp_hasFDerivAt N hquad)
  have hlin : (∫ g, pairingAsMap ((1+Real.log (quadraticForm M g)) • gaussianOuter g)
      ∂circularGaussian D) = gradientPairingCLM (gaussianSlope M) :=
    ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (Fₗ := Matrix D D ℂ →L[ℝ] ℝ)
      (pairingAsMap (D := D)) (gaussianSlope_integrable hp)
  rw [← hlin]
  apply hmain.congr_fderiv
  apply integral_congr_ae
  filter_upwards with g
  exact ((pairingAsMap (D := D)).map_smul (1+Real.log (quadraticForm M g)) (gaussianOuter g)).symm

/-- The line derivative follows by evaluating the Fréchet derivative in the direction H. -/
theorem gaussianF_hasDerivAt {M : Matrix D D ℂ} (hp : M.PosDef) (H : Matrix D D ℂ) :
    HasDerivAt (fun s : ℝ ↦ gaussianF (M + s • H)) ((gaussianSlope M * H).trace.re) 0 :=
  (gaussianF_hasFDerivAt hp).hasLineDerivAt H

end SubentropyCertificates.ConditionalContinuity

