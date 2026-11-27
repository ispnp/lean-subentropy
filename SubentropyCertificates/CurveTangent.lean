module

public import SubentropyCertificates.CurveMonotonicity
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The right tangent to the subentropy error curve. In the determinant
integral the derivative at zero is the same inverse square in every dimension.
The coordinate bound for the kernel also dominates its difference quotient. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped BigOperators Topology
namespace SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.KernelBounds
open D5.S3.Quantum.Subentropy.DensityKernel
open D5.S3.Quantum.Subentropy.UniformIntegrals

private def curveKernel (m : ℕ) (t e : ℝ) : ℝ :=
  subentropyKernel (diagonal (fun i => (extremalVector m e i : ℂ))) t

private theorem curveKernel_formula (m : ℕ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    curveKernel m t e = t / (1 + t) -
      (t / (t + (1 - e))) * (t / (t + e / (m + 1 : ℕ))) ^ (m + 1) := by
  simp only [curveKernel, kernel_diagonal _ t ht.ne', Fintype.prod_option, extremalVector,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem curveKernel_zero (m : ℕ) {t : ℝ} (ht : 0 < t) : curveKernel m t 0 = 0 := by
  simp [curveKernel_formula m ht, ht.ne', add_comm]

private theorem curveKernel_deriv_zero (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (curveKernel m t) (1 / (1 + t)^2) 0 := by
  let k : ℝ := (m + 1 : ℕ)
  have ht1 : t + 1 ≠ 0 := by linarith
  have hhead := (hasDerivAt_const (0 : ℝ) t).div
    ((hasDerivAt_const 0 t).add ((hasDerivAt_const 0 (1 : ℝ)).sub (hasDerivAt_id 0)))
    (by simpa using ht1)
  have htail := (hasDerivAt_const (0 : ℝ) t).div
    ((hasDerivAt_const 0 t).add ((hasDerivAt_id 0).div_const k)) (by simpa using ht.ne')
  have hd := (hasDerivAt_const (0 : ℝ) (t / (1 + t))).sub (hhead.mul (htail.pow (m + 1)))
  rw [show curveKernel m t = _ from funext (curveKernel_formula m ht)]
  convert hd using 1
  all_goals first
    | rfl
    | simp [k, ht.ne']
      field_simp [ht.ne', ht1, show 1 + t ≠ 0 by linarith, show (m : ℝ) + 1 ≠ 0 by positivity]
      ring

private theorem curveKernel_quotient_limit (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun e => curveKernel m t e / e) (𝓝[>] 0) (𝓝 (1 / (1 + t)^2)) := by
  simpa only [zero_add, curveKernel_zero m ht, sub_zero, smul_eq_mul, div_eq_inv_mul] using
    (curveKernel_deriv_zero m ht).tendsto_slope_zero_right

/-- The quotient along the full right neighborhood of zero for n=m+2 labels. -/
theorem phi_div_error_tendsto_one (m : ℕ) :
    Tendsto (fun e => phi m e / e) (𝓝[>] 0) (𝓝 1) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F (e t : ℝ) := curveKernel m t e / e
  let g (t : ℝ) := 1 / (1 + t)^2
  have hnear : ∀ᶠ e : ℝ in 𝓝[>] 0, e ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT_of_mem ⟨le_rfl, zero_lt_one⟩
  have hg : Integrable g μ ∧ (∫ t, g t ∂μ) = 1 := by
    change IntegrableOn g (Ioi (0 : ℝ)) ∧ (∫ t in Ioi (0 : ℝ), g t) = 1
    simpa [g, add_comm] using inverse_power 1 (by norm_num) 0
  have hmeas : ∀ᶠ e in 𝓝[>] 0, AEStronglyMeasurable (F e) μ := by
    filter_upwards [hnear] with e he
    have hA := diagonal_density (extremal_probability m ⟨he.1.le, he.2.le⟩)
    exact ((integrable_subentropy_kernel hA.1 hA.2).div_const e).aestronglyMeasurable
  have hbound : ∀ᶠ e in 𝓝[>] 0, ∀ᵐ t ∂μ, ‖F e t‖ ≤ g t := by
    filter_upwards [hnear] with e he
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp := extremal_probability m ⟨he.1.le, he.2.le⟩
    have h := classical_kernel_bounds (extremalVector m e) hp.1 hp.2 none t ht
    change 0 ≤ curveKernel m t e ∧ curveKernel m t e ≤ (1 - (1 - e)) / (1 + t)^2 at h
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h.1 he.1.le)]
    apply (div_le_iff₀ he.1).mpr
    calc
      curveKernel m t e ≤ (1 - (1 - e)) / (1 + t)^2 := h.2
      _ = g t * e := by dsimp [g]; ring
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun e => F e t) (𝓝[>] 0) (𝓝 (g t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact curveKernel_quotient_limit m ht
  have h := tendsto_integral_filter_of_dominated_convergence g hmeas hbound hg.1 hlim
  rw [hg.2] at h
  simpa only [F, μ, curveKernel, integral_div, phi, classicalSubentropy, matrixSubentropy] using h

theorem phi_hasDerivWithinAt_zero (m : ℕ) :
    HasDerivWithinAt (phi m) 1 (Ioi 0) 0 := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 from lt_irrefl _)).mpr
  simpa only [slope_fun_def_field, phi_zero, sub_zero] using phi_div_error_tendsto_one m

/-- Every positive chord lies strictly below the right tangent (including
the largest admissible error). The statement extends to the whole interval (0,1]. -/
theorem phi_lt_error (m : ℕ) {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) : phi m e < e := by
  have h := (phi_strictConcave m).slope_lt_of_hasDerivWithinAt_Ioi
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩) ⟨he.le, he1⟩ he
    (phi_hasDerivWithinAt_zero m)
  simpa only [slope_def_field, phi_zero, sub_zero, div_lt_one he] using h

end SubentropyCertificates.ClassicalCurve
