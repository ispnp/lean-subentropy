module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The squared radius of two independent standard real Gaussians,
divided by two, has unit exponential density. -/
@[expose] public section
noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Set
namespace SubentropyCertificates.Representations

private def energy (p : ℝ × ℝ) : ℝ := (p.1^2 + p.2^2) / 2

private theorem radial_substitution (f : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), r * f (r^2 / 2)) = ∫ t in Ioi (0 : ℝ), f t := by
  let u (r : ℝ) := r^2 / 2
  have himage : u '' Ioi 0 = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨r, hr, rfl⟩
      change 0 < r^2 / 2
      exact div_pos (sq_pos_of_pos hr) zero_lt_two
    · intro ht
      refine ⟨√(2*t), sqrt_pos.mpr (mul_pos zero_lt_two ht), ?_⟩
      change (√(2*t))^2 / 2 = t
      rw [sq_sqrt (mul_nonneg zero_le_two ht.le)]
      ring
  have hd (r : ℝ) (_ : r ∈ Ioi (0 : ℝ)) : HasDerivWithinAt u r (Ioi 0) r := by
    have h := ((hasDerivAt_pow 2 r).div_const 2).hasDerivWithinAt (s := Ioi 0)
    convert h using 1
    simp
  have hinj : InjOn u (Ioi 0) := by
    intro x hx y hy hxy
    change x^2 / 2 = y^2 / 2 at hxy
    exact (sq_eq_sq₀ hx.le hy.le).mp (by linarith)
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj f
  rw [himage] at h
  rw [h]
  exact setIntegral_congr_fun measurableSet_Ioi fun r hr => by
    rw [abs_of_pos hr, smul_eq_mul]

private theorem plane_radial_integral (f : ℝ → ℝ) :
    (∫ p : ℝ × ℝ, f (energy p)) = (2 * π) * ∫ t in Ioi (0 : ℝ), f t := by
  have henergy (p : ℝ × ℝ) : energy (polarCoord.symm p) = p.1^2 / 2 := by
    simp only [energy, polarCoord_symm_apply, mul_pow]
    rw [← mul_add, cos_sq_add_sin_sq, mul_one]
  rw [← integral_comp_polarCoord_symm, polarCoord_target]
  simp_rw [henergy, smul_eq_mul]
  have hprod := setIntegral_prod_mul (μ := volume) (ν := volume)
    (s := Ioi (0 : ℝ)) (t := Ioo (-π) π) (fun r => r * f (r^2 / 2)) (fun _ => (1 : ℝ))
  simp only [mul_one, ← volume_eq_prod] at hprod
  rw [hprod, radial_substitution]
  simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
    volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [pi_pos]), smul_eq_mul]
  ring

theorem gaussian_pair_integral (f : ℝ → ℝ) :
    (∫ p : ℝ × ℝ, f ((p.1^2 + p.2^2) / 2) ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ t in Ioi (0 : ℝ), exp (-t) * f t := by
  let d := gaussianPDF 0 1
  have hm : Measurable (fun p : ℝ × ℝ => d p.1 * d p.2) :=
    ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd)
  have htop (p : ℝ × ℝ) : d p.1 * d p.2 < ⊤ :=
    ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top
  have hd (x y : ℝ) :
      gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 y =
      (2 * π)⁻¹ * exp (-energy (x,y)) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, energy]
    rw [mul_mul_mul_comm, ← mul_inv, ← sq, sq_sqrt (by positivity), ← exp_add]
    congr 2
    ring
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    ← volume_eq_prod, integral_withDensity_eq_integral_toReal_smul hm (.of_forall htop)]
  simp only [d, ENNReal.toReal_mul, toReal_gaussianPDF, smul_eq_mul, hd, mul_assoc]
  rw [integral_const_mul]
  change (2 * π)⁻¹ * (∫ p : ℝ × ℝ, exp (-energy p) * f (energy p)) = _
  rw [plane_radial_integral (fun t => exp (-t) * f t)]
  field_simp

theorem gaussian_coordinate_integral {D : Type*} [Fintype D] (i : D) (f : ℝ → ℝ)
    (hf : Measurable f) :
    (∫ z : (D × Fin 2) → ℝ, f (((z (i,0))^2 + (z (i,1))^2) / 2)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) = ∫ t in Ioi (0 : ℝ), exp (-t) * f t := by
  let μ := fun _ : D × Fin 2 => gaussianReal 0 1
  let pair (z : (D × Fin 2) → ℝ) := (z (i,0), z (i,1))
  have hind := iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hne : (i, (0 : Fin 2)) ≠ (i, 1) := by simp
  have hmap : (Measure.pi μ).map pair = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    have h := (hind.indepFun hne).map_prod_eq_prod_map_map
      (measurable_pi_apply (i,0)).aemeasurable (measurable_pi_apply (i,1)).aemeasurable
    exact h.trans (congrArg₂ Measure.prod (measurePreserving_eval μ (i,0)).map_eq
      (measurePreserving_eval μ (i,1)).map_eq)
  rw [← gaussian_pair_integral f, ← hmap, integral_map]
  · exact ((measurable_pi_apply (i,0)).prodMk (measurable_pi_apply (i,1))).aemeasurable
  · exact (hf.comp (show Measurable energy by unfold energy; fun_prop)).aestronglyMeasurable

end SubentropyCertificates.Representations
