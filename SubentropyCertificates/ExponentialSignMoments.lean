module

public import SubentropyCertificates.ExponentialEntropy
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Independence.Basic

/-! Radial integrals for independent unit exponential coordinates. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Topology ENNReal
namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations

local instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

private theorem ae_nonneg_exp : ∀ᵐ x ∂expMeasure 1, 0 ≤ x := by
  rw [expMeasure, gammaMeasure]
  apply (ae_withDensity_iff (f := gammaPDF 1 1) (by
    exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 1))).mpr
  exact .of_forall fun x hx ↦ le_of_not_gt (fun h ↦ hx (gammaPDF_of_neg h))

private theorem pi_positive {D : Type*} [Fintype D] :
    ∀ᵐ z ∂Measure.pi (fun _ : D ↦ expMeasure 1), ∀ j, 0 ≤ z j := by
  rw [ae_all_iff]
  intro j
  exact (measurePreserving_eval (fun _ : D ↦ expMeasure 1) j).quasiMeasurePreserving.ae
    ae_nonneg_exp

private theorem exp_radial_factor (a : ℝ) (ha : 0 ≤ a) :
    (∫ z, exp (-(a*z)) ∂expMeasure 1) = (1+a)⁻¹ := by
  rw [unit_exponential_integral]
  simp_rw [← exp_add, show ∀ z : ℝ, -z + -(a*z) = (-(1+a))*z by intro z; ring]
  rw [integral_exp_mul_Ioi (by linarith : -(1+a) < 0)]
  simp only [mul_zero, exp_zero, neg_div_neg_eq, one_div]

private theorem exp_radial_first_moment (a : ℝ) (ha : 0 ≤ a) :
    (∫ z, z * exp (-(a*z)) ∂expMeasure 1) = (1+a)⁻¹ * (1+a)⁻¹ := by
  rw [unit_exponential_integral]
  have hh := integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0:ℝ)<2)
    (by linarith : 0 < 1+a)
  norm_num [one_div] at hh
  calc
    _ = ∫ z in Ioi (0:ℝ), z * exp (-((1+a)*z)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z _
      dsimp only
      rw [mul_left_comm, ← exp_add]
      ring_nf
    _ = _ := by simpa [sq] using hh

private theorem tilted_exp_moment {D : Type*} [Fintype D] [DecidableEq D]
    (w : D → ℝ) (hw : ∀ j, 0 ≤ w j) (i : D) (t : ℝ) (ht : 0 ≤ t) :
    (∫ z : D → ℝ, w i*z i*exp (-(t*(∑ j, w j*z j))) ∂Measure.pi (fun _ ↦ expMeasure 1)) =
      (w i / (1+t*w i)) * ∏ j, (1+t*w j)⁻¹ := by
  let f (j : D) (x : ℝ) := (if j = i then x else 1) * exp (-((t*w j)*x))
  have eq (z : D → ℝ) : w i*z i*exp (-(t*(∑ j, w j*z j))) = w i*∏ j, f j (z j) := by
    simp only [f, Finset.prod_mul_distrib, ← exp_sum, ← Finset.sum_neg_distrib, Finset.mul_sum,
      mul_assoc]
    simp
  simp_rw [eq, integral_const_mul, integral_fintype_prod_eq_prod]
  have term (j : D) : (∫ x, f j x ∂expMeasure 1) =
      (if j = i then (1+t*w i)⁻¹ else 1) * (1+t*w j)⁻¹ := by
    by_cases h : j = i
    · subst j
      simpa [f] using exp_radial_first_moment (t*w i) (mul_nonneg ht (hw i))
    · simpa [f,h] using exp_radial_factor (t*w j) (mul_nonneg ht (hw j))
  simp only [term, Finset.prod_mul_distrib]
  simp [div_eq_mul_inv, mul_assoc]

/-- The expected fraction of the total energy contributed by coordinate i equals its
determinant integral. Zero individual weights and zero total energy are allowed. -/
theorem exponential_sign_integral {D : Type*} [Fintype D] [DecidableEq D]
    (w : D → ℝ) (hw : ∀ j, 0 ≤ w j) (i : D) :
    (∫ z : D → ℝ, w i*z i/(∑ j, w j*z j) ∂Measure.pi (fun _ ↦ expMeasure 1)) =
      ∫ t in Ioi (0:ℝ), (w i/(1+t*w i)) * ∏ j, (1+t*w j)⁻¹ := by
  let μ := Measure.pi (fun _ : D ↦ expMeasure 1)
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let T (z : D → ℝ) := ∑ j, w j*z j
  let n (z : D → ℝ) := w i*z i
  let F (z : D → ℝ) (t : ℝ) := n z * exp (-(t*T z))
  have bounds {z : D → ℝ} (hz : ∀ j, 0 ≤ z j) : 0 ≤ n z ∧ n z ≤ T z :=
    ⟨mul_nonneg (hw i) (hz i), Finset.single_le_sum (fun j _ ↦ mul_nonneg (hw j) (hz j))
      (Finset.mem_univ i)⟩
  have slice {z : D → ℝ} (hz : ∀ j, 0 ≤ z j) :
      Integrable (F z) ν ∧ (∫ t, F z t ∂ν) = n z/T z := by
    obtain ⟨hn,hle⟩ := bounds hz
    by_cases h : T z = 0
    · have h0 : n z = 0 := le_antisymm (hle.trans_eq h) hn
      simp [F,h0]
    · have hp := lt_of_le_of_ne (hn.trans hle) (Ne.symm h)
      refine ⟨?_, ?_⟩
      · simpa [F, mul_comm] using (exp_neg_integrableOn_Ioi 0 hp).const_mul (n z)
      · change (∫ t in Ioi (0:ℝ), n z * exp (-(t*T z))) = _
        simp_rw [show ∀ t, -(t*T z) = (-T z)*t by intro t; ring]
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hp)]
        simp [div_eq_mul_inv]
  have hs : Integrable (Function.uncurry F) (μ.prod ν) := by
    apply (integrable_prod_iff (by dsimp [F,n,T,Function.uncurry]; fun_prop)).mpr
    refine ⟨pi_positive.mono fun z hz ↦ (slice hz).1, ?_⟩
    apply (integrable_const (μ := μ) (1 : ℝ)).mono'
    · exact (show AEStronglyMeasurable (fun p : (D → ℝ) × ℝ ↦ ‖F p.1 p.2‖) (μ.prod ν) by
        dsimp [F,n,T]; fun_prop).integral_prod_right'
    · filter_upwards [pi_positive (D := D)] with z hz
      obtain ⟨hn,hle⟩ := bounds hz
      have hab (t : ℝ) : ‖F z t‖ = F z t := Real.norm_of_nonneg (mul_nonneg hn (exp_pos _).le)
      change ‖∫ t, ‖F z t‖ ∂ν‖ ≤ 1
      simp only [hab,(slice hz).2,Real.norm_of_nonneg (div_nonneg hn (hn.trans hle))]
      exact div_le_one_of_le₀ hle (hn.trans hle)
  calc
    _ = ∫ z, ∫ t, F z t ∂ν ∂μ := integral_congr_ae (pi_positive.mono fun z hz ↦ (slice hz).2.symm)
    _ = ∫ t, ∫ z, F z t ∂μ ∂ν := integral_integral_swap hs
    _ = _ := setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ tilted_exp_moment w hw i t ht.le

private theorem exp_coord_pos {D : Type*} [Fintype D] :
    ∀ᵐ z ∂Measure.pi (fun _ : D ↦ expMeasure 1), ∀ j, 0 < z j := by
  let _ : NullSingletonClass (expMeasure 1) := ⟨fun x ↦
    withDensity_absolutelyContinuous (volume : Measure ℝ) (gammaPDF 1 1) (measure_singleton x)⟩
  have hp : ∀ᵐ x ∂expMeasure 1, 0 < x := by
    filter_upwards [ae_nonneg_exp, (expMeasure 1).ae_ne (0:ℝ)] with x hx hn
    exact lt_of_le_of_ne hx hn.symm
  rw [ae_all_iff]
  exact fun j ↦ (measurePreserving_eval (fun _ : D ↦ expMeasure 1) j).quasiMeasurePreserving.ae hp

private theorem exp_moments :
    (∫ x, x ∂expMeasure 1) = 1 ∧ Integrable (fun x : ℝ ↦ x^2) (expMeasure 1) ∧
      Integrable Real.log (expMeasure 1) ∧ Integrable (fun x ↦ x*log x) (expMeasure 1) := by
  refine ⟨by simpa using exp_radial_first_moment 0 le_rfl, ?_, ?_, ?_⟩
  · apply Integrable.of_integral_ne_zero
    rw [unit_exponential_integral]
    have h := integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0:ℝ)<3) one_pos
    norm_num at h
    simp [mul_comm, h]
  · apply Integrable.of_integral_ne_zero
    rw [unit_exponential_integral]
    have h := (hasDerivAt_Gamma_of_pos one_pos).unique hasDerivAt_Gamma_one
    simp only [sub_self, rpow_zero, one_mul] at h
    simp_rw [mul_comm (exp _) (log _), h]
    linarith [one_half_lt_eulerMascheroniConstant]
  · apply Integrable.of_integral_ne_zero
    rw [unit_exponential_log_moment]
    linarith [eulerMascheroniConstant_lt_two_thirds]

/-- The logarithm of a strictly positive weighted sum of independent exponential coordinates
is integrable, also after multiplication by any one of the coordinates. -/
theorem exponential_log_integrable {D : Type*} [Fintype D] (w : D → ℝ) (hw : ∀ j, 0 < w j) (i : D) :
    let μ := Measure.pi (fun _ : D ↦ expMeasure 1)
    let T (z : D → ℝ) := ∑ j, w j*z j
    Integrable (fun z ↦ log (T z)) μ ∧ Integrable (fun z ↦ z i*log (T z)) μ := by
  intro μ T
  have he (j : D) : Integrable (fun z : D → ℝ ↦ z j) μ :=
    integrable_comp_eval (μ := fun _ : D ↦ expMeasure 1) (f := fun x : ℝ ↦ x)
      (Integrable.of_integral_ne_zero (exp_moments.1.trans_ne one_ne_zero))
  have hs (j : D) : Integrable (fun z : D → ℝ ↦ z j^2) μ := integrable_comp_eval
    (μ := fun _ : D ↦ expMeasure 1) (f := fun x : ℝ ↦ x^2) exp_moments.2.1
  have hl : Integrable (fun z : D → ℝ ↦ log (z i)) μ := integrable_comp_eval
    (μ := fun _ : D ↦ expMeasure 1) (f := Real.log) exp_moments.2.2.1
  have hzl : Integrable (fun z : D → ℝ ↦ z i*log (z i)) μ := integrable_comp_eval
    (μ := fun _ : D ↦ expMeasure 1) (f := fun x : ℝ ↦ x*log x) exp_moments.2.2.2
  have hT : Integrable T μ := integrable_finsetSum _ (fun j _ ↦ (he j).const_mul (w j))
  have hprod (j : D) : Integrable (fun z : D → ℝ ↦ z i*z j) μ := by
    apply ((hs i).add (hs j)).mono' (by fun_prop)
    filter_upwards [pi_positive (D := D)] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (hz _) (hz _))]
    dsimp
    nlinarith [sq_nonneg (z i-z j),sq_nonneg (z i),sq_nonneg (z j)]
  have hiT : Integrable (fun z ↦ z i*T z) μ := by
    have hh : Integrable (fun z : D → ℝ ↦ ∑ j, w j*(z i*z j)) μ :=
      integrable_finsetSum _ (fun j _ ↦ (hprod j).const_mul (w j))
    apply hh.congr <| .of_forall fun z ↦ ?_
    simp only [T,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ mul_left_comm _ _ _)
  have bd {z : D → ℝ} (hz : ∀ j, 0 < z j) :
      |log (T z)| ≤ |log (w i)| + |log (z i)| + T z := by
    have hlow : w i*z i ≤ T z :=
      Finset.single_le_sum (fun j _ ↦ mul_nonneg (hw j).le (hz j).le) (Finset.mem_univ i)
    have hpos := (mul_pos (hw i) (hz i)).trans_le hlow
    have hb := Real.log_le_log (mul_pos (hw i) (hz i)) hlow
    rw [log_mul (hw i).ne' (hz i).ne'] at hb
    exact abs_le.mpr ⟨by linarith [neg_abs_le (log (w i)),neg_abs_le (log (z i))],
      by linarith [log_le_sub_one_of_pos hpos,abs_nonneg (log (w i)),abs_nonneg (log (z i))]⟩
  constructor
  · apply (((integrable_const (μ := μ) |log (w i)|).add hl.abs).add hT).mono'
      (by apply Measurable.aestronglyMeasurable; dsimp [T]; fun_prop)
    filter_upwards [exp_coord_pos (D := D)] with z hz
    exact bd hz
  · apply ((((he i).mul_const |log (w i)|).add hzl.abs).add hiT).mono'
      (by apply Measurable.aestronglyMeasurable; dsimp [T]; fun_prop)
    filter_upwards [exp_coord_pos (D := D)] with z hz
    have h := mul_le_mul_of_nonneg_left (bd hz) (hz i).le
    simpa only [Real.norm_eq_abs, abs_mul, Pi.add_apply, abs_of_pos (hz i), mul_add] using h

private def centeredLog (a s x : ℝ) :=
  (x-1)*log (s+a*x) - a*x/(s+a*x)

private theorem exponential_stein_slice {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (hi : Integrable (centeredLog a s) (expMeasure 1)) :
    (∫ x, centeredLog a s x ∂expMeasure 1) = 0 := by
  let f (x : ℝ) := -(x*exp (-x)*log (s+a*x))
  have hd (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) :
      HasDerivAt f (exp (-x)*centeredLog a s x) x := by
    have hpos := add_pos_of_nonneg_of_pos hs (mul_pos ha hx)
    have ht := (hasDerivAt_const x s).add ((hasDerivAt_id x).const_mul a)
    convert (((hasDerivAt_id x).mul (hasDerivAt_id x).neg.exp).mul (ht.log hpos.ne')).neg using 1
    · rfl
    · change exp (-x)*((x-1)*log (s+a*x)-a*x/(s+a*x)) =
        -((1*exp (-x)+x*(exp (-x)*(-1)))*log (s+a*x)+x*exp (-x)*((0+a*1)/(s+a*x)))
      field_simp [hpos.ne']
      ring
  have hzero : ContinuousWithinAt f (Ici 0) 0 := by
    rcases hs.eq_or_lt with rfl | h
    · have heq : f = fun x ↦ -exp (-x)*(x * log a + x * log x) := by
        funext x
        by_cases hx : x = 0
        · simp [f,hx]
        · rw [show f x = -(x*exp (-x)*log (a*x)) by simp [f], log_mul ha.ne' hx]
          ring
      rw [heq]
      exact ((continuous_exp.comp continuous_neg).neg.mul
        ((continuous_id.mul_const _).add continuous_mul_log)).continuousWithinAt
    · apply ContinuousAt.continuousWithinAt
      dsimp [f]
      fun_prop (disch := simp [h.ne'])
  have top : Tendsto f atTop (𝓝 0) := by
    suffices h : Tendsto (fun x ↦ x*exp (-x)*log (s+a*x)) atTop (𝓝 0) by
      simpa [f] using h.neg
    have hp : Tendsto (fun x : ℝ ↦ s*(x^1*exp (-x)) + a*(x^2*exp (-x))) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul s).add
        ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul a)
    refine squeeze_zero' ?_ ?_ hp
    · filter_upwards [eventually_ge_atTop (max 0 a⁻¹)] with x hx
      have hx0 := (le_max_left 0 a⁻¹).trans hx
      have hx1 := (le_max_right 0 a⁻¹).trans hx
      have hx2 := mul_le_mul_of_nonneg_left hx1 ha.le
      rw [mul_inv_cancel₀ ha.ne'] at hx2
      exact mul_nonneg (mul_nonneg hx0 (exp_pos _).le) (log_nonneg (by linarith))
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      have hpos := add_pos_of_nonneg_of_pos hs (mul_pos ha hx)
      have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hpos)
        (mul_nonneg hx.le (exp_pos (-x)).le)
      nlinarith only [h,mul_nonneg hx.le (exp_pos (-x)).le]
  have hint : IntegrableOn (fun x ↦ exp (-x)*centeredLog a s x) (Ioi 0) := by
    unfold expMeasure gammaMeasure at hi
    have h := (integrable_withDensity_iff
      (f := gammaPDF 1 1) (by exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 1))
      (.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) ).mp hi
    apply h.integrableOn.congr_fun _ measurableSet_Ioi
    intro x hx
    simp [gammaPDF_of_nonneg hx.le, mul_comm, (exp_pos _).le]
  rw [unit_exponential_integral, integral_Ioi_of_hasDerivAt_of_tendsto hzero hd hint top]
  simp [f]

/-- The exponential integration-by-parts identity for the logarithmic gradient moment. -/
theorem exponential_log_moment {D : Type*} [Fintype D] [DecidableEq D]
    (w : D → ℝ) (hw : ∀ j, 0 < w j) (i : D) :
    let μ := Measure.pi (fun _ : D ↦ expMeasure 1)
    let T (z : D → ℝ) := ∑ j, w j*z j
    (∫ z, (1+log (T z))*z i ∂μ) =
      1 + (∫ z, log (T z) ∂μ) + ∫ z, w i*z i/T z ∂μ := by
  intro μ T
  let J := Finset.univ.erase i
  let S (z : D → ℝ) := ∑ j ∈ J, w j*z j
  let pair (z : D → ℝ) := (S z,z i)
  let g (p : ℝ × ℝ) := centeredLog (w i) p.1 p.2
  have hsplit (z) : S z + w i*z i = T z := Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hpair : Measurable pair := hS.prodMk (measurable_pi_apply i)
  have hg : Measurable g := by dsimp [g,centeredLog]; fun_prop
  have hind : IndepFun S (fun z : D → ℝ ↦ z i) μ := by
    let b (j : D) (x : ℝ) := if j = i then x else w j*x
    have hh := iIndepFun_pi (μ := fun _ : D ↦ expMeasure 1) (X := b)
      (fun j ↦ by by_cases h : j = i <;> simp [b,h] <;> fun_prop)
    have h := hh.indepFun_finsetSum_of_notMem
      (fun j ↦ by by_cases hj : j = i <;> simp [b,hj] <;> fun_prop)
      (Finset.notMem_erase i Finset.univ)
    have he : (∑ j ∈ J, fun z : D → ℝ ↦ b j (z j)) = S := by
      funext z
      simp only [Finset.sum_apply, S]
      exact Finset.sum_congr rfl (fun j hj ↦ ite_eq_right (Finset.mem_erase.mp hj).1)
    change IndepFun (∑ j ∈ J, fun z : D → ℝ ↦ b j (z j)) (fun z ↦ b i (z i)) μ at h
    rw [he] at h
    simpa [b] using h
  have hmap : μ.map pair = (μ.map S).prod (expMeasure 1) :=
    (hind.map_prod_eq_prod_map_map hS.aemeasurable (measurable_pi_apply i).aemeasurable).trans
      (congrArg (Measure.prod (μ.map S)) (measurePreserving_eval (fun _ : D ↦ expMeasure 1) i).map_eq)
  obtain ⟨hl,hxl⟩ : Integrable (fun z ↦ log (T z)) μ ∧
      Integrable (fun z ↦ z i * log (T z)) μ := exponential_log_integrable w hw i
  have hratio : Integrable (fun z ↦ w i*z i/T z) μ := by
    apply (integrable_const (μ := μ) (1:ℝ)).mono' (by
      apply Measurable.aestronglyMeasurable
      dsimp [T]
      fun_prop)
    filter_upwards [pi_positive (D := D)] with z hz
    have hn := mul_nonneg (hw i).le (hz i)
    have hle : w i*z i ≤ T z := Finset.single_le_sum (fun j _ ↦ mul_nonneg (hw j).le (hz j))
      (Finset.mem_univ i)
    rw [Real.norm_of_nonneg (div_nonneg hn (hn.trans hle))]
    exact div_le_one_of_le₀ hle (hn.trans hle)
  have he (z) : g (pair z) = (z i*log (T z) - log (T z)) - w i*z i/T z := by
    dsimp [g,pair,centeredLog]
    rw [hsplit]
    ring
  have hi : Integrable g ((μ.map S).prod (expMeasure 1)) := by
    rw [← hmap,integrable_map_measure hg.aestronglyMeasurable hpair.aemeasurable]
    simp only [Function.comp_def, he]
    exact (hxl.sub hl).sub hratio
  have hnon : ∀ᵐ s ∂μ.map S, 0 ≤ s := by
    rw [ae_map_iff hS.aemeasurable (measurableSet_Ici (a := (0:ℝ)))]
    exact pi_positive.mono fun z hz ↦ Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw j).le (hz j)
  have hzero : (∫ z, g (pair z) ∂μ) = 0 := by
    rw [← integral_map hpair.aemeasurable hg.aestronglyMeasurable, hmap, integral_prod _ hi]
    apply integral_eq_zero_of_ae
    filter_upwards [hnon,hi.prod_right_ae] with s hs hint
    exact exponential_stein_slice (hw i) hs hint
  simp_rw [he] at hzero
  have hsub : Integrable (fun z ↦ z i*log (T z) - log (T z)) μ := hxl.sub hl
  rw [integral_sub hsub hratio,integral_sub hxl hl] at hzero
  have hx : Integrable (fun z : D → ℝ ↦ z i) μ :=
    integrable_comp_eval (μ := fun _ : D ↦ expMeasure 1) (f := fun x : ℝ ↦ x)
      (Integrable.of_integral_ne_zero (exp_moments.1.trans_ne one_ne_zero))
  have hmean : (∫ z, z i ∂μ) = 1 := by
    have h := integral_map (μ := μ) (measurable_pi_apply (X := fun _ : D ↦ ℝ) i).aemeasurable
      (by fun_prop : AEStronglyMeasurable id (μ.map (fun z ↦ z i)))
    rw [(measurePreserving_eval (fun _ : D ↦ expMeasure 1) i).map_eq] at h
    exact h.symm.trans exp_moments.1
  have heq (z : D → ℝ) : (1+log (T z))*z i = z i + z i*log (T z) := by ring
  simp_rw [heq]
  rw [integral_add hx hxl,hmean]
  linarith

end SubentropyCertificates.ConditionalContinuity
