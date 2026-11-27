module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Integration of the variable derivative bound along the unit interval. -/
@[expose] public section
noncomputable section

open Set MeasureTheory

namespace SubentropyCertificates.ConditionalContinuity

/-- A continuous majorant for the absolute derivative controls the endpoint difference. -/
theorem abs_sub_le_integral_of_deriv_bound (f v k : ℝ → ℝ) (d : ℝ)
    (hk : ContinuousOn k (Icc 0 1)) (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (v t) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |v t| ≤ k t * d) :
    |f 1 - f 0| ≤ d * ∫ t in (0 : ℝ)..1, k t := by
  have hc : ContinuousOn f (Icc 0 1) := fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun t ↦ k t * d) (Icc 0 1) :=
    (hk.mul continuousOn_const).integrableOn_Icc
  have hpos := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le zero_le_one hc
    (fun t ht ↦ (hf t (Ioo_subset_Icc_self ht)).hasDerivWithinAt) hi
    (fun t ht ↦ (le_abs_self _).trans (hb t (Ioo_subset_Icc_self ht)))
  have hneg := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le zero_le_one hc.neg
    (fun t ht ↦ (hf t (Ioo_subset_Icc_self ht)).neg.hasDerivWithinAt) hi
    (fun t ht ↦ (neg_le_abs _).trans (hb t (Ioo_subset_Icc_self ht)))
  rw [intervalIntegral.integral_mul_const, mul_comm _ d] at hpos hneg
  exact abs_le.mpr ⟨by simpa [neg_sub] using neg_le_neg hneg, hpos⟩

/-- If the path coefficient is at most one, the weighted length is at most the distance. -/
theorem weighted_path_integral_le (k : ℝ → ℝ) {d : ℝ} (hd : 0 ≤ d)
    (hk : ContinuousOn k (Icc 0 1)) (h1 : ∀ t ∈ Icc (0 : ℝ) 1, k t ≤ 1) :
    d * (∫ t in (0 : ℝ)..1, k t) ≤ d := by
  have hi : IntervalIntegrable k volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hk
  have h := intervalIntegral.integral_mono_on zero_le_one hi (intervalIntegrable_const) h1
  simpa using mul_le_mul_of_nonneg_left h hd

end SubentropyCertificates.ConditionalContinuity
