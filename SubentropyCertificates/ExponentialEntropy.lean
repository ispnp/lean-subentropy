module

public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.Probability.Distributions.Exponential

/-! The reference value for a mean-one exponential variable in Lemma 3. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
namespace SubentropyCertificates.Representations

theorem exponential_log_moment_integral :
    (∫ t in Ioi (0 : ℝ), exp (-t) * (t * log t)) = 1 - eulerMascheroniConstant := by
  have hn : HasDerivAt Gamma (1 - eulerMascheroniConstant) 2 := by
    convert hasDerivAt_Gamma_nat 1 using 1 <;> norm_num [harmonic]
    ring
  have h := (hasDerivAt_Gamma_of_pos (s := 2) (by norm_num)).unique hn
  norm_num at h
  simpa only [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm] using h

theorem unit_exponential_integral (f : ℝ → ℝ) :
    (∫ t, f t ∂expMeasure 1) = ∫ t in Ioi (0 : ℝ), exp (-t) * f t := by
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : 0 ≤ t
    · simp [Set.indicator_of_mem (show t ∈ Ici 0 from ht), gammaPDF_of_nonneg ht,
        Real.exp_nonneg, smul_eq_mul]
    · simp [Set.indicator_of_notMem (show t ∉ Ici 0 from ht), gammaPDF_of_neg (lt_of_not_ge ht)]
  · exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 1)
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

theorem unit_exponential_log_moment :
    (∫ t, t * log t ∂expMeasure 1) = 1 - eulerMascheroniConstant :=
  (unit_exponential_integral _).trans exponential_log_moment_integral

end SubentropyCertificates.Representations
