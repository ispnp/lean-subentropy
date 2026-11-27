module

public import SubentropyCertificates.NormalizedGaussian
public import SubentropyCertificates.ExponentialEntropy
public import SubentropyCertificates.GaussianRadius
import all D5.S3.Quantum.Subentropy.GaussianMatrix

/-! The circular Gaussian convention used in Lemma 3: each squared
coordinate magnitude has the unit exponential law and expectation one. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace SubentropyCertificates.Representations
open D5.S3.Quantum.Subentropy.GaussianMatrix
open D5.S3.Quantum.Subentropy.GaussianQuadratic

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem circular_coordinate_integral (i : D) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ g, f (Complex.normSq (g i)) ∂circularGaussian D) = ∫ t, f t ∂expMeasure 1 := by
  let g := complexGaussianCoordinates (ι := D)
  have hm : Measurable g := measurable_coordinates
  have hn : Measurable (normalizeGaussian (D := D)) := by unfold normalizeGaussian; fun_prop
  have he (z : (D × Fin 2) → ℝ) :
      Complex.normSq (normalizeGaussian (g z) i) = ((z (i,0))^2 + (z (i,1))^2) / 2 := by
    change Complex.normSq (((((√2)⁻¹ : ℝ) : ℂ)) * (g z i)) = _
    rw [Complex.normSq_mul, Complex.normSq_ofReal, ← sq, inv_pow, sq_sqrt (by norm_num),
      complex_coordinate_transport.2 z i]
    ring
  have htest : Measurable (fun z : V D => f (Complex.normSq (z i))) :=
    hf.comp (Complex.continuous_normSq.measurable.comp (by fun_prop))
  rw [circularGaussian, integral_map hn.aemeasurable htest.aestronglyMeasurable,
    ← complex_coordinate_transport.1]
  have ht : Measurable (fun z : V D => f (Complex.normSq (normalizeGaussian z i))) :=
    htest.comp hn
  rw [integral_map hm.aemeasurable ht.aestronglyMeasurable]
  change (∫ z : (D × Fin 2) → ℝ, f (Complex.normSq (normalizeGaussian (g z) i))
    ∂Measure.pi (fun _ => gaussianReal 0 1)) = _
  simp_rw [he]
  exact (gaussian_coordinate_integral i f hf).trans (unit_exponential_integral f).symm

theorem circular_coordinate_mean (i : D) :
    (∫ g, Complex.normSq (g i) ∂circularGaussian D) = 1 := by
  refine (circular_coordinate_integral i id measurable_id).trans ((unit_exponential_integral id).trans ?_)
  have h := (Gamma_eq_integral (s := 2) (by norm_num)).symm
  norm_num at h
  exact h

end SubentropyCertificates.Representations
