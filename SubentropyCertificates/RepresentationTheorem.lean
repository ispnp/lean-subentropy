module

public import SubentropyCertificates.GaussianCoordinateLaw
public import SubentropyCertificates.DeterminantRepresentation
public import SubentropyCertificates.SpectralExtension

/-! Lemma 3, with the paper's Euler constant, circular Gaussian and
reciprocal determinant variable. No inverse of the density matrix occurs. -/
@[expose] public section
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped ComplexOrder
namespace SubentropyCertificates.Representations
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.GaussianMatrix
open D5.S3.Quantum.Subentropy.GaussianQuadratic
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
theorem gaussian_coordinate_log_moment (i : D) :
    (∫ z : (D × Fin 2) → ℝ, let t := ((z (i,0))^2 + (z (i,1))^2) / 2
      t * log t ∂Measure.pi (fun _ => gaussianReal 0 1)) = 1 - eulerMascheroniConstant :=
  (gaussian_coordinate_integral i (fun t => t * log t) (measurable_id.mul measurable_log)).trans
    exponential_log_moment_integral

theorem gaussian_representation (A : Matrix D D ℂ) (hA : A.PosSemidef) (ht : A.trace = 1) :
    Integrable (fun g => quadraticForm A g * log (quadraticForm A g)) (circularGaussian D) ∧
      matrixSubentropy A = 1 - eulerMascheroniConstant -
        ∫ g, quadraticForm A g * log (quadraticForm A g) ∂circularGaussian D := by
  have : Nonempty D := by
    by_contra! he
    have : IsEmpty D := he
    simp [Matrix.trace] at ht
  let i : D := Classical.choice ‹Nonempty D›
  obtain ⟨hi, he⟩ := matrix_subentropy_gaussian_entropy A hA ht i
  have hn : Measurable (normalizeGaussian (D := D)) := by unfold normalizeGaussian; fun_prop
  have hq : Measurable (quadraticForm A) := by unfold quadraticForm; fun_prop
  have hf : Measurable (fun t : ℝ => t * log t) := measurable_id.mul measurable_log
  constructor
  · apply (integrable_map_measure ((hf.comp hq).aestronglyMeasurable) hn.aemeasurable).mpr
    have hneg : Integrable (fun z => -Real.negMulLog (gaussianQuadratic A z))
        (stdGaussian (V D)) := hi.neg
    simpa only [Function.comp_def, quadraticForm_normalize, Real.negMulLog_eq_neg, neg_neg] using hneg
  · simp only [Real.negMulLog_eq_neg, integral_neg] at he
    rw [gaussian_coordinate_log_moment i] at he
    rw [integral_quadratic_circular A (fun t => t * log t) hf]
    linarith

/-- Both formulas in Lemma 3 for a finite density state, with absolute
integrability of the Gaussian expectation and the determinant integral. -/
theorem lemma_three (ρ : DensityState D) :
    let A := CStarMatrix.ofMatrix.symm ρ.1
    Integrable (fun g => quadraticForm A g * log (quadraticForm A g)) (circularGaussian D) ∧
    subentropy ρ = 1 - eulerMascheroniConstant -
      (∫ g, quadraticForm A g * log (quadraticForm A g) ∂circularGaussian D) ∧
    IntegrableOn (determinantIntegrand A) (Ioi 0) ∧
    subentropy ρ = ∫ t in Ioi (0 : ℝ), determinantIntegrand A t := by
  have hg := gaussian_representation _ (density_posSemidef ρ) ρ.2.2
  exact ⟨hg.1, hg.2, reciprocal_determinant_integral _ (density_posSemidef ρ) ρ.2.2⟩

end SubentropyCertificates.Representations
