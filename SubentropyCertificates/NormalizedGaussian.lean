module

public import D5.S3.Quantum.Subentropy.GaussianMatrix

/-! The paper's circular complex Gaussian has real and imaginary parts
of variance one half. Mathlib's real standard Gaussian on complex
Euclidean space is therefore scaled by 1 / sqrt 2. -/
@[expose] public section
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Real
open scoped ComplexOrder
namespace SubentropyCertificates.Representations
open D5.S3.Quantum.Subentropy.GaussianQuadratic

variable {D : Type*} [Fintype D] [DecidableEq D]
abbrev V (D : Type*) [Fintype D] := EuclideanSpace ℂ D

def normalizeGaussian (z : V D) : V D := ((√2)⁻¹ : ℝ) • z

def circularGaussian (D : Type*) [Fintype D] : Measure (V D) :=
  (stdGaussian (V D)).map normalizeGaussian

def quadraticForm (A : Matrix D D ℂ) (g : V D) : ℝ :=
  (inner ℂ g (Matrix.toEuclideanLin A g)).re

theorem quadraticForm_normalize (A : Matrix D D ℂ) (z : V D) :
    quadraticForm A (normalizeGaussian z) = gaussianQuadratic A z := by
  let c : ℝ := (√2)⁻¹
  change (inner ℂ ((c : ℂ) • z) (Matrix.toEuclideanLin A ((c : ℂ) • z))).re =
    (inner ℂ z (Matrix.toEuclideanLin A z)).re / 2
  simp only [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hc : c * c = (2 : ℝ)⁻¹ := by
    change (√2)⁻¹ * (√2)⁻¹ = (2 : ℝ)⁻¹
    rw [← mul_inv, ← sq, sq_sqrt (by norm_num)]
  rw [← mul_assoc, hc]
  ring

theorem integral_quadratic_circular (A : Matrix D D ℂ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ z, f (quadraticForm A z) ∂circularGaussian D) =
      ∫ z, f (gaussianQuadratic A z) ∂stdGaussian (V D) := by
  have hn : Measurable (normalizeGaussian (D := D)) := by unfold normalizeGaussian; fun_prop
  have hq : Measurable (quadraticForm A) := by unfold quadraticForm; fun_prop
  have hfq : Measurable (fun z => f (quadraticForm A z)) := hf.comp hq
  rw [circularGaussian, integral_map hn.aemeasurable hfq.aestronglyMeasurable]
  simp only [quadraticForm_normalize]

end SubentropyCertificates.Representations
