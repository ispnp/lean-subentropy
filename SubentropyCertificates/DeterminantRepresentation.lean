module

public import D5.S3.Quantum.Subentropy.DensityKernel
import all D5.S3.Quantum.Subentropy.DensityKernel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The determinant integral in the variable of the arXiv manuscript. -/
@[expose] public section
noncomputable section
open Matrix MeasureTheory Set
open scoped ComplexOrder
namespace SubentropyCertificates.Representations
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel

variable {D : Type*} [Fintype D] [DecidableEq D]

def determinantIntegrand (A : Matrix D D ℂ) (t : ℝ) : ℝ :=
  (1 / (1 + t) - 1 / (1 + t • A).det.re) / t^2

/-- The determinant in the real-valued integrand is positive real, even
when the density matrix itself has a kernel. -/
theorem determinant_positive_real (A : Matrix D D ℂ) (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ∃ r : ℝ, 0 < r ∧ (1 + t • A).det = (r : ℂ) := by
  refine ⟨∏ i, (1 + t * hA.isHermitian.eigenvalues i), ?_, ?_⟩
  · exact Finset.prod_pos fun i _ => add_pos_of_pos_of_nonneg one_pos
      (mul_nonneg ht (hA.eigenvalues_nonneg i))
  · rw [det_spectral hA.isHermitian, Complex.ofReal_prod]

theorem reciprocal_determinant_integral (A : Matrix D D ℂ) (hA : A.PosSemidef) (ht : A.trace = 1) :
    IntegrableOn (determinantIntegrand A) (Ioi 0) ∧
      matrixSubentropy A = ∫ t in Ioi (0 : ℝ), determinantIntegrand A t := by
  have he (t : ℝ) (ht' : t ∈ Ioi 0) :
      (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • subentropyKernel A (t ^ (-1 : ℝ)) =
        determinantIntegrand A t := by
    rw [show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num, Real.rpow_neg ht'.le,
      Real.rpow_two, Real.rpow_neg_one]
    have hfirst : t⁻¹ / (1 + t⁻¹) = 1 / (1 + t) := by
      field_simp [ht'.ne']; ring
    simp only [subentropyKernel, inv_inv, determinantIntegrand, hfirst, abs_neg, abs_one,
      one_mul, mul_one, smul_eq_mul, div_eq_mul_inv, mul_comm]
  refine ⟨((integrableOn_Ioi_comp_rpow_iff (subentropyKernel A) (p := -1) (by norm_num)).mpr
    (integrable_subentropy_kernel hA ht)).congr_fun he measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi he, integral_comp_rpow_Ioi _ (by norm_num : (-1 : ℝ) ≠ 0)]
  rfl

end SubentropyCertificates.Representations
