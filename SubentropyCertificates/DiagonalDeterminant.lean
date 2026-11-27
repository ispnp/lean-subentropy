module

public import SubentropyCertificates.TableMerging
public import D5.S3.Quantum.Subentropy.DensityKernel
import all D5.S3.Quantum.Subentropy.DensityKernel
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-! Hadamard's determinant comparison for I+tA with A positive
semidefinite. Jensen's inequality for log is applied to each row of the
squared moduli of an eigenvector unitary. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.DeterminantComparison
open SubentropyCertificates.ClassicalSSA
open D5.S3.Quantum.Subentropy.DensityKernel
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Reciprocal determinant at the manuscript parameter t. For a
positive semidefinite matrix and nonnegative t the determinant is real
and strictly positive, including when the matrix is singular. -/
def reciprocalDet (t : ℝ) (A : Matrix D D ℂ) : ℝ := ((1 + t • A).det.re)⁻¹

theorem reciprocalDet_spectral {A : Matrix D D ℂ} (hA : A.IsHermitian) (t : ℝ) :
    reciprocalDet t A = kernel t hA.eigenvalues := by
  unfold reciprocalDet kernel factor
  rw [det_spectral hA, ← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_inv_distrib]
  simp_rw [mul_comm t]

/-- The reciprocal determinant dominates the product of reciprocal
diagonal factors in every orthonormal coordinate system. -/
theorem diagonal_kernel_le_reciprocalDet {A : Matrix D D ℂ} (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    kernel t (fun i => (A i i).re) ≤ reciprocalDet t A := by
  let H := hA.isHermitian
  let U : Matrix D D ℂ := H.eigenvectorUnitary
  let w := fun i j => Complex.normSq (U i j)
  have hr (i : D) : ∑ j, w i j = 1 := by
    have hu : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self H.eigenvectorUnitary
    have hi := congrArg (fun M : Matrix D D ℂ => (M i i).re) hu
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, w,
      Complex.normSq_apply] using hi
  have hc (j : D) : ∑ i, w i j = 1 := by
    have hu : U.conjTranspose * U = 1 := Unitary.coe_star_mul_self H.eigenvectorUnitary
    have hj := congrArg (fun M : Matrix D D ℂ => (M j j).re) hu
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, w,
      Complex.normSq_apply] using hj
  have hentry (i : D) : (A i i).re = ∑ j, w i j * H.eigenvalues j := by
    have hspec : A = U * diagonal (fun j => (H.eigenvalues j : ℂ)) * U.conjTranspose :=
      H.spectral_theorem
    conv_lhs => rw [hspec, Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, w]
    have hs (v : ℂ) : v * star v = (Complex.normSq v : ℂ) := Complex.mul_conj v
    rw [mul_right_comm, hs]
    simp
  let z := fun j => 1 + H.eigenvalues j * t
  let d := fun i => 1 + (A i i).re * t
  have hz (j) : 0 < z j := by dsimp [z,H]; have := hA.eigenvalues_nonneg j; positivity
  have hd (i) : 0 < d i := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (RCLike.nonneg_iff.mp (hA.diag_nonneg (i := i))).1 ht)
  have hmean (i) : (∑ j, w i j * z j) = d i := by
    simp only [z, d, mul_add, mul_one, ← mul_assoc, Finset.sum_add_distrib,
      ← Finset.sum_mul, hr, ← hentry]
  have hjensen (i) : ∑ j, w i j * Real.log (z j) ≤ Real.log (d i) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := Finset.univ) (w := w i) (p := z) (fun j _ => Complex.normSq_nonneg _)
      (hr i) (fun j _ => hz j)
    simpa only [smul_eq_mul, hmean] using h
  have hlog : (∑ j, Real.log (z j)) ≤ ∑ i, Real.log (d i) := by
    calc _ = ∑ i, ∑ j, w i j * Real.log (z j) := by
            rw [Finset.sum_comm]; simp only [← Finset.sum_mul, hc, one_mul]
         _ ≤ _ := Finset.sum_le_sum (fun i _ => hjensen i)
  have hprod : ∏ j, z j ≤ ∏ i, d i := by
    apply (Real.log_le_log_iff (Finset.prod_pos fun j _ => hz j)
      (Finset.prod_pos fun i _ => hd i)).mp
    simpa only [Real.log_prod (fun j _ => (hz j).ne'), Real.log_prod (fun i _ => (hd i).ne')]
      using hlog
  rw [reciprocalDet_spectral H]
  unfold kernel factor
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  exact inv_anti₀ (Finset.prod_pos fun j _ => hz j) hprod

end SubentropyCertificates.DeterminantComparison
