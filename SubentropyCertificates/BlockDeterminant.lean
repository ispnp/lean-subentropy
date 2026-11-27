module

public import SubentropyCertificates.DiagonalDeterminant
import all D5.S3.Quantum.Subentropy.DensityKernel

/-! The determinant factors in the block order of Theorem 14. Diagonalize each
block and apply the determinant comparison to the Gram matrix of all columns. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.DeterminantComparison
open SubentropyCertificates.ClassicalSSA
open D5.S3.Quantum.Subentropy.DensityKernel (det_spectral)

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- The reciprocal determinant of the direct sum factors over the label blocks. -/
theorem reciprocalDet_blockDiagonal (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosSemidef)
    (t : ℝ) : reciprocalDet t (blockDiagonal A) = ∏ x, reciprocalDet t (A x) := by
  have hs : (1 : Matrix (D × X) (D × X) ℂ) + t • blockDiagonal A =
      blockDiagonal (1 + t • A) := by
    rw [blockDiagonal_add, blockDiagonal_one, blockDiagonal_smul]
  simp only [reciprocalDet, hs, det_blockDiagonal, Pi.add_apply, Pi.one_apply, Pi.smul_apply]
  simp_rw [det_spectral (hA _).isHermitian, ← Complex.ofReal_prod, Complex.ofReal_re]
  rw [Finset.prod_inv_distrib]

/-- The inverse determinant of the joint block matrix is at most that of the sum
of the blocks for every nonnegative parameter, including singular or zero blocks. -/
theorem reciprocalDet_blocks_le_sum (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    reciprocalDet t (blockDiagonal A) ≤ reciprocalDet t (∑ x, A x) := by
  let U (x : X) : Matrix.unitaryGroup D ℂ := (hA x).isHermitian.eigenvectorUnitary
  let d (x : X) := diagonal (fun i ↦ ((hA x).isHermitian.eigenvalues i : ℂ))
  let W (x : X) := CFC.sqrt (A x) * (U x : Matrix D D ℂ)
  have hs (x : X) : (CFC.sqrt (A x)).conjTranspose = CFC.sqrt (A x) :=
    (CFC.sqrt_nonneg (A x)).isSelfAdjoint.star_eq
  have hu (x : X) : (U x : Matrix D D ℂ) * (U x : Matrix D D ℂ).conjTranspose = 1 :=
    Unitary.coe_mul_star_self _
  have hv (x : X) : (U x : Matrix D D ℂ).conjTranspose * (U x : Matrix D D ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have row (x : X) : W x * (W x).conjTranspose = A x := by
    simp only [W, conjTranspose_mul, hs, mul_assoc, ← mul_assoc (U x : Matrix D D ℂ), hu, one_mul]
    exact CFC.sqrt_mul_sqrt_self _ (hA x).nonneg
  have col (x : X) : (W x).conjTranspose * W x = d x := by
    have spec : A x = (U x : Matrix D D ℂ) * d x * (U x : Matrix D D ℂ).conjTranspose :=
      (hA x).isHermitian.spectral_theorem
    dsimp only [W]
    rw [Matrix.conjTranspose_mul, hs, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt _),
      CFC.sqrt_mul_sqrt_self _ (hA x).nonneg, spec]
    simp only [mul_assoc, hv, mul_one, ← mul_assoc (U x : Matrix D D ℂ).conjTranspose, one_mul]
  let V : Matrix D (X × D) ℂ := fun i j ↦ W j.1 i j.2
  have hrow : V * V.conjTranspose = ∑ x, A x := by
    ext i j
    change (∑ k : X × D, W k.1 i k.2 * star (W k.1 j k.2)) = _
    rw [Fintype.sum_prod_type, Matrix.sum_apply]
    exact Finset.sum_congr rfl (fun x _ ↦ congrArg (fun M : Matrix D D ℂ ↦ M i j) (row x))
  have hdiag (j : X × D) : ((V.conjTranspose * V) j j).re = (hA j.1).isHermitian.eigenvalues j.2 :=
    by
      change (((W j.1).conjTranspose * W j.1) j.2 j.2).re = _
      rw [col]
      simp [d]
  have h := diagonal_kernel_le_reciprocalDet (Matrix.posSemidef_conjTranspose_mul_self V) ht
  have hd := Matrix.det_one_add_mul_comm (t • V) V.conjTranspose
  simp only [Matrix.smul_mul, Matrix.mul_smul, hrow] at hd
  rw [← show reciprocalDet t (∑ x, A x) = reciprocalDet t (V.conjTranspose * V) from
    congrArg (fun z : ℂ ↦ z.re⁻¹) hd] at h
  rw [reciprocalDet_blockDiagonal A hA]
  simp_rw [reciprocalDet_spectral (hA _).isHermitian]
  simpa only [kernel, Fintype.prod_prod_type, hdiag] using h

end SubentropyCertificates.ConditionalContinuity
