module

public import SubentropyCertificates.SpatialSignOrder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! On a direct sum, the marginal spatial sign integral has the joint determinant
in every block. This identifies the matrices appearing in the two gradients. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

theorem blocks_posSemidef (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosSemidef) :
    (blockDiagonal A).PosSemidef := by
  let S := fun i ↦ CFC.sqrt (A i)
  have h : (blockDiagonal S).conjTranspose * blockDiagonal S = blockDiagonal A := by
    rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    congr 1
    funext i
    have hs : (S i).conjTranspose = S i := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
    rw [hs]
    exact CFC.sqrt_mul_sqrt_self _ (hA i).nonneg
  rw [← h]
  exact posSemidef_conjTranspose_mul_self _

theorem blocks_posDef (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosDef) :
    (blockDiagonal A).PosDef := by
  apply (blocks_posSemidef A (fun i ↦ (hA i).posSemidef)).posDef_iff_isUnit.mpr
  rw [isUnit_iff_isUnit_det, det_blockDiagonal, IsUnit.prod_univ_iff]
  exact fun i ↦ (isUnit_iff_isUnit_det _).mp (hA i).isUnit

omit [Fintype D] [DecidableEq D] in
theorem sum_blocks_posDef [Nonempty X] (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosDef) :
    (∑ x, A x).PosDef := by
  let x : X := Classical.choice ‹Nonempty X›
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
  exact Matrix.PosDef.posSemidef_add
    (Finset.sum_nonneg (fun i _ ↦ (hA i).posSemidef.nonneg)).posSemidef (hA x)

private theorem direct_sum_kernel (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    signKernel (blockDiagonal A) t = blockDiagonal (fun x ↦ blockSignKernel A x t) := by
  let S (i : X) := 1 + t • A i
  have shift : 1 + t • blockDiagonal A = blockDiagonal S := by
    rw [← blockDiagonal_one, ← blockDiagonal_smul, ← blockDiagonal_add]
    rfl
  have hi : (blockDiagonal S)⁻¹ = blockDiagonal (fun x ↦ (S x)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [← blockDiagonal_mul]
    have h (x : X) : S x * (S x)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (shifted_posDef (hA x) ht).isUnit)
    simp_rw [h]
    exact blockDiagonal_one
  unfold signKernel blockSignKernel signResolvent
  rw [shift, hi, ← blockDiagonal_mul, ← blockDiagonal_smul]
  rfl

private def entryMap {I : Type*} [Fintype I] [DecidableEq I] (i j : I) :
    Matrix I I ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M ↦ M i j, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }

/-- The block of K(R) at label x is K_x(R), with the full joint determinant. -/
theorem spatialSign_blockDiagonal (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosSemidef) :
    spatialSign (blockDiagonal A) = blockDiagonal (blockSpatialSign A) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  change entryMap (i,x) (j,y) (∫ t in Ioi (0 : ℝ), signKernel (blockDiagonal A) t) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ (signKernel_integrable (blocks_posSemidef A hA))]
  by_cases he : x = y
  · subst y
    rw [blockDiagonal_apply_eq]
    change _ = entryMap i j (∫ t in Ioi (0 : ℝ), blockSignKernel A x t)
    rw [← ContinuousLinearMap.integral_comp_comm _ (blockSignKernel_integrable A hA x)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (signKernel (blockDiagonal A) t) (i,x) (j,x) = _
    rw [direct_sum_kernel A hA ht.le, blockDiagonal_apply_eq]
    rfl
  · rw [blockDiagonal_apply_ne _ _ _ he]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    change (signKernel (blockDiagonal A) t) (i,x) (j,y) = 0
    rw [direct_sum_kernel A hA ht.le, blockDiagonal_apply_ne _ _ _ he]

end SubentropyCertificates.ConditionalContinuity
