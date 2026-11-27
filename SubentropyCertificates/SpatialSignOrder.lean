module

public import SubentropyCertificates.BlockDeterminant
public import SubentropyCertificates.MatrixResolvent
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute convergence and the operator order in the block gradient of conditional
subentropy. We use the determinant integral for the spatial sign covariance matrix. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.DeterminantComparison
open SubentropyCertificates.ClassicalSSA

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- Integrand for the marginal spatial sign matrix. -/
def signKernel (M : Matrix D D ℂ) (t : ℝ) := reciprocalDet t M • signResolvent M t

/-- Integrand for a diagonal block of the joint spatial sign matrix. -/
def blockSignKernel (A : X → Matrix D D ℂ) (x : X) (t : ℝ) :=
  reciprocalDet t (blockDiagonal A) • signResolvent (A x) t

/-- The determinant integral defining K(M) in Section 4. -/
def spatialSign (M : Matrix D D ℂ) := ∫ t in Ioi (0 : ℝ), signKernel M t

/-- The integral defining K_x(R), with the determinant of the full direct sum R. -/
def blockSpatialSign (A : X → Matrix D D ℂ) (x : X) :=
  ∫ t in Ioi (0 : ℝ), blockSignKernel A x t

private theorem weight_pos {M : Matrix D D ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    0 < reciprocalDet t M := by
  rw [reciprocalDet_spectral hM.isHermitian]
  exact kernel_pos ht hM.eigenvalues_nonneg

private theorem weight_continuousAt {M : Matrix D D ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun u ↦ reciprocalDet u M) t := by
  have hp := weight_pos hM ht
  have hd : (1 + t • M).det.re ≠ 0 := by
    intro h
    simp [reciprocalDet, h] at hp
  have hc : ContinuousAt (fun u : ℝ ↦ (1 + u • M).det.re) t := by fun_prop
  exact hc.inv₀ hd

omit [DecidableEq X] [Fintype D] [DecidableEq D] in
private theorem sum_psd (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosSemidef) :
    (∑ x, A x).PosSemidef := (Finset.sum_nonneg fun i _ ↦ (hA i).nonneg).posSemidef

/-- Both factors of the block integrand are dominated by their marginal counterparts. -/
theorem blockSignKernel_order (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosSemidef)
    (x : X) {t : ℝ} (ht : 0 < t) :
    0 ≤ blockSignKernel A x t ∧ blockSignKernel A x t ≤ signKernel (∑ y, A y) t := by
  have hw : 0 ≤ reciprocalDet t (blockDiagonal A) := by
    rw [reciprocalDet_blockDiagonal A hA]
    exact Finset.prod_nonneg fun i _ ↦ (weight_pos (hA i) ht.le).le
  have hx := (signResolvent_bounds (hA x) ht).1
  have hle : A x ≤ ∑ i, A i :=
    Finset.single_le_sum (fun i _ ↦ (hA i).nonneg) (Finset.mem_univ x)
  refine ⟨smul_nonneg hw hx, ?_⟩
  exact (smul_le_smul_of_nonneg_right (reciprocalDet_blocks_le_sum A hA ht.le) hx).trans
    (smul_le_smul_of_nonneg_left (signResolvent_mono (hA x) (sum_psd A hA) hle ht.le)
      (weight_pos (sum_psd A hA) ht.le).le)

/-- The marginal integral converges absolutely, including when the matrix is singular. -/
theorem signKernel_integrable {M : Matrix D D ℂ} (hM : M.PosSemidef) :
    IntegrableOn (signKernel M) (Ioi 0) := by
  by_cases hz : M = 0
  · subst M
    have zero : signKernel (0 : Matrix D D ℂ) = 0 := by
      funext t
      simp [signKernel, signResolvent]
    rw [zero]
    exact integrable_zero _ _ _
  let mass := ∑ i, hM.isHermitian.eigenvalues i
  have hm : 0 < mass := by
    apply lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ hM.eigenvalues_nonneg i)
    intro h
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hM.eigenvalues_nonneg i)).mp h.symm
    exact hz (hM.isHermitian.eigenvalues_eq_zero_iff.mp (funext fun i ↦ he i (Finset.mem_univ i)))
  have hc : ContinuousOn (signKernel M) (Ici 0) := fun t ht ↦
    ((weight_continuousAt hM ht).smul (signResolvent_continuousAt hM ht)).continuousWithinAt
  have htail : IntegrableOn (signKernel M) (Ioi 1) := by
    have hin := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul
      (mass⁻¹ * ‖(1 : Matrix D D ℂ)‖)
    apply hin.mono' ((hc.mono (fun t ht ↦ (zero_lt_one.trans ht).le)).aestronglyMeasurable
      measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hw : reciprocalDet t M ≤ (mass * t)⁻¹ := by
      rw [reciprocalDet_spectral hM.isHermitian]
      exact (refinement ht0.le Finset.univ _ hM.eigenvalues_nonneg).trans
        (inv_anti₀ (mul_pos hm ht0) (by dsimp [mass]; linarith))
    have hres := signResolvent_bounds hM ht0
    have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hres.2 hres.1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht0.le)] at hn
    change ‖reciprocalDet t M • signResolvent M t‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (weight_pos hM ht0.le).le]
    calc
      _ ≤ (mass * t)⁻¹ * (t⁻¹ * ‖(1 : Matrix D D ℂ)‖) :=
        mul_le_mul hw hn (norm_nonneg _) (inv_nonneg.mpr (mul_nonneg hm.le ht0.le))
      _ = _ := by rw [Real.rpow_neg ht0.le, Real.rpow_two, mul_inv, sq, mul_inv]; ring
  have hcompact : IntegrableOn (signKernel M) (Icc 0 1) :=
    (hc.mono Icc_subset_Ici_self).integrableOn_Icc
  exact ((hcompact.union htail).mono_set (fun t ht ↦ by
    by_cases h : t ≤ 1
    · exact Or.inl ⟨ht.le, h⟩
    · exact Or.inr (lt_of_not_ge h)))

/-- The block integral converges absolutely. The proof also allows a zero block. -/
theorem blockSignKernel_integrable (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosSemidef)
    (x : X) : IntegrableOn (blockSignKernel A x) (Ioi 0) := by
  have hc : ContinuousOn (blockSignKernel A x) (Ioi 0) := by
    intro t ht
    unfold blockSignKernel
    simp_rw [reciprocalDet_blockDiagonal A hA]
    have hw : ContinuousAt (fun u ↦ ∏ i, reciprocalDet u (A i)) t :=
      tendsto_finsetProd _ (fun i _ ↦ weight_continuousAt (hA i) ht.le)
    exact (hw.smul
      (signResolvent_continuousAt (hA x) ht.le)).continuousWithinAt
  apply Integrable.mono (signKernel_integrable (sum_psd A hA))
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  obtain ⟨hp, hl⟩ := blockSignKernel_order A hA x ht
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hl hp

/-- In Loewner order the gradient correction B_x = K(A) - K_x(R) lies between zero
and the marginal spatial sign matrix, which is bounded by its operator norm times I. -/
theorem spatialSign_block_gradient_order (A : X → Matrix D D ℂ) (hA : ∀ x, (A x).PosSemidef)
    (x : X) :
    let K := spatialSign (∑ y, A y)
    let B := K - blockSpatialSign A x
    0 ≤ B ∧ B ≤ K ∧ K ≤ ‖K‖ • 1 := by
  have hp : 0 ≤ blockSpatialSign A x := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (blockSignKernel_order A hA x ht).1
  have hl : blockSpatialSign A x ≤ spatialSign (∑ y, A y) := by
    apply integral_mono_ae (blockSignKernel_integrable A hA x)
      (signKernel_integrable (sum_psd A hA))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (blockSignKernel_order A hA x ht).2
  refine ⟨sub_nonneg.mpr hl, sub_le_self _ hp, ?_⟩
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (hp.trans hl).isSelfAdjoint.le_algebraMap_norm_self

end SubentropyCertificates.ConditionalContinuity
