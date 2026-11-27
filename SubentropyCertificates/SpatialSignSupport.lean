module

public import SubentropyCertificates.GaussianSpatialSign
import all SubentropyCertificates.ExponentialSignMoments

/-! The spatial sign covariance is positive and has the same support as its input. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.DeterminantComparison
open SubentropyCertificates.ClassicalSSA

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The spatial sign integral of a positive matrix is positive semidefinite. -/
theorem spatialSign_posSemidef {M : Matrix D D ℂ} (hM : M.PosSemidef) :
    (spatialSign M).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold signKernel
  rw [reciprocalDet_spectral hM.isHermitian]
  exact smul_nonneg (kernel_pos ht.le hM.eigenvalues_nonneg).le (signResolvent_bounds hM ht).1

private def signWeight (w : D → ℝ) (i : D) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (w i / (1 + t * w i)) * ∏ j, (1 + t * w j)⁻¹

private theorem signWeight_zero_iff (w : D → ℝ) (hw : ∀ j, 0 ≤ w j) (i : D) :
    signWeight w i = 0 ↔ w i = 0 := by
  by_cases hi : w i = 0
  · simp [signWeight, hi]
  let μ := Measure.pi (fun _ : D ↦ expMeasure 1)
  let f (z : D → ℝ) := w i * z i / (∑ j, w j * z j)
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hbounds : ∀ᵐ z ∂μ, 0 < f z ∧ f z ≤ 1 := by
    filter_upwards [exp_coord_pos (D := D)] with z hz
    have hp := mul_pos (lt_of_le_of_ne (hw i) (Ne.symm hi)) (hz i)
    have hs := Finset.single_le_sum (s := Finset.univ) (f := fun j ↦ w j * z j)
      (fun j _ ↦ mul_nonneg (hw j) (hz j).le) (Finset.mem_univ i)
    exact ⟨div_pos hp (hp.trans_le hs), div_le_one_of_le₀ hs (hp.trans_le hs).le⟩
  have hf : Integrable f μ := (integrable_const (μ := μ) (1 : ℝ)).mono'
    (by apply Measurable.aestronglyMeasurable; dsimp [f]; fun_prop) (hbounds.mono fun z hz ↦ by
      simpa only [Real.norm_of_nonneg hz.1.le] using hz.2)
  constructor
  · intro he
    change (∫ t in Ioi (0 : ℝ), _) = 0 at he
    rw [← exponential_sign_integral w hw i] at he
    have hn := (integral_eq_zero_iff_of_nonneg_ae (hbounds.mono fun _ hz ↦ hz.1.le) hf).mp he
    obtain ⟨z, hz, hzero⟩ := (hbounds.and hn).exists
    exact False.elim (hz.1.ne' hzero)
  · exact False.elim ∘ hi

private theorem range_spectral_mono (U : unitary (Matrix D D ℂ)) (v w : D → ℝ)
    (h : ∀ i, w i = 0 → v i = 0) :
    let C := Unitary.conjStarAlgAut ℂ _ U
    LinearMap.range (C (diagonal fun i ↦ (v i : ℂ))).mulVecLin ≤
      LinearMap.range (C (diagonal fun i ↦ (w i : ℂ))).mulVecLin := by
  let C := Unitary.conjStarAlgAut ℂ _ U
  let d (a : D → ℝ) := diagonal fun i ↦ (a i : ℂ)
  have he : C (d v) = C (d w) * C (d (fun i ↦ v i / w i)) := by
    rw [← map_mul, show d w * d (fun i ↦ v i / w i) =
      diagonal (fun i ↦ (w i : ℂ) * ((v i / w i : ℝ) : ℂ)) from diagonal_mul_diagonal _ _]
    apply congrArg C
    apply congrArg diagonal
    funext i
    rw [← Complex.ofReal_mul]
    by_cases hz : w i = 0
    · simp [hz, h i hz]
    · field_simp
  change LinearMap.range (C (d v)).mulVecLin ≤ _
  rw [he, mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- The range of K(M), equivalently its support space, is exactly the range of M, including
when M is singular. In their common eigenbasis the two diagonal weights vanish together. -/
theorem spatialSign_range {M : Matrix D D ℂ} (hM : M.PosSemidef) :
    LinearMap.range (spatialSign M).mulVecLin = LinearMap.range M.mulVecLin := by
  let w := hM.isHermitian.eigenvalues
  let U := hM.isHermitian.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℂ _ U
  have hk : spatialSign M = C (diagonal fun i ↦ (signWeight w i : ℂ)) := spatialSign_spectral hM
  have hm : M = C (diagonal fun i ↦ (w i : ℂ)) := hM.isHermitian.spectral_theorem
  rw [hk, hm]
  exact le_antisymm (range_spectral_mono U (signWeight w) w
    (fun i ↦ (signWeight_zero_iff w hM.eigenvalues_nonneg i).2))
    (range_spectral_mono U w (signWeight w) (fun i ↦ (signWeight_zero_iff w hM.eigenvalues_nonneg i).1))

/-- The spatial sign covariance preserves rank. -/
theorem spatialSign_rank {M : Matrix D D ℂ} (hM : M.PosSemidef) : (spatialSign M).rank = M.rank := by
  exact congrArg (fun S : Submodule ℂ (D → ℂ) ↦ Module.finrank ℂ S) (spatialSign_range hM)

end SubentropyCertificates.ConditionalContinuity

