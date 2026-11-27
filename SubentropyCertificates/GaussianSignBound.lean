module

public import SubentropyCertificates.GaussianGradientDefs

/-! Integrability of the normalized outer product even at a singular covariance. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem gaussianOuter_norm (g : V D) : ‖gaussianOuter g‖ = ‖g‖ ^ 2 := by
  have h : toEuclideanCLM (𝕜 := ℂ) (gaussianOuter g) = InnerProductSpace.rankOne ℂ g g := by
    ext x i
    change ((gaussianOuter g) *ᵥ (fun j ↦ x j)) i = _
    rw [gaussianOuter, vecMulVec_mulVec, InnerProductSpace.rankOne_apply,
      EuclideanSpace.inner_eq_star_dotProduct]
    change (g i) * ((star (WithLp.ofLp g)) ⬝ᵥ (WithLp.ofLp x)) = _
    rw [dotProduct_comm (star (WithLp.ofLp g)), mul_comm]
    rfl
  rw [← Matrix.l2_opNorm_toEuclideanCLM, h, InnerProductSpace.norm_rankOne, sq]

theorem quadraticForm_sqrt_norm {M : Matrix D D ℂ} (hM : M.PosSemidef) (g : V D) :
    quadraticForm M g = ‖Matrix.toEuclideanLin (CFC.sqrt M) g‖ ^ 2 := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℂ) (CFC.sqrt M)
  have hh : star L * L = Matrix.toEuclideanCLM (𝕜 := ℂ) M := by
    dsimp only [L]
    rw [← map_star, ← map_mul, (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq,
      CFC.sqrt_mul_sqrt_self _ hM.nonneg]
  have hv := congrArg (fun T : V D →L[ℂ] V D ↦ T g) hh
  rw [show Matrix.toEuclideanLin (CFC.sqrt M) g = L g from rfl,
    L.apply_norm_sq_eq_inner_adjoint_right]
  exact congrArg (fun v : V D ↦ (inner ℂ g v).re) hv.symm

/-- A normalized Gaussian outer product has operator norm at most one pointwise. -/
theorem gaussianSign_norm_le_one {M : Matrix D D ℂ} (hM : M.PosSemidef) (g : V D) :
    ‖gaussianSign M g‖ ≤ 1 := by
  rw [gaussianSign, norm_smul, gaussianOuter_norm, quadraticForm_sqrt_norm hM]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  by_cases h : ‖Matrix.toEuclideanLin (CFC.sqrt M) g‖ ^ 2 = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem gaussianSign_integrable {M : Matrix D D ℂ} (hM : M.PosSemidef) :
    Integrable (gaussianSign M) (circularGaussian D) := by
  have hn : Measurable (normalizeGaussian (D := D)) := by unfold normalizeGaussian; fun_prop
  have : IsProbabilityMeasure (circularGaussian D) := (Measure.isProbabilityMeasure_map_iff hn.aemeasurable).mpr inferInstance
  apply (integrable_const (1 : ℝ)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold gaussianSign gaussianOuter quadraticForm
    fun_prop
  · exact .of_forall (gaussianSign_norm_le_one hM)

end SubentropyCertificates.ConditionalContinuity
