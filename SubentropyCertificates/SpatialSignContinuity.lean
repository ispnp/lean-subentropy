module

public import SubentropyCertificates.GaussianSpatialSign
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! Continuity of the spatial sign matrix on the positive semidefinite cone away from zero. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter Set
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- When the limiting quadratic form is positive, the normalized outer product
varies continuously along the positive semidefinite cone. -/
private theorem gaussianSign_continuousWithinAt {M : Matrix D D ℂ} (hM : M.PosSemidef)
    (g : V D) (hg : 0 < quadraticForm M g) :
    ContinuousWithinAt (fun A ↦ gaussianSign A g) {A | A.PosSemidef} M := by
  have hev : Continuous (fun A : Matrix D D ℂ ↦ Matrix.toEuclideanLin A g) := by
    change Continuous (fun A : Matrix D D ℂ ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := D) A g)
    have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := D)).toAlgEquiv.toLinearEquiv
      |>.toContinuousLinearEquiv.continuous
    exact h.clm_apply continuous_const
  have hq : Continuous (fun A : Matrix D D ℂ ↦ quadraticForm A g) :=
    Complex.continuous_re.comp (continuous_const.inner hev)
  have hs : ContinuousWithinAt CFC.sqrt {A : Matrix D D ℂ | A.PosSemidef} M :=
    (CFC.continuousOn_sqrt M hM.nonneg).mono fun _ hA ↦ hA.nonneg
  have ho : Continuous (gaussianOuter (D := D)) := by unfold gaussianOuter vecMulVec; fun_prop
  exact (hq.continuousWithinAt.inv₀ hg.ne').smul
    ((ho.comp hev).continuousAt.comp_continuousWithinAt hs)

/-- The determinant integral is continuous along positive semidefinite matrices at
every nonzero limit, even when the limit is singular. -/
theorem spatialSign_continuousWithinAt_posSemidef {M : Matrix D D ℂ} (hM : M.PosSemidef)
    (hn : M ≠ 0) : ContinuousWithinAt spatialSign {A | A.PosSemidef} M := by
  let : IsProbabilityMeasure (circularGaussian D) := by unfold circularGaussian; infer_instance
  have hcone : ∀ᶠ A in 𝓝[{N : Matrix D D ℂ | N.PosSemidef}] M, A.PosSemidef :=
    self_mem_nhdsWithin
  have h := continuousWithinAt_of_dominated (F := gaussianSign) (μ := circularGaussian D)
    (s := {A : Matrix D D ℂ | A.PosSemidef}) (x₀ := M) (bound := fun _ ↦ (1 : ℝ))
    (hcone.mono fun A hA ↦ (gaussianSign_integrable hA).aestronglyMeasurable)
    (hcone.mono fun A hA ↦ .of_forall (gaussianSign_norm_le_one hA))
    (integrable_const _) ((quadraticForm_pos_ae hM hn).mono fun g hg ↦
      gaussianSign_continuousWithinAt hM g hg)
  exact h.congr (fun _ hA ↦ spatialSign_gaussian_expectation hA)
    (spatialSign_gaussian_expectation hM)

/-- In particular the spatial sign matrix is continuous on positive definite matrices. -/
theorem spatialSign_continuousOn_posDef :
    ContinuousOn (spatialSign (D := D)) {M | M.PosDef} := by
  cases isEmpty_or_nonempty D with
  | inl he => exact (continuous_of_const fun _ _ ↦ Subsingleton.elim _ _).continuousOn
  | inr hn =>
    intro M hM
    exact (spatialSign_continuousWithinAt_posSemidef hM.posSemidef hM.isUnit.ne_zero).mono
      fun N hN ↦ hN.posSemidef

end SubentropyCertificates.ConditionalContinuity
