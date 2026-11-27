module

public import SubentropyCertificates.CircularRadii
public import SubentropyCertificates.GaussianSignBound
public import SubentropyCertificates.GaussianSignSpectral
public import SubentropyCertificates.ExponentialSignMoments

/-! The Gaussian representation of K, and the first moment of the logarithmic Gaussian tilt. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
private theorem radii_test (f : (D → ℝ) → ℝ) (hf : Measurable f) :
    (∫ g, f (fun i ↦ Complex.normSq (g i)) ∂circularGaussian D) =
      ∫ z, f z ∂Measure.pi (fun _ ↦ expMeasure 1) := by
  rw [← circular_radii_map D, integral_map (by fun_prop) hf.aestronglyMeasurable]

private theorem radial_sign (w : D → ℝ) (hw : ∀ j, 0 ≤ w j) (i : D) :
    (∫ g, w i * Complex.normSq (g i) / diagonalEnergy w g ∂circularGaussian D) =
      ∫ t in Ioi (0 : ℝ), (w i / (1 + t*w i)) * ∏ j, (1 + t*w j)⁻¹ :=
  (radii_test (fun z ↦ w i*z i / (∑ j, w j*z j)) (by fun_prop)).trans
    (exponential_sign_integral w hw i)

private theorem radial_log (w : D → ℝ) (hw : ∀ j, 0 < w j) (i : D) :
    (∫ g, (1 + Real.log (diagonalEnergy w g)) * Complex.normSq (g i) ∂circularGaussian D) =
      1 + (∫ g, Real.log (diagonalEnergy w g) ∂circularGaussian D) +
      ∫ g, w i * Complex.normSq (g i) / diagonalEnergy w g ∂circularGaussian D := by
  let T (z : D → ℝ) := ∑ j, w j*z j
  have hT : Measurable T := by dsimp [T]; fun_prop
  have h := exponential_log_moment w hw i
  exact ((radii_test (fun z ↦ (1 + Real.log (T z)) * z i) (by fun_prop)).trans h).trans
    (congrArg₂ (· + ·)
      (congrArg (1 + ·) (radii_test (fun z ↦ Real.log (T z)) (by fun_prop)).symm)
      (radii_test (fun z ↦ w i*z i/T z) (by fun_prop)).symm)

/-- The determinant integral agrees with the Gaussian normalized outer product for every
positive semidefinite matrix. The totalized expression also equals zero at the zero matrix. -/
theorem spatialSign_gaussian_expectation {M : Matrix D D ℂ} (hM : M.PosSemidef) :
    spatialSign M = ∫ g, gaussianSign M g ∂circularGaussian D := by
  rw [spatialSign_spectral hM, gaussianSign_spectral hM (gaussianSign_integrable hM)]
  simp_rw [radial_sign _ hM.eigenvalues_nonneg]

/-- For a nonzero covariance the denominator is strictly positive almost surely,
even when the matrix is singular. -/
theorem quadraticForm_pos_ae {M : Matrix D D ℂ} (hM : M.PosSemidef) (hn : M ≠ 0) :
    ∀ᵐ g ∂circularGaussian D, 0 < quadraticForm M g := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < hM.isHermitian.eigenvalues i := by
    by_contra! he
    exact hn (hM.isHermitian.eigenvalues_eq_zero_iff.mp
      (funext fun i ↦ le_antisymm (he i) (hM.eigenvalues_nonneg i)))
  have hz : ∀ᵐ t ∂expMeasure 1, t ≠ 0 := by
    rw [expMeasure, gammaMeasure]
    exact (Measure.ae_le_iff_absolutelyContinuous.mpr (withDensity_absolutelyContinuous _ _))
      (volume.ae_ne (0 : ℝ))
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hprod := (measurePreserving_eval (fun _ : D ↦ expMeasure 1) i).quasiMeasurePreserving.ae hz
  rw [← circular_radii_map D] at hprod
  have hr := ae_of_ae_map (by fun_prop : AEMeasurable (fun (g : V D) j ↦ Complex.normSq (g j))
    (circularGaussian D)) hprod
  apply (quadraticForm_spectral_ae hM.isHermitian (0 < ·)).2
  filter_upwards [hr] with g hg
  have hzi : 0 < Complex.normSq (g i) := lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hg)
  exact lt_of_lt_of_le (mul_pos hi hzi) (Finset.single_le_sum
    (fun j _ ↦ mul_nonneg (hM.eigenvalues_nonneg j) (Complex.normSq_nonneg (g j)))
    (Finset.mem_univ i))

/-- The Gaussian representation has trace one at every nonzero covariance. -/
theorem spatialSign_trace_one {M : Matrix D D ℂ} (hM : M.PosSemidef) (hn : M ≠ 0) :
    (spatialSign M).trace = 1 := by
  let L : Matrix D D ℂ →L[ℝ] ℂ := (Matrix.traceLinearMap D ℝ ℂ).toContinuousLinearMap
  let : IsProbabilityMeasure (circularGaussian D) := by unfold circularGaussian; infer_instance
  rw [spatialSign_gaussian_expectation hM]
  change L _ = 1
  rw [← L.integral_comp_comm (gaussianSign_integrable hM)]
  calc
    _ = ∫ _ : V D, (1 : ℂ) ∂circularGaussian D := by
      apply integral_congr_ae
      filter_upwards [quadraticForm_pos_ae hM hn] with g hg
      let y := Matrix.toEuclideanLin (CFC.sqrt M) g
      have ho : (gaussianOuter y).trace = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
        rw [gaussianOuter, trace_vecMulVec, Complex.ofReal_pow]
        exact (EuclideanSpace.inner_eq_star_dotProduct y y).symm.trans (inner_self_eq_norm_sq_to_K _)
      change ((quadraticForm M g)⁻¹ • gaussianOuter y).trace = _
      rw [trace_smul, ho, ← quadraticForm_sqrt_norm hM g, Complex.real_smul,
        ← Complex.ofReal_mul, inv_mul_cancel₀ hg.ne', Complex.ofReal_one]
    _ = 1 := by simp

/-- Integration by parts identifies the Gaussian derivative moment at a positive definite M. -/
theorem gaussianSlope_eq_of_integrable {M : Matrix D D ℂ} (hM : M.PosDef)
    (hi : Integrable (fun g ↦ (1 + Real.log (quadraticForm M g)) • gaussianOuter g)
      (circularGaussian D)) :
    gaussianSlope M = (1 + gaussianLogMean M) • 1 + spatialSign M := by
  let h := hM.isHermitian
  let U := Unitary.conjStarAlgAut ℂ _ h.eigenvectorUnitary
  let w := h.eigenvalues
  let b := 1 + ∫ g, Real.log (diagonalEnergy w g) ∂circularGaussian D
  let v (i : D) := ∫ g, w i * Complex.normSq (g i) / diagonalEnergy w g ∂circularGaussian D
  rw [gaussianSlope_spectral h hi, gaussianLogMean_spectral h, spatialSign_gaussian_expectation
    hM.posSemidef, gaussianSign_spectral hM.posSemidef (gaussianSign_integrable hM.posSemidef)]
  change U (diagonal fun i ↦ ((∫ g, (1 + Real.log (diagonalEnergy w g)) *
    Complex.normSq (g i) ∂circularGaussian D : ℝ) : ℂ)) = b • 1 + U (diagonal fun i ↦ (v i : ℂ))
  have he (i : D) : (∫ g, (1 + Real.log (diagonalEnergy w g)) * Complex.normSq (g i)
      ∂circularGaussian D) = b + v i := radial_log w hM.eigenvalues_pos i
  simp_rw [he, Complex.ofReal_add]
  rw [← diagonal_add (fun _ : D ↦ (b : ℂ)) (fun i ↦ (v i : ℂ)), map_add]
  congr 1
  have hid : diagonal (fun _ : D ↦ (b : ℂ)) = (b : ℂ) • (1 : Matrix D D ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hid, map_smul, map_one]
  rfl

end SubentropyCertificates.ConditionalContinuity
