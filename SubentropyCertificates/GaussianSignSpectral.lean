module
public import SubentropyCertificates.GaussianGradientDefs
import all D5.S3.Quantum.Subentropy.GaussianQuadratic

/-! Spectral coordinates for the spatial sign integral and the Gaussian gradient. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations
open SubentropyCertificates.DeterminantComparison
open SubentropyCertificates.ClassicalSSA
open D5.S3.Quantum.Subentropy.GaussianQuadratic

variable {D : Type*} [Fintype D] [DecidableEq D]

private abbrev matEval (i j : D) : Matrix D D ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M ↦ M i j, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }

private abbrev spectralConj (U : Matrix.unitaryGroup D ℂ) :
    Matrix D D ℂ ≃L[ℝ] Matrix D D ℂ :=
  ((Unitary.conjStarAlgAut ℂ _ U).toAlgEquiv.toLinearEquiv.restrictScalars ℝ)
    |>.toContinuousLinearEquiv

omit [DecidableEq D] in
private theorem circPreserving (e : V D ≃ₗᵢ[ℂ] V D) :
    MeasurePreserving e (circularGaussian D) (circularGaussian D) := by
  refine ⟨e.continuous.measurable, ?_⟩
  have hn : Measurable (normalizeGaussian (D := D)) := by unfold normalizeGaussian; fun_prop
  have hcomm : e ∘ normalizeGaussian = normalizeGaussian ∘ e := by
    funext z
    change e (((√2)⁻¹ : ℝ) • z) = ((√2)⁻¹ : ℝ) • e z
    exact (realIsometry e).map_smul _ _
  rw [circularGaussian, Measure.map_map e.continuous.measurable hn, hcomm,
    ← Measure.map_map hn e.continuous.measurable]
  exact congrArg (Measure.map normalizeGaussian) (stdGaussian_map (realIsometry e))

private def flipCoord (i : D) : V D ≃ₗᵢ[ℂ] V D :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j : D ↦ if j = i then (LinearIsometryEquiv.neg ℂ : ℂ ≃ₗᵢ[ℂ] ℂ)
      else LinearIsometryEquiv.refl ℂ ℂ)

private theorem flip_apply (i j : D) (z : V D) :
    flipCoord i z j = if j = i then -z j else z j := by
  change (if j = i then (LinearIsometryEquiv.neg ℂ : ℂ ≃ₗᵢ[ℂ] ℂ)
    else LinearIsometryEquiv.refl ℂ ℂ) (z j) = _
  split_ifs <;> rfl

private theorem basis_action {M : Matrix D D ℂ} (h : M.IsHermitian) (z : V D) :
    ⇑(h.eigenvectorBasis.repr.symm z) = (h.eigenvectorUnitary : Matrix D D ℂ) *ᵥ (fun i ↦ z i) := by
  funext j
  rw [← OrthonormalBasis.sum_repr_symm]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, mulVec, dotProduct,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

private theorem base_quad {M : Matrix D D ℂ} (h : M.IsHermitian) (z : V D) :
    quadraticForm M (h.eigenvectorBasis.repr.symm z) = diagonalEnergy h.eigenvalues z := by
  have hh := (spectral_transport h).1 z
  unfold gaussianQuadratic at hh
  change (inner ℂ _ _).re = _
  unfold diagonalEnergy
  linarith

private theorem outer_transport {U : Matrix.unitaryGroup D ℂ} {y z : V D}
    (hy : ⇑y = (U : Matrix D D ℂ) *ᵥ (fun i ↦ z i)) :
    gaussianOuter y = spectralConj U (gaussianOuter z) := by
  change vecMulVec (fun i ↦ y i) (star (fun i ↦ y i)) =
    (U : Matrix D D ℂ) * gaussianOuter z * (U : Matrix D D ℂ).conjTranspose
  rw [hy, Matrix.star_mulVec, gaussianOuter, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rfl


private def scaleCoords (a : D → ℝ) (g : V D) : V D :=
  WithLp.toLp 2 (fun i ↦ (a i : ℂ) * g i)

private def weightedOuter (w a : D → ℝ) (f : ℝ → ℝ) (g : V D) : Matrix D D ℂ :=
  f (diagonalEnergy w g) • gaussianOuter (scaleCoords a g)

omit [DecidableEq D] in
private theorem weight_entry (w a : D → ℝ) (f : ℝ → ℝ) (g : V D) (i j : D) :
    weightedOuter w a f g i j =
      (f (diagonalEnergy w g) * a i * a j : ℝ) * (g i * star (g j) : ℂ) := by
  change ((f (diagonalEnergy w g) : ℂ) * (((a i : ℂ) * g i) * star ((a j : ℂ) * g j))) = _
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

private theorem phase_integral (w a : D → ℝ) (f : ℝ → ℝ) {i j : D} (hij : i ≠ j) :
    (∫ z, weightedOuter w a f z i j ∂circularGaussian D) = 0 := by
  let e := flipCoord i
  have henergy (z : V D) : diagonalEnergy w (e z) = diagonalEnergy w z := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show e z k = _ from flip_apply i k z]
    split_ifs <;> simp
  have hx (g : V D) : weightedOuter w a f (e g) i j = -weightedOuter w a f g i j := by
    rw [weight_entry, weight_entry, henergy, show e g i = -g i by simp [e, flip_apply],
      show e g j = g j by simp [e, flip_apply, hij.symm], neg_mul, mul_neg]
  have h := (circPreserving e).integral_comp e.toHomeomorph.measurableEmbedding
    (fun z ↦ weightedOuter w a f z i j)
  simp only [hx, integral_neg] at h
  exact neg_eq_self.mp h

private theorem weighted_integral (w a : D → ℝ) (f : ℝ → ℝ)
    (hi : Integrable (weightedOuter w a f) (circularGaussian D)) :
    (∫ z, weightedOuter w a f z ∂circularGaussian D) =
      diagonal (fun i ↦ ((∫ z, f (diagonalEnergy w z) * (a i)^2 * Complex.normSq (z i)
        ∂circularGaussian D : ℝ) : ℂ)) := by
  ext i j
  change matEval i j _ = _
  rw [← (matEval i j).integral_comp_comm hi]
  change (∫ z, weightedOuter w a f z i j ∂circularGaussian D) = _
  by_cases he : i = j
  · subst j
    rw [diagonal_apply_eq, ← integral_complex_ofReal]
    apply integral_congr_ae
    refine .of_forall fun z ↦ ?_
    change weightedOuter w a f z i i = _
    rw [weight_entry]
    simp only [sq, mul_assoc]
    simp only [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  · rw [diagonal_apply_ne _ he, phase_integral w a f he]

private theorem spectral_moment {M : Matrix D D ℂ} (h : M.IsHermitian)
    (F : V D → Matrix D D ℂ) (a : D → ℝ) (f : ℝ → ℝ)
    (hi : Integrable F (circularGaussian D))
    (hF : ∀ g, F (h.eigenvectorBasis.repr.symm g) =
      spectralConj h.eigenvectorUnitary (weightedOuter h.eigenvalues a f g)) :
    (∫ g, F g ∂circularGaussian D) =
      spectralConj h.eigenvectorUnitary (diagonal fun i ↦
        ((∫ z, f (diagonalEnergy h.eigenvalues z) * (a i)^2 * Complex.normSq (z i)
          ∂circularGaussian D : ℝ) : ℂ)) := by
  let e := h.eigenvectorBasis.repr.symm
  have he := circPreserving e
  have hcomp := (he.integrable_comp_emb e.toHomeomorph.measurableEmbedding).2 hi
  change Integrable (fun z ↦ F (h.eigenvectorBasis.repr.symm z)) _ at hcomp
  simp_rw [hF] at hcomp
  rw [← he.integral_comp e.toHomeomorph.measurableEmbedding F]
  change (∫ z, F (h.eigenvectorBasis.repr.symm z) ∂_) = _
  simp_rw [hF]
  rw [ContinuousLinearEquiv.integral_comp_comm,
    weighted_integral _ _ _ ((spectralConj h.eigenvectorUnitary).integrable_comp_iff.mp hcomp)]


private theorem diag_resolvent {M : Matrix D D ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    signResolvent M t = spectralConj hM.isHermitian.eigenvectorUnitary
      (diagonal (fun i ↦ ((hM.isHermitian.eigenvalues i /
        (1 + t * hM.isHermitian.eigenvalues i) : ℝ) : ℂ))) := by
  let w := hM.isHermitian.eigenvalues
  let U := Unitary.conjStarAlgAut ℂ _ hM.isHermitian.eigenvectorUnitary
  let d (f : D → ℝ) := diagonal (fun i ↦ (f i : ℂ))
  have hbase : M = U (d w) := hM.isHermitian.spectral_theorem
  have hshift : 1 + t • M = U (d (fun i ↦ 1 + t*w i)) := by
    have hm : t • U (d w) = U (t • d w) := ((spectralConj _).map_smul t (d w)).symm
    rw [hbase, hm, ← map_one U, ← map_add]
    congr 1
    ext i j
    by_cases he : i = j
    · subst j
      simp [d, Complex.real_smul]
    · simp [d, he]
  let N := U (d (fun i ↦ w i / (1+t*w i)))
  have hid : N * (1 + t • M) = M := by
    rw [hshift, hbase]
    change U _ * U _ = U _
    rw [← map_mul]
    apply congrArg U
    simp only [d, diagonal_mul_diagonal, ← Complex.ofReal_mul]
    congr 1
    funext i
    have hn : 0 ≤ w i := hM.eigenvalues_nonneg _
    rw [div_mul_cancel₀ _ (by positivity)]
  change M * (1 + t • M)⁻¹ = N
  calc _ = (N * (1+t • M)) * (1+t • M)⁻¹ := congrArg (· * _) hid.symm
       _ = N := by rw [mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
                    (shifted_posDef hM ht).isUnit), Matrix.mul_one]

/-- In the eigenbasis of M the determinant integral is diagonal, also at repeated
and zero eigenvalues. -/
theorem spatialSign_spectral {M : Matrix D D ℂ} (hM : M.PosSemidef) :
    let w := hM.isHermitian.eigenvalues
    spatialSign M = Unitary.conjStarAlgAut ℂ _ hM.isHermitian.eigenvectorUnitary
      (diagonal fun i ↦ ((∫ t in Ioi (0 : ℝ),
        (w i / (1 + t * w i)) * ∏ j, (1 + t * w j)⁻¹ : ℝ) : ℂ)) := by
  let w := hM.isHermitian.eigenvalues
  let U := spectralConj hM.isHermitian.eigenvectorUnitary
  let f (t : ℝ) (i : D) := (w i / (1 + t*w i)) * ∏ j, (1+t*w j)⁻¹
  let F (t : ℝ) := diagonal (fun i ↦ (f t i : ℂ))
  have hid : (fun t ↦ U (F t)) =ᵐ[volume.restrict (Ioi (0 : ℝ))] signKernel M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [signKernel, diag_resolvent hM ht.le, reciprocalDet_spectral hM.isHermitian]
    change U _ = _ • U _
    rw [← U.map_smul]
    apply congrArg U
    ext i j
    by_cases he : i = j
    · subst j
      simp [F, f, kernel, factor, w, Complex.real_smul, mul_comm]
    · simp [F, he]
  have hi : IntegrableOn F (Ioi 0) := U.integrable_comp_iff.mp
    ((signKernel_integrable hM).congr hid.symm)
  unfold spatialSign
  rw [← integral_congr_ae hid, ContinuousLinearEquiv.integral_comp_comm]
  apply congrArg U
  ext i j
  change matEval i j _ = _
  rw [← (matEval i j).integral_comp_comm hi]
  by_cases he : i = j
  · subst j
    change (∫ t in Ioi (0 : ℝ), F t i i) = _
    simp only [F, diagonal_apply_eq]
    exact integral_complex_ofReal (f := fun t ↦ f t i)
  · change (∫ t in Ioi (0 : ℝ), F t i j) = _
    simp only [F, diagonal_apply_ne _ he, integral_zero]

/-- Spectral transport preserves almost sure properties of the quadratic form. -/
theorem quadraticForm_spectral_ae {M : Matrix D D ℂ} (h : M.IsHermitian) (p : ℝ → Prop) :
    (∀ᵐ g ∂circularGaussian D, p (quadraticForm M g)) ↔
      ∀ᵐ z ∂circularGaussian D, p (diagonalEnergy h.eigenvalues z) := by
  let e := h.eigenvectorBasis.repr.symm
  calc
    _ ↔ ∀ᵐ g ∂(circularGaussian D).map e, p (quadraticForm M g) := by rw [(circPreserving e).map_eq]
    _ ↔ ∀ᵐ z ∂circularGaussian D, p (quadraticForm M (e z)) :=
      e.toHomeomorph.measurableEmbedding.ae_map_iff
    _ ↔ _ := by simp only [e, base_quad]

/-- The Gaussian mean of log(g* M g) in spectral coordinates. -/
theorem gaussianLogMean_spectral {M : Matrix D D ℂ} (hM : M.IsHermitian) :
    gaussianLogMean M = ∫ z, Real.log (diagonalEnergy hM.eigenvalues z) ∂circularGaussian D := by
  let e := hM.eigenvectorBasis.repr.symm
  unfold gaussianLogMean
  rw [← (circPreserving e).integral_comp e.toHomeomorph.measurableEmbedding]
  simp only [e, base_quad]

/-- The derivative moment is diagonal in the eigenbasis, with the indicated weighted
exponential moments as entries. -/
theorem gaussianSlope_spectral {M : Matrix D D ℂ} (hM : M.IsHermitian)
    (hi : Integrable (fun g ↦ (1 + Real.log (quadraticForm M g)) • gaussianOuter g)
      (circularGaussian D)) :
    gaussianSlope M = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary
      (diagonal fun i ↦ ((∫ z, (1 + Real.log (diagonalEnergy hM.eigenvalues z)) *
        Complex.normSq (z i) ∂circularGaussian D : ℝ) : ℂ)) := by
  have h := spectral_moment hM _ (fun _ ↦ 1) (fun t ↦ 1 + Real.log t) hi (by
    intro z
    rw [base_quad, outer_transport (basis_action hM z)]
    have hsc : scaleCoords (fun _ : D ↦ 1) z = z := by ext i; simp [scaleCoords]
    simp [weightedOuter, hsc])
  unfold gaussianSlope
  refine h.trans ?_
  apply congrArg (spectralConj hM.eigenvectorUnitary)
  simp only [one_pow, mul_one]


private theorem sqrt_action {M : Matrix D D ℂ} (hM : M.PosSemidef) (g : V D) :
    let h := hM.isHermitian
    ⇑(Matrix.toEuclideanLin (CFC.sqrt M) (h.eigenvectorBasis.repr.symm g)) =
      (h.eigenvectorUnitary : Matrix D D ℂ) *ᵥ ⇑(scaleCoords (fun i ↦ √(h.eigenvalues i)) g) := by
  let h := hM.isHermitian
  let U : Matrix D D ℂ := h.eigenvectorUnitary
  let s (i : D) := (√(h.eigenvalues i) : ℂ)
  have hs : CFC.sqrt M = U * diagonal s * U.conjTranspose := by
    rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ M hM.nonneg, h.cfc_eq,
      Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp only [s, Real.sqrt, RCLike.ofReal_eq_complex_ofReal]
    rfl
  have hunit : U.conjTranspose * U = 1 := Unitary.coe_star_mul_self h.eigenvectorUnitary
  change CFC.sqrt M *ᵥ ⇑(h.eigenvectorBasis.repr.symm g) = U *ᵥ _
  rw [basis_action, hs]
  change (U * diagonal s * U.conjTranspose) *ᵥ (U *ᵥ ⇑g) = U *ᵥ _
  rw [mulVec_mulVec, Matrix.mul_assoc (U * _) U.conjTranspose, hunit, Matrix.mul_one,
    ← mulVec_mulVec]
  apply congrArg (U *ᵥ ·)
  funext i
  exact Matrix.mulVec_diagonal _ _ _

/-- Spectral expansion of the Gaussian expectation defining the spatial sign matrix. -/
theorem gaussianSign_spectral {M : Matrix D D ℂ} (hM : M.PosSemidef)
    (hi : Integrable (gaussianSign M) (circularGaussian D)) :
    let w := hM.isHermitian.eigenvalues
    (∫ g, gaussianSign M g ∂circularGaussian D) =
      Unitary.conjStarAlgAut ℂ _ hM.isHermitian.eigenvectorUnitary (diagonal fun i ↦
        ((∫ z, w i * Complex.normSq (z i) / diagonalEnergy w z ∂circularGaussian D : ℝ) : ℂ)) := by
  let h := hM.isHermitian
  have H := spectral_moment h _ (fun i ↦ √(h.eigenvalues i)) (fun t ↦ t⁻¹) hi (by
    intro g
    rw [gaussianSign, base_quad, outer_transport (sqrt_action hM g)]
    simp [weightedOuter])
  refine H.trans ?_
  apply congrArg (spectralConj h.eigenvectorUnitary)
  congr 1
  funext i
  apply congrArg Complex.ofReal
  apply integral_congr_ae
  refine .of_forall fun g ↦ ?_
  change _ * (√(h.eigenvalues i))^2 * _ = h.eigenvalues i * Complex.normSq (g i) /
    diagonalEnergy h.eigenvalues g
  rw [sq_sqrt (hM.eigenvalues_nonneg i), div_eq_mul_inv]
  ring

end SubentropyCertificates.ConditionalContinuity

