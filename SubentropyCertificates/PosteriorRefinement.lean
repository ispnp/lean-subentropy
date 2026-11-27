module
public import SubentropyCertificates.QuantumEquality
public import SubentropyCertificates.PinchingGeometry
public import SubentropyCertificates.PinchingIntegral

/-! The spectral construction in the retained PinchingUpper module, originating
in the Omega Institute's pinching_upper (see provenance.json and LICENSE.upstream),
is exposed here with its eigenvectors and intermediate classical Jensen bound. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
namespace SubentropyCertificates.PinchingEquality
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.PinchingGap
open SubentropyCertificates.MeasurementPosterior
open SubentropyCertificates.ClassicalCurve
variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

theorem spectral_refinement (G : Matrix (X × B) (X × B) ℂ) (hG : G.PosSemidef)
    (htr : G.trace = 1) (x₀ : X) :
    ∃ (w : X × B → ℝ), (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∃ v : X × B → X × B → ℂ, (∀ i, amplitude (v i) (v i) = 1) ∧
        G = ∑ i, w i • projector (v i) ∧
        (∑ i, w i * gain (projector (v i))) ≤ classicalSubentropy (labelMass G) := by
  let w := hG.isHermitian.eigenvalues
  let v : (X × B) → (X × B) → ℂ := fun j => ⇑(hG.isHermitian.eigenvectorBasis j)
  let R := fun j => Matrix.vecMulVec (v j) (star (v j))
  let r : (X × B) → X → ℝ := fun j x => ∑ b, Complex.normSq (v j (x,b))
  have hw := spectral_prob hG htr
  have hv (j : X × B) : ∑ i, star (v j i) * v j i = 1 := by
    change star (⇑(hG.isHermitian.eigenvectorBasis j)) ⬝ᵥ
      ⇑(hG.isHermitian.eigenvectorBasis j) = 1
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hG.isHermitian.eigenvectorBasis.orthonormal.1 j]
    norm_num
  have hdecomp : G = ∑ j, w j • R j := by
    ext a b
    conv_lhs => rw [hG.isHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, w, v, R]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hr (j : X × B) : (∀ x, 0 ≤ r j x) ∧ ∑ x, r j x = 1 := by
    refine ⟨fun x => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _, ?_⟩
    have hC : ((∑ x, r j x : ℝ) : ℂ) = 1 := by
      simpa only [r, Complex.ofReal_sum, Fintype.sum_prod_type,
        Complex.normSq_eq_conj_mul_self, starRingEnd_apply] using hv j
    exact_mod_cast hC
  have hD (j : X × B) :
      (diagonal (fun x => (r j x : ℂ))).PosSemidef ∧
        (diagonal (fun x => (r j x : ℂ))).trace = 1 := by
    refine ⟨Matrix.PosSemidef.diagonal (fun x => by
      simpa [Complex.le_def] using (hr j).1 x), ?_⟩
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, (hr j).2, Complex.ofReal_one]
  have hmass (x : X) : (∑ j, w j * r j x) = (∑ b, G (x,b) (x,b)).re := by
    rw [hdecomp]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul,
      R, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum, r]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hDsum : (∑ j, w j • diagonal (fun x => (r j x : ℂ))) =
      diagonal (fun x => (((∑ b, G (x,b) (x,b)).re : ℝ) : ℂ)) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
        Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sum, hmass]
    · simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hxy]
  have hd := ConcaveOn.le_map_sum (matrix_subentropy_concave x₀)
    (t := Finset.univ) (w := w) (p := fun j => diagonal (fun x => (r j x : ℂ)))
    (fun j _ => hw.1 j) hw.2 (fun j _ => hD j)
  rw [hDsum] at hd
  refine ⟨w, hw.1, hw.2, v, hv, hdecomp, ?_⟩
  calc
    _ = ∑ j, w j * matrixSubentropy (diagonal (fun x => (r j x : ℂ))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (w j * ·) (pure_block_pinching (v j) (hv j)).1
    _ ≤ _ := hd


theorem refinement_of_gram_pieces {Y : Type*} [Fintype Y]
    (G : Y → Matrix (X × B) (X × B) ℂ) (hG : ∀ y, (G y).PosSemidef)
    (htr : (∑ y, G y).trace = 1) (x₀ : X) :
    ∃ w : Y × (X × B) → ℝ, (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧
      ∃ v : Y × (X × B) → X × B → ℂ, (∀ k, amplitude (v k) (v k) = 1) ∧
        (∑ y, G y) = ∑ k, w k • projector (v k) ∧
        (∑ k, w k * gain (projector (v k))) ≤
          ∑ y ∈ Finset.univ.filter (fun y => 0 < mass (G y)),
            mass (G y) * classicalSubentropy (labelPosterior (G y)) := by
  classical
  let T := ∑ y, G y
  let q y := mass (G y)
  have hq y : 0 ≤ q y := mass_nonneg _ (hG y)
  have hs : ∑ y, q y = 1 := by
    simp only [q, mass, ← Complex.re_sum, ← Matrix.trace_sum, htr, Complex.one_re]
  let H y := if q y = 0 then T else (q y)⁻¹ • G y
  have hH y : (H y).PosSemidef ∧ (H y).trace = 1 := by
    by_cases hz : q y = 0
    · simp only [H, hz, ite_true]
      exact ⟨Matrix.posSemidef_sum _ (fun i _ => hG i), htr⟩
    · simp only [H, ite_eq_right hz]
      refine ⟨(hG y).smul (inv_nonneg.mpr (hq y)), ?_⟩
      rw [Matrix.trace_smul, psd_trace_eq_real_mass _ (hG y)]
      change (q y)⁻¹ • (q y : ℂ) = 1
      simp [hz]
  have hpiece y : q y • H y = G y := by
    by_cases hz : q y = 0
    · rw [hz, zero_smul, psd_eq_zero_of_mass_zero _ (hG y) hz]
    · simp only [H, ite_eq_right hz, smul_smul, mul_inv_cancel₀ hz, one_smul]
  have spec y := spectral_refinement (H y) (hH y).1 (hH y).2 x₀
  let w y := (spec y).choose
  have ws y := (spec y).choose_spec
  let v y := (ws y).2.2.choose
  have vs y := (ws y).2.2.choose_spec
  refine ⟨fun k => q k.1 * w k.1 k.2, fun k => mul_nonneg (hq _) ((ws _).1 _), ?_,
    fun k => v k.1 k.2, fun k => (vs _).1 _, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simpa only [← Finset.mul_sum, w, fun y => (ws y).2.1, mul_one] using hs
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro y _
    calc
      G y = q y • H y := (hpiece y).symm
      _ = q y • ∑ k, w y k • projector (v y k) := congrArg (q y • ·) (vs y).2.1
      _ = _ := by simp only [Finset.smul_sum, smul_smul]
  · rw [Fintype.sum_prod_type, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro y _
    change (∑ j, (q y * w y j) * gain (projector (v y j))) ≤
      if 0 < q y then q y * classicalSubentropy (labelPosterior (G y)) else 0
    by_cases hy : 0 < q y
    · have hlabels : labelMass (H y) = labelPosterior (G y) := by
        funext x
        rw [show H y = (q y)⁻¹ • G y from ite_eq_right hy.ne', labelMass_smul]
        simp only [labelPosterior, q, div_eq_mul_inv]
        ring
      simp only [hy, ite_true, mul_assoc, ← Finset.mul_sum]
      rw [← hlabels]
      exact mul_le_mul_of_nonneg_left (vs y).2.2 hy.le
    · have hz : q y = 0 := le_antisymm (le_of_not_gt hy) (hq y)
      simp [hz]

end SubentropyCertificates.PinchingEquality
