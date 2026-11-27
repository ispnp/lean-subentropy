module

public import SubentropyCertificates.MixedMarginalNorm
public import SubentropyCertificates.SubentropyMaximum

/-! Spectral coordinates and values of the optimal fixed-marginal coefficient. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.BinarySpectra (densityMatrix)
open SubentropyCertificates.SpectralContinuity (maximallyMixed maximallyMixed_matrix)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
private theorem ne_zero_of_trace_one {M : Matrix D D ℂ} (ht : M.trace = 1) : M ≠ 0 := by
  rintro rfl
  simp at ht

/-- A top spatial sign weight lies on a positive eigenvalue of the marginal, including
at singular marginals. The two eigenbases are identified by the spectral integral formula. -/
theorem exists_spatialSign_top_coordinate {M : Matrix D D ℂ} (hM : M.PosSemidef)
    (ht : M.trace = 1) :
    ∃ i, 0 < hM.isHermitian.eigenvalues i ∧
      (∫ t in Ioi (0 : ℝ), (hM.isHermitian.eigenvalues i / (1 + t * hM.isHermitian.eigenvalues i)) *
        ∏ j, (1 + t * hM.isHermitian.eigenvalues j)⁻¹) = ‖spatialSign M‖ := by
  let w := hM.isHermitian.eigenvalues
  let k (i : D) := ∫ t in Ioi (0 : ℝ),
    (w i / (1 + t*w i)) * ∏ j, (1+t*w j)⁻¹
  have hn := ne_zero_of_trace_one ht
  have : Nonempty D := by
    by_contra! he
    exact hn (Subsingleton.elim _ _)
  have hkn := ne_zero_of_trace_one (spatialSign_trace_one hM hn)
  have hpos (i : D) : 0 ≤ k i := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht'
    have hw := hM.eigenvalues_nonneg
    change 0 ≤ (w i / (1 + t * w i)) * ∏ j, (1 + t * w j)⁻¹
    have hw' (j : D) : 0 ≤ w j := hw j
    have ht'' : 0 ≤ t := ht'.le
    have hden (j : D) : 0 ≤ 1 + t * w j := add_nonneg zero_le_one (mul_nonneg ht'' (hw' j))
    exact mul_nonneg (div_nonneg (hw' i) (hden i))
      (Finset.prod_nonneg fun j _ ↦ inv_nonneg.mpr (hden j))
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ k Finset.univ_nonempty
  have hnorm : ‖spatialSign M‖ = k i := by
    rw [spatialSign_spectral hM]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
    change ‖(fun u : D ↦ (k u : ℂ))‖ = _
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (hpos i)).2
      intro j
      simpa [Real.norm_of_nonneg (hpos j)] using hi j (Finset.mem_univ j)
    · simpa [Real.norm_of_nonneg (hpos i)] using norm_le_pi_norm (fun j : D ↦ (k j : ℂ)) i
  refine ⟨i, lt_of_le_of_ne (hM.eigenvalues_nonneg i) ?_, hnorm.symm⟩
  intro hz
  have hzero : w i = 0 := hz.symm
  exact hkn (norm_eq_zero.mp (by simpa [k, hzero] using hnorm))

/-- A pure marginal has fixed-marginal coefficient one. -/
theorem spatialSign_norm_eq_one_of_rank_one {M : Matrix D D ℂ} (hM : M.PosSemidef)
    (hr : M.rank = 1) : ‖spatialSign M‖ = 1 := by
  have hn : M ≠ 0 := by rintro rfl; simp at hr
  let K := spatialSign M
  have hK : K.PosSemidef := spatialSign_posSemidef hM
  have ht : K.trace = 1 := spatialSign_trace_one hM hn
  have hcard : Fintype.card {j // hK.isHermitian.eigenvalues j ≠ 0} = 1 := by
    rw [← hK.isHermitian.rank_eq_card_non_zero_eigs]
    exact (spatialSign_rank hM).trans hr
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hcard
  have : Nonempty D := ⟨a.val⟩
  have hspec := CStarAlgebra.norm_mem_spectrum_of_nonneg K hK.nonneg
  rw [hK.isHermitian.spectrum_real_eq_range_eigenvalues] at hspec
  obtain ⟨i, hi⟩ := hspec
  have hi0 : hK.isHermitian.eigenvalues i ≠ 0 := hi.trans_ne (norm_ne_zero_iff.mpr
    (ne_zero_of_trace_one ht))
  have hs : ∑ j, hK.isHermitian.eigenvalues j = 1 := by
    simpa [ht] using congrArg Complex.re hK.isHermitian.trace_eq_sum_eigenvalues.symm
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun j _ hj ↦ by
    by_contra he
    exact hj (congrArg Subtype.val ((ha ⟨j,he⟩).trans (ha ⟨i,hi0⟩).symm)))] at hs
  exact hi.symm.trans hs

/-- For a maximally mixed marginal, the spatial sign operator is itself maximally mixed. -/
theorem spatialSign_maximallyMixed (D : Type*) [Fintype D] [DecidableEq D] [Nonempty D] :
    spatialSign (densityMatrix (maximallyMixed D)) = densityMatrix (maximallyMixed D) := by
  let M := densityMatrix (maximallyMixed D)
  let hM : M.PosSemidef := density_posSemidef (maximallyMixed D)
  let w := hM.isHermitian.eigenvalues
  let c : ℂ := 1 / (Fintype.card D : ℂ)
  let C := Unitary.conjStarAlgAut ℂ _ hM.isHermitian.eigenvectorUnitary
  have hm : M = c • 1 := maximallyMixed_matrix D
  have hd : diagonal (fun j ↦ (w j : ℂ)) = c • 1 := by
    apply C.injective
    change C (diagonal (fun j ↦ (w j : ℂ))) = C (c • 1)
    rw [map_smul, map_one, ← hm]
    exact hM.isHermitian.spectral_theorem.symm
  have hw (j : D) : (w j : ℂ) = c := by
    simpa using congrArg (fun N : Matrix D D ℂ ↦ N j j) hd
  let i : D := Classical.choice inferInstance
  have he (j : D) : w j = w i := Complex.ofReal_injective ((hw j).trans (hw i).symm)
  let z : ℝ := ∫ t in Ioi (0 : ℝ), (w i / (1 + t*w i)) * ∏ j, (1+t*w j)⁻¹
  have hsign : spatialSign M = (z : ℂ) • 1 := by
    rw [spatialSign_spectral hM]
    change C (diagonal _) = _
    rw [← map_one C, ← map_smul]
    apply congrArg C
    ext j l
    by_cases h : j = l
    · subst l
      simp only [diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
      change ((∫ t in Ioi (0 : ℝ), (w j / (1 + t * w j)) * ∏ u, (1 + t * w u)⁻¹ : ℝ) : ℂ) = _
      rw [he j]
    · simp [h]
  have ht : M.trace = 1 := (maximallyMixed D).2.2
  have htr := spatialSign_trace_one hM (ne_zero_of_trace_one ht)
  rw [hsign, trace_smul, trace_one, smul_eq_mul] at htr
  have hz : (z : ℂ) = c := by
    exact (eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).2 htr
  exact hsign.trans ((congrArg (fun v : ℂ ↦ v • (1 : Matrix D D ℂ)) hz).trans hm.symm)

/-- The optimal coefficient at the maximally mixed marginal is the reciprocal dimension. -/
theorem spatialSign_norm_maximallyMixed (D : Type*) [Fintype D] [DecidableEq D] [Nonempty D] :
    ‖spatialSign (densityMatrix (maximallyMixed D))‖ = 1 / (Fintype.card D : ℝ) := by
  rw [spatialSign_maximallyMixed, maximallyMixed_matrix, norm_smul, norm_one, mul_one]
  simp

end SubentropyCertificates.ConditionalContinuity
