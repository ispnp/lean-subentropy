module

public import SubentropyCertificates.GaussianGradientDefs

/-! Joint law of the squared magnitudes of a circular complex Gaussian. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators

namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations
open D5.S3.Quantum.Subentropy.GaussianQuadratic

private abbrev normalPair := Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 1)

private def pairSquare (a : Fin 2 → ℝ) := (a 0 ^ 2 + a 1 ^ 2) / 2

private theorem pairSquare_map : normalPair.map pairSquare = expMeasure 1 := by
  have m : Measurable pairSquare := by unfold pairSquare; fun_prop
  let e := MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)
  have pe := measurePreserving_piFinTwo (fun _ : Fin 2 ↦ gaussianReal 0 1)
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have : IsProbabilityMeasure (normalPair.map pairSquare) := (Measure.isProbabilityMeasure_map_iff m.aemeasurable).mpr inferInstance
  ext s hs
  apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _) |>.mp
  let f := s.indicator (fun _ : ℝ ↦ (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hs
  have ht (μ : Measure ℝ) [IsProbabilityMeasure μ] : ∫ u, f u ∂μ = (μ s).toReal := by
    simp [f, integral_indicator hs, measureReal_def]
  rw [← ht, ← ht, integral_map m.aemeasurable hf.aestronglyMeasurable]
  have eq := (gaussian_pair_integral f).trans (unit_exponential_integral f).symm
  rw [← pe.integral_comp' (fun p : ℝ × ℝ ↦ f ((p.1 ^ 2 + p.2 ^ 2) / 2))] at eq
  exact eq

private theorem gaussian_uncurry (D : Type*) [Fintype D] :
    (Measure.pi (fun _ : D ↦ normalPair)).map (fun z (p : D × Fin 2) ↦ z p.1 p.2) =
      Measure.pi (fun _ ↦ gaussianReal 0 1) := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.map_apply (by fun_prop) (.univ_pi hs)]
  have he : (fun (z : D → Fin 2 → ℝ) (p : D × Fin 2) ↦ z p.1 p.2) ⁻¹' univ.pi s =
      univ.pi (fun i ↦ univ.pi (fun j ↦ s (i,j))) := by
    ext z
    simp [mem_pi, Prod.forall]
  rw [he, Measure.pi_pi, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl (fun _ _ ↦ Measure.pi_pi _ _)

/-- The entire squared-radius vector has product unit exponential law. -/
theorem circular_radii_map (D : Type*) [Fintype D] :
    (circularGaussian D).map (fun g i ↦ Complex.normSq (g i)) =
      Measure.pi (fun _ : D ↦ expMeasure 1) := by
  classical
  let c := complexGaussianCoordinates (ι := D)
  have hc : Measurable c := by
    unfold c complexGaussianCoordinates
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  have hn : Measurable (normalizeGaussian (D := D)) := by unfold normalizeGaussian; fun_prop
  have hr : Measurable (fun (g : V D) i ↦ Complex.normSq (g i)) := by fun_prop
  have hp : Measurable pairSquare := by unfold pairSquare; fun_prop
  have : IsProbabilityMeasure (normalPair.map pairSquare) := (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  rw [circularGaussian, ← complex_coordinate_transport.1, ← gaussian_uncurry D,
    Measure.map_map hc (by fun_prop), Measure.map_map hn (by fun_prop), Measure.map_map hr (by fun_prop)]
  have he (z : D → Fin 2 → ℝ) (i : D) :
      Complex.normSq (normalizeGaussian (c (fun p ↦ z p.1 p.2)) i) = pairSquare (z i) := by
    change Complex.normSq (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * (c (fun p ↦ z p.1 p.2) i)) = _
    rw [Complex.normSq_mul, Complex.normSq_ofReal, ← sq, inv_pow, Real.sq_sqrt (by norm_num),
      complex_coordinate_transport.2]
    unfold pairSquare
    ring
  change (Measure.pi (fun _ : D ↦ normalPair)).map
    (fun z i ↦ Complex.normSq (normalizeGaussian (c (fun p ↦ z p.1 p.2)) i)) = _
  simp_rw [he]
  rw [Measure.pi_map_pi (fun _ ↦ hp.aemeasurable)]
  simp only [pairSquare_map]

end SubentropyCertificates.ConditionalContinuity
