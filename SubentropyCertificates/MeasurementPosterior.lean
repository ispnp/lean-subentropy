module

public import SubentropyCertificates.PinchingUpper

/-!
# Comparison with measurement posteriors

The outcome type is independent of the signal-label type. Zero-probability
outcomes are excluded from posterior averages explicitly. The supporting
pinching lemmas retain their upstream attribution; the comparison is proved
here using normalized positive Gram pieces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra

namespace SubentropyCertificates.MeasurementPosterior

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.PinchingGap

variable {X B Y : Type*} [Fintype X]
  [Fintype B] [Fintype Y]

def mass (G : Matrix (X × B) (X × B) ℂ) : ℝ := G.trace.re

def labelMass (G : Matrix (X × B) (X × B) ℂ) (x : X) : ℝ :=
  (∑ b, G (x,b) (x,b)).re

def labelPosterior (G : Matrix (X × B) (X × B) ℂ) (x : X) : ℝ :=
  labelMass G x / mass G

theorem psd_trace_eq_real_mass (G : Matrix (X × B) (X × B) ℂ)
    (hG : G.PosSemidef) : G.trace = (mass G : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (RCLike.nonneg_iff.mp hG.trace_nonneg).2

theorem mass_nonneg (G : Matrix (X × B) (X × B) ℂ) (hG : G.PosSemidef) :
    0 ≤ mass G := (RCLike.nonneg_iff.mp hG.trace_nonneg).1

theorem psd_eq_zero_of_mass_zero (G : Matrix (X × B) (X × B) ℂ)
    (hG : G.PosSemidef) (hz : mass G = 0) : G = 0 := by
  apply hG.trace_eq_zero_iff.mp
  rw [psd_trace_eq_real_mass G hG, hz]
  rfl

omit [Fintype X] in
theorem labelMass_nonneg (G : Matrix (X × B) (X × B) ℂ)
    (hG : G.PosSemidef) (x : X) : 0 ≤ labelMass G x := by
  unfold labelMass
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun b _ => (RCLike.nonneg_iff.mp (hG.diag_nonneg (i := (x,b)))).1

theorem sum_labelMass (G : Matrix (X × B) (X × B) ℂ) :
    ∑ x, labelMass G x = mass G := by
  simp only [labelMass, mass, Matrix.trace, Matrix.diag_apply,
    Fintype.sum_prod_type, Complex.re_sum]

theorem labelPosterior_probability (G : Matrix (X × B) (X × B) ℂ)
    (hG : G.PosSemidef) (hpos : 0 < mass G) :
    (∀ x, 0 ≤ labelPosterior G x) ∧ ∑ x, labelPosterior G x = 1 := by
  refine ⟨fun x => div_nonneg (labelMass_nonneg G hG x) hpos.le, ?_⟩
  simp only [labelPosterior, ← Finset.sum_div, sum_labelMass, div_self (ne_of_gt hpos)]

omit [Fintype X] in
theorem labelMass_smul (a : ℝ) (G : Matrix (X × B) (X × B) ℂ) (x : X) :
    labelMass (a • G) x = a * labelMass G x := by
  unfold labelMass
  simp only [Matrix.smul_apply, Complex.re_sum]
  simp only [Complex.smul_re, smul_eq_mul, Finset.mul_sum]

variable [DecidableEq X] [DecidableEq B]

/-- A finite positive Gram decomposition gives an average of classical posteriors. -/
theorem pinching_gap_le_outcome_average
    (G : Y → Matrix (X × B) (X × B) ℂ) (hG : ∀ y, (G y).PosSemidef)
    (htr : (∑ y, G y).trace = 1) (x₀ : X) (i₀ : X × B) :
    matrixSubentropy (blockPinch (∑ y, G y)) - matrixSubentropy (∑ y, G y) ≤
      ∑ y ∈ Finset.univ.filter (fun y => 0 < mass (G y)),
        mass (G y) * matrixSubentropy (diagonal (fun x => (labelPosterior (G y) x : ℂ))) := by
  let T := ∑ y, G y
  have hT : T.PosSemidef := by
    exact Matrix.posSemidef_sum Finset.univ (fun y _ => hG y)
  let r : Y → ℝ := fun y => mass (G y)
  have hr (y : Y) : 0 ≤ r y := mass_nonneg (G y) (hG y)
  have hrs : ∑ y, r y = 1 := by
    simp only [r, mass, ← Complex.re_sum, ← Matrix.trace_sum, htr, Complex.one_re]
  let H : Y → Matrix (X × B) (X × B) ℂ := fun y =>
    if r y = 0 then T else (r y)⁻¹ • G y
  have hH (y : Y) : (H y).PosSemidef ∧ (H y).trace = 1 := by
    by_cases hz : r y = 0
    · simpa only [H, ite_eq_left hz] using And.intro hT htr
    · simp only [H, ite_eq_right hz]
      refine ⟨(hG y).smul (inv_nonneg.mpr (hr y)), ?_⟩
      rw [Matrix.trace_smul, psd_trace_eq_real_mass (G y) (hG y)]
      change (r y)⁻¹ • (r y : ℂ) = 1
      simp [hz]
  have hpiece (y : Y) : r y • H y = G y := by
    by_cases hz : r y = 0
    · have hzero := psd_eq_zero_of_mass_zero (G y) (hG y) hz
      simp only [hz, zero_smul, hzero]
    · simp only [H, ite_eq_right hz, smul_smul, mul_inv_cancel₀ hz, one_smul]
  have htotal : (∑ y, r y • H y) = T := by
    exact Finset.sum_congr rfl (fun y _ => hpiece y)
  have hj := (actual_pinching_gap_laws i₀).1.map_sum_le
    (t := Finset.univ) (w := r) (p := H) (fun y _ => hr y) hrs (fun y _ => hH y)
  change matrixSubentropy (blockPinch (∑ y, r y • H y)) -
    matrixSubentropy (∑ y, r y • H y) ≤
    ∑ y, r y * (matrixSubentropy (blockPinch (H y)) - matrixSubentropy (H y)) at hj
  rw [htotal] at hj
  have hupper (y : Y) : r y * (matrixSubentropy (blockPinch (H y)) -
      matrixSubentropy (H y)) ≤ r y * matrixSubentropy
      (diagonal (fun x => (labelPosterior (G y) x : ℂ))) := by
    by_cases hz : r y = 0
    · simp only [hz, zero_mul, le_refl]
    · have hlabels (x : X) : labelMass (H y) x = labelPosterior (G y) x := by
        rw [show H y = (r y)⁻¹ • G y from ite_eq_right hz, labelMass_smul]
        simp only [labelPosterior, r, div_eq_mul_inv]
        ring
      have hu := pinching_gap_le_label_subentropy (H y) (hH y).1 (hH y).2 x₀ i₀
      change _ ≤ matrixSubentropy (diagonal (fun x => (labelMass (H y) x : ℂ))) at hu
      simp_rw [hlabels] at hu
      exact mul_le_mul_of_nonneg_left hu (hr y)
  have hfilter : (∑ y, r y * matrixSubentropy
      (diagonal (fun x => (labelPosterior (G y) x : ℂ)))) =
      ∑ y ∈ Finset.univ.filter (fun y => 0 < mass (G y)),
        mass (G y) * matrixSubentropy (diagonal (fun x => (labelPosterior (G y) x : ℂ))) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hpos : 0 < r y
    · simp only [r] at hpos ⊢
      simp only [hpos, ite_true]
    · have hz : r y = 0 := by linarith [hr y]
      simp only [show ¬ 0 < mass (G y) from hpos, ite_false, hz, zero_mul]
  calc
    _ ≤ ∑ y, r y * (matrixSubentropy (blockPinch (H y)) - matrixSubentropy (H y)) := hj
    _ ≤ ∑ y, r y * matrixSubentropy
        (diagonal (fun x => (labelPosterior (G y) x : ℂ))) :=
      Finset.sum_le_sum (fun y _ => hupper y)
    _ = _ := hfilter

end SubentropyCertificates.MeasurementPosterior
