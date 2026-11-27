module

public import SubentropyCertificates.CounterexampleState
public import SubentropyCertificates.CounterexampleIntegral

/-! Shifted determinants of the actual joint density and its partial traces. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators
namespace SubentropyCertificates.QuantumCounterexample
open D5.S3.Quantum.Foundation.FiniteStateChannel


private theorem det_mixture {D : Type*} [Fintype D] [DecidableEq D]
    (V : Matrix D Bit ℂ) (t : ℝ) :
    (1 + t • mixture V).det = (1 + (t*(1/10 : ℝ)) • (V.conjTranspose*V)).det := by
  simpa only [mixture, smul_smul, Matrix.mul_smul, Matrix.smul_mul] using
    Matrix.det_one_add_mul_comm ((t*(1/10 : ℝ)) • V) V.conjTranspose

private theorem det_diag {D : Type*} [Fintype D] [DecidableEq D] (w : D → ℝ) (t : ℝ) :
    (1 + t • diagonal (fun i => (w i : ℂ))).det = ↑(∏ i, (1+t*w i)) := by
  have h : (1 : Matrix D D ℂ) + t • diagonal (fun i => (w i : ℂ)) =
      diagonal (fun i => ((1+t*w i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp [Complex.real_smul]
    · simp [hij]
  rw [h, Matrix.det_diagonal, Complex.ofReal_prod]

def shiftDet {D : Type*} [Fintype D] [DecidableEq D] (ρ : DensityState D) (t : ℝ) : ℂ :=
  (1 + t • (CStarMatrix.ofMatrix.symm ρ.1)).det

/-- Polynomial identities hold for every real t, including zero. -/
theorem witness_determinants (t : ℝ) :
    shiftDet state t = (d0 t : ℂ) ∧ shiftDet stateB t = (d0 t : ℂ) ∧
    shiftDet stateAB t = (d1 t : ℂ) ∧ shiftDet stateBC t = (d2 t : ℂ) := by
  obtain ⟨hab,hb,hbc⟩ := marginal_matrices
  obtain ⟨hX,hY⟩ := signal_grams
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (1 + t • mixture labelled).det = _
    rw [det_mixture, hX]
    change (1 + _ • diagonal (fun _ : Bit => ((5 : ℝ) : ℂ))).det = _
    rw [det_diag]
    apply congrArg Complex.ofReal
    simp only [Fin.prod_univ_two, d0]
    ring
  · unfold shiftDet
    rw [hb]
    rw [← show ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) by norm_num]
    rw [det_diag]
    apply congrArg Complex.ofReal
    simp only [Fin.prod_univ_two, d0]
    ring
  · unfold shiftDet
    rw [hab, det_diag]
    apply congrArg Complex.ofReal
    simp [Fintype.prod_prod_type, Fin.prod_univ_two, abWeight, d1]
    ring
  · unfold shiftDet
    rw [hbc, det_mixture, hY, Matrix.det_fin_two]
    norm_num [Matrix.one_apply, Complex.real_smul, d2]
    ring

def determinantGap (t : ℝ) :=
  (shiftDet stateB t).re⁻¹ + (shiftDet state t).re⁻¹ -
  (shiftDet stateAB t).re⁻¹ - (shiftDet stateBC t).re⁻¹

theorem determinant_gap_eq (t : ℝ) : determinantGap t = gap t := by
  obtain ⟨h,hb,hab,hbc⟩ := witness_determinants t
  simp only [determinantGap,h,hb,hab,hbc,Complex.ofReal_re,gap,div_eq_mul_inv]
  ring

end SubentropyCertificates.QuantumCounterexample
