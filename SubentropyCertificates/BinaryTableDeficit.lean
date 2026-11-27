module

public import SubentropyCertificates.FourCellDeficit
public import SubentropyCertificates.ClassicalCurve
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Integration of the quantitative four-cell comparison. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped BigOperators
namespace SubentropyCertificates.QubitDeficit
open SubentropyCertificates.FourCell
open SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel

/-- In the library's integral variable s, the exponential lower bound
has density (1/s)^2 exp(-3/s). Substitute t = 1/s. -/
private theorem reciprocal_exponential :
    let f := fun s : ℝ => s⁻¹^2 * Real.exp (-(3*s⁻¹))
    IntegrableOn f (Ioi 0) ∧ (∫ s in Ioi 0, f s) = 1/3 := by
  let g := fun t : ℝ => Real.exp (-(3*t))
  have hi : IntegrableOn g (Ioi 0) := by
    simpa [g, neg_mul] using integrableOn_exp_mul_Ioi (a := (-3 : ℝ)) (by norm_num) 0
  have hv : (∫ t in Ioi 0, g t) = 1/3 := by
    simpa [g, neg_mul] using integral_exp_mul_Ioi (a := (-3 : ℝ)) (by norm_num) 0
  have he (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) • g (s ^ (-1 : ℝ)) =
      s⁻¹^2 * Real.exp (-(3*s⁻¹)) := by
    rw [show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num, Real.rpow_neg hs.le,
      Real.rpow_two, Real.rpow_neg_one]
    simp [g]
  refine ⟨((integrableOn_Ioi_comp_rpow_iff g (p := -1) (by norm_num)).mpr hi).congr_fun he
    measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi he, integral_comp_rpow_Ioi g (by norm_num : (-1 : ℝ) ≠ 0)]
  exact hv

/-- The determinant kernel in the variable used in the four-cell comparison. -/
private theorem kernel_reciprocal {D : Type*} [Fintype D] [DecidableEq D] (p : D → ℝ)
    {s : ℝ} (hs : 0 < s) :
    subentropyKernel (diagonal (fun i => (p i : ℂ))) s =
      1/(1+s⁻¹) - 1/(∏ i, (1+p i*s⁻¹)) := by
  rw [kernel_diagonal _ s hs.ne']
  have h (x : ℝ) : s / (s+x) = (1+x*s⁻¹)⁻¹ := by
    rw [show 1+x*s⁻¹ = (s+x)/s by field_simp]
    simp
  simp_rw [h]
  rw [Finset.prod_inv_distrib, one_div (∏ i, (1+p i*s⁻¹))]
  congr 1
  rw [add_comm (1 : ℝ) s, h 1, one_mul, one_div]

/-- Integrated estimate for an arbitrary probability table on two binary
indices. The two marginal sums are given explicitly. -/
theorem classical_two_by_two_deficit (p : Fin 2 × Fin 2 → ℝ)
    (hp : p ∈ probabilitySimplex _) :
    let r := fun i => ∑ j, p (i,j)
    let c := fun j => ∑ i, p (i,j)
    r 0 * r 1 * (c 0 * c 1) / 3 ≤ classicalSubentropy r + classicalSubentropy c -
      classicalSubentropy p := by
  dsimp only
  let r := fun i => ∑ j, p (i,j)
  let c := fun j => ∑ i, p (i,j)
  have hr : r ∈ probabilitySimplex _ := ⟨fun i => Finset.sum_nonneg (fun j _ => hp.1 (i,j)),
    (Fintype.sum_prod_type p).symm.trans hp.2⟩
  have hc : c ∈ probabilitySimplex _ := ⟨fun j => Finset.sum_nonneg (fun i _ => hp.1 (i,j)),
    (Finset.sum_comm).trans hr.2⟩
  let K {D : Type} [Fintype D] [DecidableEq D] (w : D → ℝ) :=
    subentropyKernel (diagonal (fun i => (w i : ℂ)))
  have hK {D : Type} [Fintype D] [DecidableEq D] {w : D → ℝ}
      (hw : w ∈ probabilitySimplex D) : IntegrableOn (K w) (Ioi 0) :=
    integrable_subentropy_kernel (diagonal_density hw).1 (diagonal_density hw).2
  let m := r 0 * r 1 * (c 0 * c 1)
  have hpoint (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      m * (s⁻¹^2 * Real.exp (-(3*s⁻¹))) ≤ K r s + K c s - K p s := by
    have hn := hp.2
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at hn
    have h := four_cell_exponential_bound (p (0,0)) (p (0,1)) (p (1,0)) (p (1,1)) s⁻¹
      (hp.1 _) (hp.1 _) (hp.1 _) (hp.1 _) (by linarith only [hn]) (inv_nonneg.mpr hs.le)
    dsimp only [K]
    rw [kernel_reciprocal r hs, kernel_reciprocal c hs, kernel_reciprocal p hs]
    simp only [m, r, c, Fintype.prod_prod_type, Fin.prod_univ_two, Fin.sum_univ_two]
    unfold U V rowKernel columnKernel cellKernel at h
    -- The cell product over pairs groups the four factors by row.
    rw [mul_assoc ((1+p (0,0)*s⁻¹)*(1+p (0,1)*s⁻¹))] at h
    linarith only [h]
  obtain ⟨hi, hv⟩ := reciprocal_exponential
  have h := setIntegral_mono_on (hi.const_mul m) (((hK hr).add (hK hc)).sub (hK hp))
    measurableSet_Ioi hpoint
  simp only [Pi.sub_apply, Pi.add_apply] at h
  rw [integral_const_mul, hv, integral_sub (f := fun s => K r s + K c s) ((hK hr).add (hK hc)) (hK hp),
    integral_add (hK hr) (hK hc)] at h
  change m / 3 ≤ (∫ s in Ioi (0 : ℝ), K r s) + (∫ s in Ioi (0 : ℝ), K c s) -
    ∫ s in Ioi (0 : ℝ), K p s
  simpa only [div_eq_mul_inv, one_mul] using h

end SubentropyCertificates.QubitDeficit
