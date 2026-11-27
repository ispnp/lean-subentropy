module
public import SubentropyCertificates.KernelStrongConvexity
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Integration of the pointwise curvature and the corrected concave
spectral functional. The diagonal result also applies directly to posteriors. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set Filter
open scoped BigOperators
namespace SubentropyCertificates.StrongConcavity
open SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
variable {D J : Type*} [Fintype D] [DecidableEq D] [Fintype J]

private def K (p : D → ℝ) := subentropyKernel (diagonal (fun i => (p i:ℂ)))
private def density (d : ℕ) (s : ℝ) := s⁻¹^2 * Real.exp (-(rate d*s⁻¹))

private theorem density_integral {d : ℕ} (hd : 2 ≤ d) :
    IntegrableOn (density d) (Ioi 0) ∧ (∫ s in Ioi (0:ℝ), density d s) = mu d := by
  let g (t : ℝ) := Real.exp (-(rate d*t))
  have hneg : -rate d < 0 := neg_lt_zero.mpr (rate_pos hd)
  have hi : IntegrableOn g (Ioi 0) := by
    simpa [g,neg_mul] using integrableOn_exp_mul_Ioi (a := -rate d) hneg 0
  have hv : (∫ t in Ioi (0:ℝ), g t) = mu d := by
    simpa [g,neg_mul,neg_div,one_div,inv_rate hd] using integral_exp_mul_Ioi (a := -rate d) hneg 0
  have he (s : ℝ) (hs : s ∈ Ioi (0:ℝ)) :
      (|(-1:ℝ)| * s^((-1:ℝ)-1)) • g (s^(-1:ℝ)) = density d s := by
    rw [show (-1:ℝ)-1 = -2 by norm_num,Real.rpow_neg hs.le,Real.rpow_two,Real.rpow_neg_one]
    simp [g,density]
  refine ⟨((integrableOn_Ioi_comp_rpow_iff g (p := -1) (by norm_num)).mpr hi).congr_fun he
    measurableSet_Ioi,?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi he,integral_comp_rpow_Ioi g (by norm_num : (-1:ℝ) ≠ 0)]
  exact hv

private theorem kernel_laplace {p : D → ℝ} (hp : p ∈ probabilitySimplex D) {s : ℝ} (hs : 0 < s) :
    K p s = s/(1+s)-laplace s⁻¹ p := by
  rw [K,kernel_diagonal _ _ hs.ne',laplace,Real.exp_neg,Real.exp_sum,← Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hden : 0 < 1+s⁻¹*p i := by have := hp.1 i; positivity
  rw [Real.exp_log hden,show 1+s⁻¹*p i = (s+p i)/s by field_simp]
  simp

theorem classical_chord (hd : 2 ≤ Fintype.card D) {p q : D → ℝ}
    (hp : p ∈ probabilitySimplex D) (hq : q ∈ probabilitySimplex D)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a*classicalSubentropy p+b*classicalSubentropy q +
      mu (Fintype.card D)/2*a*b*energy (q-p) ≤ classicalSubentropy (a • p+b • q) := by
  let r := a • p+b • q
  have hr : r ∈ probabilitySimplex D := simplex_convex D hp hq ha hb hab
  have hK {v : D → ℝ} (hv : v ∈ probabilitySimplex D) : IntegrableOn (K v) (Ioi 0) :=
    integrable_subentropy_kernel (diagonal_density hv).1 (diagonal_density hv).2
  obtain ⟨hi,hv⟩ := density_integral hd
  let c := a*b/2*energy (q-p)
  have hpoint : ∀ᵐ s ∂volume.restrict (Ioi (0:ℝ)),
      a*K p s+b*K q s+c*density (Fintype.card D) s ≤ K r s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [kernel_laplace hp hs,kernel_laplace hq hs,kernel_laplace hr hs]
    have h := laplace_chord hd (inv_nonneg.mpr hs.le) hp hq ha hb hab
    have hconst := congrArg (fun x : ℝ => x*(s/(1+s))) hab
    change _ + c*density (Fintype.card D) s ≤ _ at h
    change _ ≤ s/(1+s)-laplace s⁻¹ (a • p+b • q)
    linarith
  have H := integral_mono_ae (((hK hp).const_mul a |>.add ((hK hq).const_mul b)).add (hi.const_mul c))
    (hK hr) hpoint
  have hsum : IntegrableOn (fun x => a*K p x+b*K q x) (Ioi 0) := ((hK hp).const_mul a).add ((hK hq).const_mul b)
  change (∫ x in Ioi (0:ℝ), a*K p x+b*K q x+c*density (Fintype.card D) x) ≤ _ at H
  rw [integral_add hsum (hi.const_mul c),
    integral_add ((hK hp).const_mul a) ((hK hq).const_mul b),integral_const_mul,integral_const_mul,
    integral_const_mul,hv] at H
  change a*classicalSubentropy p+b*classicalSubentropy q+c*mu (Fintype.card D) ≤ classicalSubentropy r at H
  dsimp only [c,r] at H
  linarith

def corrected (p : D → ℝ) := classicalSubentropy p + mu (Fintype.card D)/2*energy p

theorem corrected_concave (hd : 2 ≤ Fintype.card D) :
    ConcaveOn ℝ (probabilitySimplex D) corrected := by
  refine ⟨simplex_convex D,?_⟩
  intro p hp q hq a b ha hb hab
  have h := classical_chord hd hp hq ha hb hab
  have hid : energy (a • p+b • q) + a*b*energy (q-p) = a*energy p+b*energy q := by
    unfold energy
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    linear_combination (a*(p i)^2+b*(q i)^2)*hab
  simp only [corrected,smul_eq_mul]
  linarith only [h,congrArg (fun x => mu (Fintype.card D)/2*x) hid]

theorem corrected_perm (p : D → ℝ) (σ : Equiv.Perm D) : corrected (p ∘ σ) = corrected p := by
  unfold corrected
  rw [classical_subentropy_reindex]
  have h : energy (p ∘ σ) = energy p := Equiv.sum_comp σ (fun i => p i^2)
  rw [h]

end SubentropyCertificates.StrongConcavity
