module

public import SubentropyCertificates.ClassicalCurve

/-! Strict concavity from the original determinant kernel, including zero weights. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators

namespace SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel

theorem inverse_product_exp {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) {t : ℝ} (ht : 0 < t) :
    (∏ i, (t + p i)⁻¹) = Real.exp (-(∑ i, Real.log (t + p i))) := by
  rw [Real.exp_neg, Real.exp_sum, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.exp_log (add_pos_of_pos_of_nonneg ht (hp i))]

theorem inverse_product_strict {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpq : p ≠ q) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    {t : ℝ} (ht : 0 < t) :
    (∏ i, (t + (a * p i + b * q i))⁻¹) <
      a * (∏ i, (t + p i)⁻¹) + b * (∏ i, (t + q i)⁻¹) := by
  classical
  have hmix (i : ι) : 0 ≤ a * p i + b * q i :=
    add_nonneg (mul_nonneg ha.le (hp i)) (mul_nonneg hb.le (hq i))
  have hcoord (i : ι) : a * Real.log (t + p i) + b * Real.log (t + q i) ≤
      Real.log (t + (a * p i + b * q i)) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.2
      (show 0 < t + p i by linarith [hp i])
      (show 0 < t + q i by linarith [hq i]) ha.le hb.le hab
    have heq : a * (t + p i) + b * (t + q i) = t + (a * p i + b * q i) := by
      nlinarith
    simpa only [smul_eq_mul, heq] using h
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ q j := by
    by_contra h
    push Not at h
    exact hpq (funext h)
  have hjlt : a * Real.log (t + p j) + b * Real.log (t + q j) <
      Real.log (t + (a * p j + b * q j)) := by
    have h := strictConcaveOn_log_Ioi.2
      (show 0 < t + p j by linarith [hp j])
      (show 0 < t + q j by linarith [hq j])
      (show t + p j ≠ t + q j by exact fun h => hj (by linarith)) ha hb hab
    have heq : a * (t + p j) + b * (t + q j) = t + (a * p j + b * q j) := by
      nlinarith
    simpa only [smul_eq_mul, heq] using h
  have hsum := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hcoord i)
    ⟨j, Finset.mem_univ j, hjlt⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [inverse_product_exp _ hmix ht, inverse_product_exp _ hp ht,
    inverse_product_exp _ hq ht]
  calc
    _ < Real.exp (a * (-(∑ i, Real.log (t + p i))) +
        b * (-(∑ i, Real.log (t + q i)))) := by
      apply Real.exp_lt_exp.mpr
      linarith
    _ ≤ _ := convexOn_exp.2 (mem_univ _) (mem_univ _) ha.le hb.le hab

theorem classical_kernel_strict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpq : p ≠ q) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    {t : ℝ} (ht : 0 < t) :
    a * subentropyKernel (diagonal (fun i => (p i : ℂ))) t +
      b * subentropyKernel (diagonal (fun i => (q i : ℂ))) t <
      subentropyKernel (diagonal (fun i => ((a * p i + b * q i : ℝ) : ℂ))) t := by
  simp only [kernel_diagonal _ t ht.ne', div_eq_mul_inv,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have h := mul_lt_mul_of_pos_left (inverse_product_strict p q hp hq hpq a b ha hb hab ht)
    (pow_pos ht (Fintype.card ι))
  have hc := congrArg (fun r : ℝ => r * (t * (1 + t)⁻¹)) hab
  nlinarith only [h, hc]

theorem integral_strict_mono_Ioi {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0))
    (hfg : ∀ t ∈ Ioi (0 : ℝ), f t < g t) :
    (∫ t in Ioi (0 : ℝ), f t) < ∫ t in Ioi (0 : ℝ), g t := by
  have hlt : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), f t < g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hfg t ht
  have hle := hlt.mono (fun _ h => h.le)
  apply lt_of_le_of_ne (integral_mono_ae hf hg hle)
  intro heq
  have he := (integral_eq_iff_of_ae_le hf hg hle).mp heq
  have hfalse : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), False := by
    filter_upwards [hlt, he] with t ht heq
    exact ht.ne heq
  have hz : volume.restrict (Ioi (0 : ℝ)) = 0 := by
    simpa only [Filter.eventually_false_iff_eq_bot, ae_eq_bot] using hfalse
  have hm := congrArg (fun μ : Measure ℝ => μ (Ioc 1 2)) hz
  have hset : Ioc (1 : ℝ) 2 ∩ Ioi 0 = Ioc 1 2 := by
    ext x
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, lt_trans zero_lt_one h.1⟩
  norm_num [Measure.restrict_apply, measurableSet_Ioc, hset] at hm

theorem classical_subentropy_strictConcave {ι : Type*} [Fintype ι] [DecidableEq ι] :
    StrictConcaveOn ℝ (probabilitySimplex ι) classicalSubentropy := by
  refine ⟨simplex_convex ι, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  have hmix := simplex_convex ι hp hq ha.le hb.le hab
  have hdP := diagonal_density hp
  have hdQ := diagonal_density hq
  have hdM := diagonal_density hmix
  have h := integral_strict_mono_Ioi
    (((integrable_subentropy_kernel hdP.1 hdP.2).const_mul a).add
      ((integrable_subentropy_kernel hdQ.1 hdQ.2).const_mul b))
    (integrable_subentropy_kernel hdM.1 hdM.2)
    (fun t ht => classical_kernel_strict p q hp.1 hq.1 hpq a b ha hb hab ht)
  simp only [Pi.add_apply] at h
  rw [integral_add ((integrable_subentropy_kernel hdP.1 hdP.2).const_mul a)
    ((integrable_subentropy_kernel hdQ.1 hdQ.2).const_mul b),
    integral_const_mul, integral_const_mul] at h
  exact h

theorem phi_strictConcave (m : ℕ) : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (phi m) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro u hu v hv huv a b ha hb hab
  have hne : extremalVector m u ≠ extremalVector m v := by
    intro he
    have hn := congrFun he none
    simp only [extremalVector] at hn
    exact huv (by linarith)
  have h := classical_subentropy_strictConcave.2
    (extremal_probability m hu) (extremal_probability m hv) hne ha hb hab
  simpa only [phi, smul_eq_mul, ← extremal_affine m u v a b hab] using h

end SubentropyCertificates.ClassicalCurve
