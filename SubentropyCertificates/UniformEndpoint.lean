module

public import SubentropyCertificates.ClassicalCurve
public import Mathlib.NumberTheory.Harmonic.Defs

/-! Evaluation at the uniform spectrum in every finite dimension. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped BigOperators Topology

namespace SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.UniformIntegrals

def ratio (a t : ℝ) : ℝ := t / (t + a)

theorem ratio_limit (a : ℝ) : Tendsto (ratio a) atTop (𝓝 1) := by
  have hshift : Tendsto (fun t : ℝ => t + a) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b - a)] with t ht
    linarith
  have h : Tendsto (fun t : ℝ => 1 - a * (t + a)⁻¹) atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, sub_zero] using
      tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hshift))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (-a)] with t ht
  have hta : t + a ≠ 0 := by linarith
  dsimp [ratio]
  field_simp
  ring

theorem integral_ratio_power (a : ℝ) (ha : 0 < a) (n : ℕ) :
    IntegrableOn (fun t => (ratio a t)^n / (t + a)^2) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), (ratio a t)^n / (t + a)^2) =
        1 / (a * (n + 1 : ℕ)) := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt
      (fun t => (ratio a t)^(n + 1) / (a * (n + 1 : ℕ)))
      ((ratio a t)^n / (t + a)^2) t := by
    intro t ht
    have hta : t + a ≠ 0 := by linarith [ht.out]
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hr : HasDerivAt (ratio a) (a / (t + a)^2) t := by
      convert (hasDerivAt_id t).div ((hasDerivAt_id t).add_const a) hta using 1
      all_goals first | (funext x; rfl) | (dsimp; ring)
    convert (hr.pow (n + 1)).div_const (a * (n + 1 : ℕ)) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hp : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ (ratio a t)^n / (t + a)^2 := by
    intro t ht
    exact div_nonneg (pow_nonneg (div_nonneg ht.le (by linarith [ht.out])) _) (sq_nonneg _)
  have hl : Tendsto (fun t => (ratio a t)^(n + 1) / (a * (n + 1 : ℕ)))
      atTop (𝓝 (1 / (a * (n + 1 : ℕ)))) := by
    simpa only [one_pow] using ((ratio_limit a).pow (n + 1)).div_const (a * (n + 1 : ℕ))
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp hl, ?_⟩
  have hv := integral_Ioi_of_hasDerivAt_of_nonneg' hd hp hl
  simpa [ratio] using hv

def uniformCorrection (n : ℕ) (a t : ℝ) : ℝ :=
  (1 - (ratio a t)^n) / (t + a)

theorem uniformCorrection_succ (n : ℕ) (a t : ℝ) (hta : t + a ≠ 0) :
    uniformCorrection (n + 1) a t = uniformCorrection n a t +
      a * ((ratio a t)^n / (t + a)^2) := by
  simp only [uniformCorrection, ratio, pow_succ]
  field_simp
  ring

theorem integral_uniformCorrection (n : ℕ) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (uniformCorrection n a) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), uniformCorrection n a t) = (harmonic n : ℝ) := by
  induction n with
  | zero =>
    have hz : uniformCorrection 0 a = fun _ : ℝ => 0 := by
      funext t
      simp [uniformCorrection]
    rw [hz]
    simp
  | succ n ih =>
    have hi := integral_ratio_power a ha n
    have heq : uniformCorrection (n + 1) a =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun t => uniformCorrection n a t + a * ((ratio a t)^n / (t + a)^2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact uniformCorrection_succ n a t (by linarith [ht.out])
    refine ⟨(ih.1.add (hi.1.const_mul a)).congr heq.symm, ?_⟩
    rw [integral_congr_ae heq, integral_add ih.1 (hi.1.const_mul a),
      integral_const_mul, ih.2, hi.2, harmonic_succ]
    push_cast
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp

def scaledUniformKernel (n : ℕ) (a t : ℝ) : ℝ :=
  1 - (n : ℝ) * a / (t + 1) - (ratio a t)^n

theorem scaledUniformKernel_succ (n : ℕ) (a t : ℝ) (hta : t + a ≠ 0) :
    scaledUniformKernel (n + 1) a t = scaledUniformKernel n a t +
      a * (1 / (t + a) - 1 / (t + 1)) - a * uniformCorrection n a t := by
  simp only [scaledUniformKernel, uniformCorrection, ratio, pow_succ, Nat.cast_add,
    Nat.cast_one]
  field_simp
  ring

theorem integral_scaledUniformKernel (n : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    IntegrableOn (scaledUniformKernel n a) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), scaledUniformKernel n a t) =
        (n : ℝ) * a * (-Real.log a - (harmonic n : ℝ) + 1) := by
  induction n with
  | zero =>
    have hz : scaledUniformKernel 0 a = fun _ : ℝ => 0 := by
      funext t
      simp [scaledUniformKernel]
    rw [hz]
    simp
  | succ n ih =>
    have hi := reciprocal_difference a 1 ha ha1
    have hc := integral_uniformCorrection n a ha
    have heq : scaledUniformKernel (n + 1) a =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun t => scaledUniformKernel n a t +
          a * (1 / (t + a) - 1 / (t + 1)) - a * uniformCorrection n a t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact scaledUniformKernel_succ n a t (by linarith [ht.out])
    refine ⟨((ih.1.add (hi.1.const_mul a)).sub (hc.1.const_mul a)).congr heq.symm, ?_⟩
    have hia : IntegrableOn (fun t => scaledUniformKernel n a t +
        a * (1 / (t + a) - 1 / (t + 1))) (Ioi 0) := ih.1.add (hi.1.const_mul a)
    rw [integral_congr_ae heq, integral_sub hia
      (hc.1.const_mul a), integral_add ih.1 (hi.1.const_mul a),
      integral_const_mul, integral_const_mul, ih.2, hi.2, hc.2, harmonic_succ]
    simp only [Real.log_one, zero_sub]
    push_cast
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at hn
    field_simp
    ring

theorem classical_subentropy_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : 0 < Fintype.card ι) :
    classicalSubentropy (fun _ : ι => (1 : ℝ) / Fintype.card ι) =
      Real.log (Fintype.card ι) - (harmonic (Fintype.card ι) : ℝ) + 1 := by
  let n := Fintype.card ι
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have h := integral_scaledUniformKernel n (1 / n) (by positivity)
    (by exact (div_le_one hnR).mpr hn1)
  have heq : ∀ t ∈ Ioi (0 : ℝ),
      subentropyKernel (diagonal (fun _ : ι => ((1 / (n : ℝ) : ℝ) : ℂ))) t =
        scaledUniformKernel n (1 / n) t := by
    intro t ht
    rw [kernel_diagonal _ t ht.ne']
    simp only [Finset.prod_const, Finset.card_univ, scaledUniformKernel, ratio]
    have ht1 : t + 1 ≠ 0 := by linarith [ht.out]
    have ht2 : 1 + t ≠ 0 := by linarith [ht.out]
    field_simp
    ring
  unfold classicalSubentropy matrixSubentropy
  rw [setIntegral_congr_fun measurableSet_Ioi heq, h.2]
  rw [Real.log_div one_ne_zero hnR.ne', Real.log_one]
  field_simp
  simp [n]

theorem phi_uniform_endpoint (m : ℕ) :
    phi m (uniformError m) = Real.log (m + 2 : ℕ) - (harmonic (m + 2) : ℝ) + 1 := by
  rw [phi, extremal_uniform]
  simpa [Nat.add_assoc]
    using classical_subentropy_uniform (ι := Option (Fin (m + 1))) (by simp)

def zeroPad {ι : Type*} (p : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => p i

theorem classical_subentropy_zero_pad {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) : classicalSubentropy (zeroPad p) = classicalSubentropy p := by
  unfold classicalSubentropy matrixSubentropy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [kernel_diagonal _ t ht.ne', kernel_diagonal _ t ht.ne']
  simp only [Fintype.prod_option, zeroPad, add_zero, div_self ht.ne', one_mul]

theorem phi_one (m : ℕ) :
    phi m 1 = Real.log (m + 1 : ℕ) - (harmonic (m + 1) : ℝ) + 1 := by
  have hv : extremalVector m 1 = zeroPad (fun _ : Fin (m + 1) => (1 : ℝ) / (m + 1 : ℕ)) := by
    funext i
    cases i <;> simp only [extremalVector, zeroPad, sub_self]
  rw [phi, hv, classical_subentropy_zero_pad]
  simpa only [Fintype.card_fin] using classical_subentropy_uniform (ι := Fin (m + 1)) (by simp)

end SubentropyCertificates.ClassicalCurve
