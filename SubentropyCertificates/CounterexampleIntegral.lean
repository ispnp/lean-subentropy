module

public import D5.S3.Quantum.Subentropy.UniformIntegrals

/-! Exact rational and logarithmic calculations for the three-qubit witness.
The determinant variable is t; the library integrates in s = 1/t. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace SubentropyCertificates.QuantumCounterexample
open D5.S3.Quantum.Subentropy.UniformIntegrals

def d0 (t : ℝ) := (1+t/2)^2
def d1 (t : ℝ) := (1+2*t/5)^2 * (1+t/10)^2
def d2 (t : ℝ) := (1+9*t/10)*(1+t/10)
def gap (t : ℝ) := 2/d0 t - 1/d1 t - 1/d2 t
def exactDeficit : ℝ := 2*Real.log 5 - 256/135*Real.log 2 - 81/40*Real.log 3 + 5/18

theorem gap_formula {t : ℝ} (ht : 0 < t) :
    gap t = -(t^2*(5000+2500*t+250*t^2+75*t^3+7*t^4)) /
      (62500*d0 t*d1 t*d2 t) ∧ gap t < 0 := by
  have he : gap t = -(t^2*(5000+2500*t+250*t^2+75*t^3+7*t^4)) /
      (62500*d0 t*d1 t*d2 t) := by
    unfold gap
    have h0 : 0 < d0 t := by unfold d0; positivity
    have h1 : 0 < d1 t := by unfold d1; positivity
    have h2 : 0 < d2 t := by unfold d2; positivity
    field_simp [h0.ne', h1.ne', h2.ne']
    unfold d0 d1 d2
    ring
  refine ⟨he, ?_⟩
  rw [he]
  unfold d0 d1 d2
  apply div_neg_of_neg_of_pos <;> first | positivity | exact neg_lt_zero.mpr (by positivity)

private def diff (a b s : ℝ) := 1/(s+a) - 1/(s+b)
private def sqInv (a s : ℝ) := 1/(s+a)^2

private def Evaluates (f : ℝ → ℝ) (v : ℝ) :=
  IntegrableOn f (Ioi 0) ∧ (∫ s in Ioi (0 : ℝ), f s) = v

private theorem eval_add {f g : ℝ → ℝ} {a b : ℝ} (hf : Evaluates f a) (hg : Evaluates g b) :
    Evaluates (fun s => f s + g s) (a+b) :=
  ⟨hf.1.add hg.1, (integral_add hf.1 hg.1).trans (congrArg₂ (· + ·) hf.2 hg.2)⟩

private theorem eval_scale {f : ℝ → ℝ} {a : ℝ} (c : ℝ) (hf : Evaluates f a) :
    Evaluates (fun s => c*f s) (c*a) :=
  ⟨hf.1.const_mul c, (integral_const_mul c f).trans (congrArg (c * ·) hf.2)⟩

private theorem eval_diff (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Evaluates (diff a b) (Real.log b - Real.log a) := reciprocal_difference a b ha hab

private theorem eval_sq (a : ℝ) (ha : 0 < a) : Evaluates (sqInv a) (1/a) := by
  change IntegrableOn (fun s : ℝ => 1/(s+a)^2) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), 1/(s+a)^2) = 1/a
  simpa using inverse_power a ha 0

private def expansion (s : ℝ) :=
  17/432*diff (1/10) (1/2) s + 128/135*diff (2/5) (1/2) s +
  (-81/80)*diff (1/2) (9/10) s + (-1/900)*sqInv (1/10) s +
  (-64/225)*sqInv (2/5) s + 1/2*sqInv (1/2) s

private theorem partial_fractions {s : ℝ} (hs : 0 < s) : gap s⁻¹ = expansion s := by
  have shift (a : ℝ) : 1 + a*s⁻¹ = (s+a)/s := by field_simp
  have repl (a b : ℝ) : a*s⁻¹/b = (a/b)*s⁻¹ := by ring
  unfold gap d0 d1 d2 expansion diff sqInv
  rw [show s⁻¹/2 = (1/2)*s⁻¹ by ring, show s⁻¹/10 = (1/10)*s⁻¹ by ring,
    repl 2 5, repl 9 10]
  simp only [shift, div_pow, div_div_eq_mul_div, mul_div_assoc']
  have h1 : 0 < s+1/10 := by linarith
  have h2 : 0 < s+2/5 := by linarith
  have h5 : 0 < s+1/2 := by linarith
  have h9 : 0 < s+9/10 := by linarith
  field_simp [hs.ne',h1.ne',h2.ne',h5.ne',h9.ne']
  ring

/-- Improper integral of the signed reciprocal determinant combination at 1/s. -/
theorem gap_integral :
    IntegrableOn (fun s : ℝ => gap s⁻¹) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), gap s⁻¹) = exactDeficit := by
  have he := eval_add (eval_add (eval_add (eval_add
    (eval_add (eval_scale (17/432) (eval_diff (1/10) (1/2) (by norm_num) (by norm_num)))
      (eval_scale (128/135) (eval_diff (2/5) (1/2) (by norm_num) (by norm_num))))
    (eval_scale (-81/80) (eval_diff (1/2) (9/10) (by norm_num) (by norm_num))))
    (eval_scale (-1/900) (eval_sq (1/10) (by norm_num))))
    (eval_scale (-64/225) (eval_sq (2/5) (by norm_num))))
    (eval_scale (1/2) (eval_sq (1/2) (by norm_num)))
  have hid (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : gap s⁻¹ = expansion s := partial_fractions hs
  refine ⟨he.1.congr_fun (fun s hs => (hid s hs).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hid]
  change (∫ s in Ioi (0 : ℝ), expansion s) = _
  rw [show (∫ s in Ioi (0 : ℝ), expansion s) = _ from he.2]
  have l10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l9 : Real.log 9 = 2*Real.log 3 := by
    rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]; norm_num
  unfold exactDeficit
  rw [Real.log_div (by norm_num) (by norm_num) (x := 1) (y := 2),
      Real.log_div (by norm_num) (by norm_num) (x := 1) (y := 10),
      Real.log_div (by norm_num) (by norm_num) (x := 2) (y := 5),
      Real.log_div (by norm_num) (by norm_num) (x := 9) (y := 10), Real.log_one, l10, l9]
  ring

end SubentropyCertificates.QuantumCounterexample
