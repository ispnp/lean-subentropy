module

public import SubentropyCertificates.GaussianSignBound
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! Differentiation of the Gaussian entropy functional on positive definite matrices. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology BigOperators ENNReal
namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.Representations

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
private theorem circular_probability : IsProbabilityMeasure (circularGaussian D) :=
  by unfold circularGaussian; infer_instance

omit [DecidableEq D] in
private theorem circular_pow (k : ℕ) (hk : k ≠ 0) :
    Integrable (fun g : V D ↦ ‖g‖ ^ k) (circularGaussian D) := by
  unfold circularGaussian
  rw [integrable_map_measure (by fun_prop) (by unfold normalizeGaussian; fun_prop)]
  have hh := (IsGaussian.memLp_id (stdGaussian (V D)) (k : ℝ≥0∞) (by simp)).integrable_norm_pow hk
  simpa [Function.comp_def, normalizeGaussian, norm_smul, mul_pow] using
    hh.const_mul (‖(Real.sqrt 2)⁻¹‖ ^ k)

private theorem quadratic_bound (A : Matrix D D ℂ) (g : V D) :
    |quadraticForm A g| ≤ ‖A‖ * ‖g‖ ^ 2 := by
  unfold quadraticForm
  calc
    _ ≤ _ := Complex.abs_re_le_norm _
    _ ≤ _ := norm_inner_le_norm _ _
    _ ≤ ‖g‖ * (‖A‖ * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := D) A).le_opNorm g
    _ = _ := by ring

private theorem quadratic_lower {M : Matrix D D ℂ} (hp : M.PosDef) :
    ∃ a : ℝ, 0 < a ∧ ∀ g : V D, a * ‖g‖ ^ 2 ≤ quadraticForm M g := by
  classical
  cases isEmpty_or_nonempty D with
  | inl he => exact ⟨1, one_pos, fun g ↦ by simp [Subsingleton.elim g 0, quadraticForm]⟩
  | inr he =>
    obtain ⟨a, ha, hl⟩ := (CFC.exists_pos_algebraMap_le_iff M).2
      (fun x hx ↦ hp.isStrictlyPositive.spectrum_pos hx)
    refine ⟨a, ha, fun g ↦ ?_⟩
    rw [Algebra.algebraMap_eq_smul_one] at hl
    have h := D5.S3.Quantum.Subentropy.GaussianQuadratic.quadratic_nonnegative
      (Matrix.le_iff.mp hl) g
    change 0 ≤ (inner ℂ g (Matrix.toEuclideanLin (M - (a:ℂ) • (1 : Matrix D D ℂ)) g)).re / 2 at h
    have hone : Matrix.toEuclideanLin (1 : Matrix D D ℂ) = LinearMap.id := Matrix.toLpLin_one _
    rw [map_sub, map_smul, hone, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_sub_right, inner_smul_right] at h
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h
    have hself : (inner ℂ g g).re = ‖g‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) g).symm
    rw [hself] at h
    unfold quadraticForm
    linarith only [h]

private theorem quadratic_line (M H : Matrix D D ℂ) (s : ℝ) (g : V D) :
    quadraticForm (M + s • H) g = quadraticForm M g + s * quadraticForm H g := by
  change (inner ℂ g ((Matrix.toEuclideanLin (M + s • H)) g)).re = _
  change (inner ℂ g (Matrix.toEuclideanLin (M + (s : ℂ) • H) g)).re = _
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_right,
    inner_smul_right]
  simp only [quadraticForm, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- A scalar bound uniform down to zero. The linear factor cancels the logarithmic singularity. -/
private theorem weighted_log_bound {t : ℝ} (ht : 0 ≤ t) :
    t * |Real.log t| ≤ 1 + t^2 := by
  rcases eq_or_lt_of_le ht with rfl | h
  · simp
  rcases le_total 1 t with h₁ | h₁
  · rw [abs_of_nonneg (Real.log_nonneg h₁)]
    nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) ht]
  · rw [abs_of_nonpos (Real.log_nonpos ht h₁)]
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr h)
    rw [Real.log_inv] at hi
    have := mul_le_mul_of_nonneg_left hi ht
    rw [mul_sub, mul_inv_cancel₀ h.ne', mul_one] at this
    nlinarith [sq_nonneg t]

private theorem line_bounds {M : Matrix D D ℂ} (hp : M.PosDef) (H : Matrix D D ℂ) :
    ∃ a b ε : ℝ, 0 < a ∧ 0 < b ∧ 0 < ε ∧ ∀ s : ℝ, |s| < ε → ∀ g : V D,
      a * ‖g‖^2 ≤ quadraticForm (M+s•H) g ∧ quadraticForm (M+s•H) g ≤ b * ‖g‖^2 := by
  obtain ⟨a, ha, hl⟩ := quadratic_lower hp
  let r := a / (2*(1+‖H‖))
  refine ⟨a/2, 1+‖M‖+‖H‖, min 1 r, by positivity, by positivity,
    lt_min one_pos (by dsimp [r]; positivity), ?_⟩
  intro s hs g
  have hs₁ := (lt_min_iff.mp hs).1
  have hs₂ := (lt_div_iff₀ (by positivity : 0 < 2*(1+‖H‖))).mp (lt_min_iff.mp hs).2
  have hsH : |s| * ‖H‖ ≤ a/2 := by nlinarith [abs_nonneg s]
  have hsH' : |s| * ‖H‖ ≤ ‖H‖ := by nlinarith [mul_le_mul_of_nonneg_right hs₁.le (norm_nonneg H)]
  have hterm : |s * quadraticForm H g| ≤ (|s| * ‖H‖)*‖g‖^2 := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (quadratic_bound H g) (abs_nonneg s)
  rw [quadratic_line]
  constructor
  · nlinarith only [hl g, neg_abs_le (s*quadraticForm H g), hterm,
      mul_le_mul_of_nonneg_right hsH (sq_nonneg ‖g‖)]
  · nlinarith only [le_abs_self (quadraticForm M g), quadratic_bound M g, le_abs_self
      (s*quadraticForm H g), hterm, mul_le_mul_of_nonneg_right hsH' (sq_nonneg ‖g‖),
      sq_nonneg ‖g‖]

private def envelope (a b : ℝ) (g : V D) : ℝ := ‖g‖^2 + (1+b^2*‖g‖^4)/a

omit [DecidableEq D] in
private theorem slope_bound {a b t : ℝ} (ha : 0 < a) (g : V D)
    (hl : a * ‖g‖^2 ≤ t) (hu : t ≤ b * ‖g‖^2) :
    |1 + Real.log t| * ‖g‖^2 ≤ envelope a b g := by
  have ht := (mul_nonneg ha.le (sq_nonneg ‖g‖)).trans hl
  have hh := mul_le_mul_of_nonneg_right hl (abs_nonneg (Real.log t))
  have hsq := pow_le_pow_left₀ ht hu 2
  have hlog : |Real.log t| * ‖g‖^2 ≤ (1+b^2*‖g‖^4)/a := by
    apply (le_div_iff₀ ha).2
    nlinarith only [hh, weighted_log_bound ht, hsq]
  unfold envelope
  nlinarith only [hlog, mul_le_mul_of_nonneg_right (abs_add_le 1 (Real.log t)) (sq_nonneg ‖g‖),
    (abs_one : |(1:ℝ)| = 1)]

omit [DecidableEq D] in
private theorem envelope_integrable (a b : ℝ) : Integrable (envelope (D := D) a b)
    (circularGaussian D) := by
  have := circular_probability (D := D)
  exact (circular_pow 2 (by decide)).add
    (((integrable_const (1 : ℝ)).add ((circular_pow 4 (by decide)).const_mul (b^2))).div_const a)

private theorem outer_trace (g : V D) (H : Matrix D D ℂ) :
    ((gaussianOuter g * H).trace).re = quadraticForm H g := by
  rw [Matrix.trace_mul_comm, gaussianOuter, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rfl

/-- The Gaussian matrix moment defining the slope is absolutely integrable. -/
theorem gaussianSlope_integrable {M : Matrix D D ℂ} (hp : M.PosDef) :
    Integrable (fun g : V D ↦ (1+Real.log (quadraticForm M g)) • gaussianOuter g)
      (circularGaussian D) := by
  obtain ⟨a,b,ε,ha,_,he,hr⟩ := line_bounds hp 0
  have hm : Measurable (fun g : V D ↦ 1+Real.log (quadraticForm M g)) :=
    measurable_const.add (Real.measurable_log.comp (by unfold quadraticForm; fun_prop))
  have ho : Continuous (gaussianOuter (D := D)) := by
    unfold gaussianOuter Matrix.vecMulVec
    fun_prop
  apply (envelope_integrable a b).mono' ((hm.smul ho.measurable).aestronglyMeasurable)
  filter_upwards with g
  change ‖(1 + Real.log (quadraticForm M g)) • gaussianOuter g‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, gaussianOuter_norm]
  have h := hr 0 (by simpa) g
  simp at h
  exact slope_bound ha g h.1 h.2

private theorem coord_log_integrable (i : D) :
    Integrable (fun g : V D ↦ Real.log (Complex.normSq (g i))) (circularGaussian D) := by
  -- The integral is Γ′(1) = −γ, so it cannot equal the zero value of an undefined integral.
  by_contra hn
  have he := circular_coordinate_integral i Real.log Real.measurable_log
  rw [integral_undef hn, unit_exponential_integral] at he
  simp_rw [mul_comm (Real.exp _) _] at he
  rw [← Real.deriv_Gamma_one_eq_integral_log, Real.hasDerivAt_Gamma_one.deriv] at he
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- The scalar Gaussian logarithmic moment exists at each positive definite matrix. -/
theorem gaussianLogMean_integrable {M : Matrix D D ℂ} (hp : M.PosDef) :
    Integrable (fun g : V D ↦ Real.log (quadraticForm M g)) (circularGaussian D) := by
  obtain ⟨a, ha, hl⟩ := quadratic_lower hp
  have := circular_probability (D := D)
  have hz := integrable_finsetSum Finset.univ fun i _ ↦ (coord_log_integrable (D := D) i).abs
  apply ((((circular_pow 2 (D := D) (by decide)).const_mul ‖M‖).add
    (integrable_const |Real.log a|)).add hz).mono'
    ((Real.measurable_log.comp (by unfold quadraticForm; fun_prop)).aestronglyMeasurable)
  filter_upwards with g
  let z := fun i ↦ Complex.normSq (g i)
  have hSum : 0 ≤ ∑ i, |Real.log (z i)| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  change |Real.log (quadraticForm M g)| ≤ ‖M‖*‖g‖^2 + |Real.log a| + ∑ i, |Real.log (z i)|
  by_cases hg : g = 0
  · subst g
    simp only [quadraticForm, map_zero, inner_zero_right, Complex.zero_re, Real.log_zero, abs_zero]
    positivity
  obtain ⟨i, hi⟩ : ∃ i, g i ≠ 0 := by
    by_contra! h
    exact hg (PiLp.ext fun i ↦ h i)
  have hi' : 0 < z i := Complex.normSq_pos.mpr hi
  have hu : z i ≤ ‖g‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [z, Complex.sq_norm] using
      Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖g j‖) (Finset.mem_univ i)
  have hpos : 0 < quadraticForm M g := (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hg))).trans_le
    (hl g)
  have hlo := Real.log_le_log (mul_pos ha hi') ((mul_le_mul_of_nonneg_left hu ha.le).trans (hl g))
  rw [Real.log_mul ha.ne' hi'.ne'] at hlo
  have hiSum := Finset.single_le_sum (s := Finset.univ)
    (fun j _ ↦ abs_nonneg (Real.log (z j))) (Finset.mem_univ i)
  apply abs_le.mpr
  constructor
  · nlinarith only [hlo, hiSum, neg_abs_le (Real.log a), neg_abs_le (Real.log (z i)),
      mul_nonneg (norm_nonneg M) (sq_nonneg ‖g‖)]
  · linarith only [le_abs_self (quadraticForm M g), quadratic_bound M g,
      Real.log_le_sub_one_of_pos hpos, abs_nonneg (Real.log a), hSum]

/-- Every sufficiently small Hermitian line perturbation stays positive definite. -/
theorem eventually_posDef_line {M H : Matrix D D ℂ} (hp : M.PosDef) (hH : H.IsHermitian) :
    ∀ᶠ s : ℝ in 𝓝 0, (M+s•H).PosDef := by
  obtain ⟨a,_,ε,ha,_,he,hr⟩ := line_bounds hp H
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) he] with s hs
  have hh := hp.isHermitian.add (hH.smul (show IsSelfAdjoint s from IsSelfAdjoint.all _))
  apply hh.posDef_iff_eigenvalues_pos.mpr
  intro i
  let v := hh.eigenvectorBasis i
  have act : Matrix.toEuclideanLin (M+s•H) v = (hh.eigenvalues i : ℂ) • v := by
    apply PiLp.ext
    intro j
    exact congrFun (hh.mulVec_eigenvectorBasis i) j
  have hv : ‖v‖ = 1 := hh.eigenvectorBasis.orthonormal.norm_eq_one i
  have hq := (hr s (by simpa [Real.dist_eq] using hs) v).1
  have hpv := lt_of_lt_of_le (mul_pos ha (by rw [hv]; norm_num : 0 < ‖v‖ ^ 2)) hq
  unfold quadraticForm at hpv
  rw [act, inner_smul_right, inner_self_eq_norm_sq_to_K, hv] at hpv
  simpa using hpv

end SubentropyCertificates.ConditionalContinuity
