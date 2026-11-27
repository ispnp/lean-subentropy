module

public import SubentropyCertificates.QuadraticStatistic
public import SubentropyCertificates.QuadraticCurve
public import SubentropyCertificates.GuessingAttainment

/-! A bound from the measurement posteriors, followed by optimization
over label-valued measurements. Zero-probability outcomes have weight zero. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder
namespace SubentropyCertificates.Quadratic
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.MeasurementPosterior
open SubentropyCertificates.Discrimination
variable {X B Y : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] [Fintype Y]

omit [DecidableEq B] in
private theorem one_piece (H : Matrix (X × B) (X × B) ℂ) (hH : H.PosSemidef)
    (hs : mass H = 1) : offSquare H / 2 ≤ collisionGap (labelMass H) := by
  have h := Finset.sum_le_sum (s := distinctPairs X) (fun z _ => blockSquare_le H hH z)
  change offSquare H ≤ ∑ z ∈ distinctPairs X, labelMass H z.1 * labelMass H z.2 at h
  rw [distinct_sum (fun x z => labelMass H x * labelMass H z)] at h
  simp only [← Finset.mul_sum, sum_labelMass,hs,mul_one,← sq] at h
  unfold collisionGap
  linarith

omit [DecidableEq B] in
theorem gram_posterior_bound (G : Y → Matrix (X × B) (X × B) ℂ) (hG : ∀ y, (G y).PosSemidef)
    (hs : ∑ y, mass (G y) = 1) :
    offSquare (∑ y, G y)/2 ≤ ∑ y, mass (G y)*collisionGap (labelPosterior (G y)) := by
  let q y := mass (G y)
  let H y := (q y)⁻¹ • G y
  have hq y : 0 ≤ q y := mass_nonneg _ (hG y)
  have hpiece y : q y • H y = G y := by
    by_cases hz : q y=0
    · rw [hz,zero_smul,psd_eq_zero_of_mass_zero _ (hG y) hz]
    · simp [H,smul_smul,hz]
  have h := offSquare_mean q hq hs H
  simp_rw [hpiece] at h
  have hu (y : Y) : q y * offSquare (H y) ≤ 2*(q y*collisionGap (labelPosterior (G y))) := by
    by_cases hz : q y=0
    · simp [hz]
    have hm : mass (H y) = 1 := by
      simp only [H,mass,Matrix.trace_smul,Complex.smul_re,smul_eq_mul]
      change (q y)⁻¹ * q y = 1
      exact inv_mul_cancel₀ hz
    have hl : labelMass (H y) = labelPosterior (G y) := by
      funext x
      rw [show H y = (q y)⁻¹ • G y from rfl, labelMass_smul]
      unfold labelPosterior
      change (q y)⁻¹ * _ = _ / q y
      ring
    have hb := one_piece (H y) ((hG y).smul (inv_nonneg.mpr (hq y))) hm
    rw [hl] at hb
    nlinarith [mul_nonneg (hq y) (sub_nonneg.mpr hb)]
  have ht := h.trans (Finset.sum_le_sum fun y _ => hu y)
  rw [← Finset.mul_sum] at ht
  change _ ≤ ∑ y, q y*_
  linarith

theorem measurement_collision_bound (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1)
    (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hnorm : ∑ y, F y=1) :
    statistic p hp hs ρ ≤ ∑ y, outcomeProbability p ρ (F y)*collisionGap (posterior p ρ (F y)) := by
  rw [statistic_eq_gram, ← sum_effectGram p ρ F hnorm]
  have h := gram_posterior_bound (fun y => effectGram p ρ (F y))
    (fun y => effectGram_posSemidef p ρ _ (hF y))
    (by simpa only [mass_effectGram p hp ρ] using sum_outcomeProbability p hp hs ρ F hnorm)
  have hb (y : Y) : labelPosterior (effectGram p ρ (F y)) = posterior p ρ (F y) := by
    funext x
    rw [labelPosterior,posterior,labelMass_effectGram p hp ρ,mass_effectGram p hp ρ]
  simpa only [hb,mass_effectGram p hp ρ] using h

theorem optimal_quadratic_upper (m : ℕ) (hn : Fintype.card X=m+2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1) (ρ : X → DensityState B) :
    statistic p hp hs ρ ≤ curve m (1-pGuess p ρ) := by
  obtain ⟨F,hF,hnorm,hopt⟩ := exists_optimal_povm p hp hs ρ
  let q y := outcomeProbability p ρ (F y)
  let b y := posterior p ρ (F y)
  have hq y : 0 ≤ q y := outcomeProbability_nonneg p hp ρ _ (hF y)
  have hqs : ∑ y, q y=1 := sum_outcomeProbability p hp hs ρ F hnorm
  have hlocal (y : X) : q y*collisionGap (b y) ≤ q y*curve m (1-b y y) := by
    by_cases hz : q y=0
    · simp [hz]
    exact mul_le_mul_of_nonneg_left (collision_coordinate m hn (b y)
      (posterior_probability p hp ρ _ (hF y) (lt_of_le_of_ne (hq y) (Ne.symm hz))).2 y) (hq y)
  have h := (measurement_collision_bound p hp hs ρ F hF hnorm).trans
    ((Finset.sum_le_sum (fun y _ => hlocal y)).trans (curve_average m q (fun y => 1-b y y) hq hqs))
  have hsucc (y) : q y*b y y = jointProbability p ρ (F y) y := weighted_posterior p hp ρ (F y) (hF y) y
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hsucc,hqs] at h
  exact h.trans_eq (congrArg (fun z => curve m (1-z)) hopt)

end SubentropyCertificates.Quadratic
