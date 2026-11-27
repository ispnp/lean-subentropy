module

public import SubentropyCertificates.BinaryHelstrom

/-! Section 6.2, eq:binary-quadratic-exact. All normalized amplitude
vectors and all priors in [0,1] are allowed, with no independence assumption. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder
namespace SubentropyCertificates.Helstrom
open SubentropyCertificates.PinchingEquality
open SubentropyCertificates.Discrimination
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.InputInformationBalance
open SubentropyCertificates.Quadratic
open D5.S3.Quantum.Subentropy.GuessingProbability
variable {D : Type*} [Fintype D] [DecidableEq D]

private theorem inverse_binary (c : ℝ) : inverse 0 c = (1-Real.sqrt (1-4*c))/2 := by
  rw [inverse_formula]
  norm_num
  ring

/-- The purity-difference statistic, its inverse lower bound, the optimal
binary error and the trace norm of the Helstrom difference for pure signals. -/
theorem binary_pure_quadratic_exact {p : ℝ} (hp : p ∈ Icc 0 1) (v w : D → ℂ)
    (hv : ∑ i, star (v i)*v i=1) (hw : ∑ i, star (w i)*w i=1) :
    let ρ := purePair v w hv hw
    let s := ‖amplitude v w‖
    let c := statistic (binaryPrior p) (binary_prior_nonneg hp) (binary_prior_sum p) ρ
    let e := 1-pGuess (binaryPrior p) ρ
    c = p*(1-p)*s^2 ∧ inverse 0 c = e ∧
      e = (1-Real.sqrt (1-4*(p*(1-p)*s^2)))/2 ∧
      (∑ i, |(difference_hermitian hp ρ).eigenvalues i|) =
        Real.sqrt (1-4*(p*(1-p)*s^2)) := by
  let ρ := purePair v w hv hw
  let c := p*(1-p)*‖amplitude v w‖^2
  let t := ∑ i, |(difference_hermitian hp ρ).eigenvalues i|
  let e := 1-pGuess (binaryPrior p) ρ
  have hstat := binary_pure_statistic hp v w hv hw
  have hlow := (complementary_quadratic_bound 0 (by decide : Fintype.card (Fin 2)=0+2)
    (binaryPrior p) (binary_prior_nonneg hp) (binary_prior_sum p) ρ).1.2.2
  change inverse 0 (statistic _ _ _ (purePair v w hv hw)) ≤ e at hlow
  rw [hstat,inverse_binary] at hlow
  have hm := spectral_second_moment (difference_hermitian hp ρ)
  rw [difference_trace, show (difference p ρ * difference p ρ).trace.re = _ from
    difference_second_moment p v w hv hw] at hm
  have hdisc : 1-4*c ≤ t^2 := by
    change 2*(p^2+(1-p)^2-2*c) ≤ t^2+(2*p-1)^2 at hm
    nlinarith
  have ht : 0 ≤ t := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hroot := Real.sqrt_le_iff.mpr ⟨ht,hdisc⟩
  have hs : pGuess (binaryPrior p) ρ = (1+t)/2 := (binary_helstrom hp ρ).1
  have herr : e = (1-Real.sqrt (1-4*c))/2 := by
    apply le_antisymm _ hlow
    dsimp only [e]
    linarith
  refine ⟨hstat,?_,herr,?_⟩
  · change inverse 0 (statistic _ _ _ (purePair v w hv hw)) = e
    rw [hstat,inverse_binary]
    exact herr.symm
  · change t = Real.sqrt (1-4*c)
    dsimp only [e] at herr
    linarith

/-- At unit overlap the states agree up to phase and the error is the
smaller prior, including the tie at p=1/2. -/
theorem unit_overlap_error {p : ℝ} (hp : p ∈ Icc 0 1) (v w : D → ℂ)
    (hv : ∑ i, star (v i)*v i=1) (hw : ∑ i, star (w i)*w i=1) (h : ‖amplitude v w‖=1) :
    1-pGuess (binaryPrior p) (purePair v w hv hw) = min p (1-p) := by
  rw [(binary_pure_quadratic_exact hp v w hv hw).2.2.1,h]
  rw [show 1-4*(p*(1-p)*(1:ℝ)^2) = (p-(1-p))^2 by ring,Real.sqrt_sq_eq_abs]
  rcases le_total p (1-p) with hl | hl
  · rw [abs_of_nonpos (sub_nonpos.mpr hl),min_eq_left hl]; ring
  · rw [abs_of_nonneg (sub_nonneg.mpr hl),min_eq_right hl]; ring

theorem zero_prior_errors (v w : D → ℂ) (hv : ∑ i, star (v i)*v i=1)
    (hw : ∑ i, star (w i)*w i=1) :
    1-pGuess (binaryPrior 0) (purePair v w hv hw) = 0 ∧
    1-pGuess (binaryPrior 1) (purePair v w hv hw) = 0 := by
  constructor
  · rw [(binary_pure_quadratic_exact (p := 0) (by constructor <;> norm_num) v w hv hw).2.2.1]
    norm_num
  · rw [(binary_pure_quadratic_exact (p := 1) (by constructor <;> norm_num) v w hv hw).2.2.1]
    norm_num

theorem orthogonal_pure_error {p : ℝ} (hp : p ∈ Icc 0 1) (v w : D → ℂ)
    (hv : ∑ i, star (v i)*v i=1) (hw : ∑ i, star (w i)*w i=1) (h : amplitude v w=0) :
    1-pGuess (binaryPrior p) (purePair v w hv hw) = 0 := by
  rw [(binary_pure_quadratic_exact hp v w hv hw).2.2.1,h]
  norm_num

theorem identical_pure_error {p : ℝ} (hp : p ∈ Icc 0 1) (v : D → ℂ)
    (hv : ∑ i, star (v i)*v i=1) :
    1-pGuess (binaryPrior p) (purePair v v hv hv) = min p (1-p) := by
  apply unit_overlap_error hp
  rw [show amplitude v v = 1 from hv,norm_one]

private theorem pure_representation (σ : DensityState D) (hσ : IsPure σ) :
    ∃ (v : D → ℂ) (hv : ∑ i, star (v i)*v i=1), σ = pureSignal v hv := by
  obtain ⟨v,hv⟩ := hσ
  have htr := σ.2.2
  change ∑ i, σ.1 i i = 1 at htr
  simp only [hv] at htr
  have hn : ∑ i, star (v i)*v i=1 := by simpa only [mul_comm] using htr
  refine ⟨v,hn,Subtype.ext ?_⟩
  ext i j
  exact hv i j

/-- An equivalent statement for bundled pure density states, with no
choice of amplitude or phase in the hypotheses or conclusion. -/
theorem binary_pure_density_exact {p : ℝ} (hp : p ∈ Icc 0 1) (ρ : Fin 2 → DensityState D)
    (hρ : ∀ i, IsPure (ρ i)) :
    let c := statistic (binaryPrior p) (binary_prior_nonneg hp) (binary_prior_sum p) ρ
    let s₂ := ((CStarMatrix.ofMatrix.symm (ρ 0).1) * (CStarMatrix.ofMatrix.symm (ρ 1).1)).trace.re
    c = p*(1-p)*s₂ ∧ inverse 0 c = 1-pGuess (binaryPrior p) ρ ∧
      1-pGuess (binaryPrior p) ρ = (1-Real.sqrt (1-4*(p*(1-p)*s₂)))/2 := by
  obtain ⟨v,hv,h₀⟩ := pure_representation (ρ 0) (hρ 0)
  obtain ⟨w,hw,h₁⟩ := pure_representation (ρ 1) (hρ 1)
  have hpair : ρ = purePair v w hv hw := by
    funext i; fin_cases i <;> first | exact h₀ | exact h₁
  subst ρ
  have h := binary_pure_quadratic_exact hp v w hv hw
  change _ = p*(1-p)*(projector v * projector w).trace.re ∧ _ ∧
    _ = (1-Real.sqrt (1-4*(p*(1-p)*(projector v * projector w).trace.re)))/2
  rw [projector_overlap]
  exact ⟨h.1,h.2.1,h.2.2.1⟩

end SubentropyCertificates.Helstrom
