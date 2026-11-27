module

public import SubentropyCertificates.IdenticalPureSignals

/-!
# Equality in the comparison with measurement posteriors

The posterior average ranges only over positive-probability outcomes. The
point-mass criterion follows from strict concavity of classical subentropy
on the closed simplex; it applies to arbitrary finite signal and outcome sets.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.QuantumEquality
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.MeasurementPosterior
open SubentropyCertificates.Discrimination

variable {X : Type*} [Fintype X] [DecidableEq X]

def pointMass (i : X) : X → ℝ := fun j => if j = i then 1 else 0

theorem pointMass_probability (i : X) : pointMass i ∈ probabilitySimplex X := by
  exact ⟨fun j => by by_cases h : j = i <;> simp [pointMass, h], by simp [pointMass]⟩

theorem pointMass_subentropy (i : X) : classicalSubentropy (pointMass i) = 0 := by
  let v (j : X) : ℂ := if j = i then 1 else 0
  have hv : ∑ j, star (v j) * v j = 1 := by simp [v]
  have hd : diagonal (fun j => (pointMass i j : ℂ)) = vecMulVec v (star v) := by
    apply Matrix.ext
    intro a b
    by_cases ha : a = i
    · subst a
      by_cases hb : b = i
      · subst b; simp [pointMass, v, vecMulVec]
      · simp [pointMass, v, vecMulVec, Matrix.diagonal, hb, Ne.symm hb]
    · simp [pointMass, v, vecMulVec, Matrix.diagonal, ha]
  exact (congrArg matrixSubentropy hd).trans (matrixSubentropy_pure v hv)

theorem pointMass_barycenter (p : X → ℝ) : ∑ i, p i • pointMass i = p := by
  funext j
  simp [Finset.sum_apply, pointMass, Pi.smul_apply, mul_ite]

theorem classical_subentropy_nonneg (p : X → ℝ) (hp : p ∈ probabilitySimplex X) :
    0 ≤ classicalSubentropy p := by
  have h := classical_subentropy_strictConcave.concaveOn.le_map_sum
    (t := Finset.univ) (w := p) (p := pointMass) (fun i _ => hp.1 i) hp.2
    (fun i _ => pointMass_probability i)
  simpa only [pointMass_barycenter, pointMass_subentropy, smul_zero, Finset.sum_const_zero] using h

theorem classical_zero_iff_pointMass (p : X → ℝ) (hp : p ∈ probabilitySimplex X) :
    classicalSubentropy p = 0 ↔ ∃ i, p = pointMass i := by
  constructor
  · intro hz
    have h := classical_subentropy_strictConcave.map_sum_eq_iff'
      (t := Finset.univ) (w := p) (p := pointMass) (fun i _ => hp.1 i) hp.2
      (fun i _ => pointMass_probability i)
    simp only [pointMass_barycenter, pointMass_subentropy, smul_zero, Finset.sum_const_zero] at h
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra! hzero
      have hs := hp.2
      simp [hzero] at hs
    exact ⟨i, (h.mp hz i (Finset.mem_univ _) hi).symm⟩
  · rintro ⟨i, rfl⟩
    exact pointMass_subentropy i

variable {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq B]

def posteriorAverage (p : X → ℝ) (ρ : X → DensityState B) (F : Y → Matrix B B ℂ) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y => 0 < outcomeProbability p ρ (F y)),
    outcomeProbability p ρ (F y) * classicalSubentropy (posterior p ρ (F y))

theorem posteriorAverage_zero_iff (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (F : Y → Matrix B B ℂ) (hF : ∀ y, (F y).PosSemidef) :
    posteriorAverage p ρ F = 0 ↔
      ∀ y, 0 < outcomeProbability p ρ (F y) → ∃ x, posterior p ρ (F y) = pointMass x := by
  let S := Finset.univ.filter (fun y => 0 < outcomeProbability p ρ (F y))
  have hpos {y : Y} (hy : y ∈ S) : 0 < outcomeProbability p ρ (F y) := (Finset.mem_filter.mp hy).2
  have hb {y : Y} (hy : y ∈ S) : posterior p ρ (F y) ∈ probabilitySimplex X :=
    posterior_probability p hp ρ (F y) (hF y) (hpos hy)
  have hterm (y : Y) (hy : y ∈ S) :
      0 ≤ outcomeProbability p ρ (F y) * classicalSubentropy (posterior p ρ (F y)) :=
    mul_nonneg (hpos hy).le (classical_subentropy_nonneg _ (hb hy))
  constructor
  · intro hz y hy
    have hmem : y ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    have heq := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hz y hmem
    exact (classical_zero_iff_pointMass _ (hb hmem)).mp ((mul_eq_zero.mp heq).resolve_left hy.ne')
  · intro h
    apply Finset.sum_eq_zero
    intro y hy
    exact mul_eq_zero_of_right _ ((classical_zero_iff_pointMass _ (hb hy)).mpr (h y (hpos hy)))

/-- Under the zero hypothesis, this is the upper equality in the paper's
measurement comparison. A complete POVM is covered, and the equivalence
itself only uses positivity of its effects. -/
theorem zero_conditional_posterior_equality_iff (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hz : conditionalSubentropy p hp hs ρ = 0) :
    conditionalSubentropy p hp hs ρ = posteriorAverage p ρ F ↔
      ∀ y, 0 < outcomeProbability p ρ (F y) → ∃ x, posterior p ρ (F y) = pointMass x := by
  rw [hz, eq_comm]
  exact posteriorAverage_zero_iff p hp ρ F hF

theorem zero_and_posterior_equality_iff (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hsF : ∑ y, F y = 1) :
    (conditionalSubentropy p hp hs ρ = 0 ∧
      conditionalSubentropy p hp hs ρ = posteriorAverage p ρ F) ↔
      ∀ y, 0 < outcomeProbability p ρ (F y) → ∃ x, posterior p ρ (F y) = pointMass x := by
  constructor
  · rintro ⟨hz, he⟩
    exact (zero_conditional_posterior_equality_iff p hp hs ρ F hF hz).mp he
  · intro h
    have ha := (posteriorAverage_zero_iff p hp ρ F hF).mpr h
    obtain ⟨hlo, hhi⟩ := measurement_posterior_comparison p hp hs ρ F hF hsF
    change conditionalSubentropy p hp hs ρ ≤ posteriorAverage p ρ F at hhi
    exact ⟨le_antisymm (hhi.trans_eq ha) hlo, le_antisymm hhi (ha.trans_le hlo)⟩

theorem eq_pointMass_iff_probability_one (p : X → ℝ) (hp : p ∈ probabilitySimplex X) (i : X) :
    p = pointMass i ↔ p i = 1 := by
  constructor
  · rintro rfl
    simp [pointMass]
  · intro hi
    have hsum := Finset.sum_erase_add Finset.univ p (Finset.mem_univ i)
    rw [hp.2, hi] at hsum
    have hzero : ∑ j ∈ Finset.univ.erase i, p j = 0 := by linarith
    have hoff := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp.1 j)).mp hzero
    funext j
    by_cases hji : j = i
    · subst j; simpa [pointMass] using hi
    · simpa [pointMass, hji] using hoff j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)

/-- A decision rule succeeds with probability one exactly when it selects
the atom of every positive-probability posterior. -/
theorem perfect_decision_iff (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hsF : ∑ y, F y = 1) (selected : Y → X) :
    decisionSuccess p ρ F selected = 1 ↔ ∀ y, 0 < outcomeProbability p ρ (F y) →
      posterior p ρ (F y) = pointMass (selected y) := by
  let q := fun y => outcomeProbability p ρ (F y)
  let b := fun y => posterior p ρ (F y)
  let S := Finset.univ.filter (fun y => 0 < q y)
  have hpos {y : Y} (hy : y ∈ S) : 0 < q y := (Finset.mem_filter.mp hy).2
  have hb (y : Y) (hy : 0 < q y) : b y ∈ probabilitySimplex X :=
    posterior_probability p hp ρ (F y) (hF y) hy
  have hterm (y : Y) (hy : y ∈ S) : 0 ≤ q y * (1 - b y (selected y)) := by
    apply mul_nonneg (hpos hy).le
    apply sub_nonneg.mpr
    rw [← (hb y (hpos hy)).2]
    exact Finset.single_le_sum (fun j _ => (hb y (hpos hy)).1 j) (Finset.mem_univ _)
  have herr := posterior_average_error p hp hs ρ F hF hsF selected
  change (∑ y ∈ S, q y * (1 - b y (selected y))) = 1 - decisionSuccess p ρ F selected at herr
  constructor
  · intro h y hy
    have hmem : y ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    rw [h, sub_self] at herr
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp herr y hmem
    have hone := (mul_eq_zero.mp hz).resolve_left (hpos hmem).ne'
    exact (eq_pointMass_iff_probability_one _ (hb y hy) _).mpr (sub_eq_zero.mp hone).symm
  · intro h
    have hz : ∑ y ∈ S, q y * (1 - b y (selected y)) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hone := (eq_pointMass_iff_probability_one _ (hb y (hpos hy)) _).mp (h y (hpos hy))
      rw [hone, sub_self, mul_zero]
    linarith

theorem zero_equality_iff_perfect_decision (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hsF : ∑ y, F y = 1) (hz : conditionalSubentropy p hp hs ρ = 0) :
    conditionalSubentropy p hp hs ρ = posteriorAverage p ρ F ↔
      ∃ selected : Y → X, decisionSuccess p ρ F selected = 1 := by
  classical
  rw [zero_conditional_posterior_equality_iff p hp hs ρ F hF hz]
  constructor
  · intro h
    have hX : Nonempty X := by
      by_contra hnone
      have : IsEmpty X := not_nonempty_iff.mp hnone
      simp at hs
    let selected (y : Y) : X := if hy : 0 < outcomeProbability p ρ (F y)
      then Classical.choose (h y hy) else Classical.choice hX
    refine ⟨selected, (perfect_decision_iff p hp hs ρ F hF hsF selected).mpr ?_⟩
    intro y hy
    simpa only [selected, dite_eq_left hy] using Classical.choose_spec (h y hy)
  · rintro ⟨selected, hsel⟩ y hy
    exact ⟨selected y, (perfect_decision_iff p hp hs ρ F hF hsF selected).mp hsel y hy⟩

omit [DecidableEq X] in
theorem mixture_congr_on_support (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ σ : X → DensityState B) (h : ∀ x, 0 < p x → ρ x = σ x) :
    mixtureState p hp hs ρ = mixtureState p hp hs σ := by
  apply Subtype.ext
  change ∑ x, p x • (ρ x).1 = ∑ x, p x • (σ x).1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p x = 0
  · simp only [hx, zero_smul]
  · rw [h x (lt_of_le_of_ne (hp x) (Ne.symm hx))]

theorem conditional_congr_on_support (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ σ : X → DensityState B) (h : ∀ x, 0 < p x → ρ x = σ x) :
    conditionalSubentropy p hp hs ρ = conditionalSubentropy p hp hs σ := by
  have hr : recordState p hp hs ρ = recordState p hp hs σ := by
    apply mixture_congr_on_support
    intro x hx
    rw [h x hx]
  unfold conditionalSubentropy
  rw [hr, mixture_congr_on_support p hp hs ρ σ h]

omit [DecidableEq X] in
/-- Identical signals on the prior support leave the prior unchanged after
conditioning on any outcome of positive probability. -/
theorem posterior_of_identical_on_support (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (σ : DensityState B)
    (h : ∀ x, 0 < p x → ρ x = σ) (E : Matrix B B ℂ) (hpos : 0 < outcomeProbability p ρ E) :
    posterior p ρ E = p := by
  classical
  let r := (trace (E * CStarMatrix.ofMatrix.symm σ.1)).re
  have hj (x : X) : jointProbability p ρ E x = p x * r := by
    unfold jointProbability
    by_cases hx : p x = 0
    · simp only [hx, zero_mul]
    · rw [h x (lt_of_le_of_ne (hp x) (Ne.symm hx))]
  have hq : outcomeProbability p ρ E = r := by
    calc
      _ = ∑ x, jointProbability p ρ E x := (sum_jointProbability p hp ρ E).symm
      _ = ∑ x, p x * r := Finset.sum_congr rfl (fun x _ => hj x)
      _ = r := by rw [← Finset.sum_mul, hs, one_mul]
  funext x
  unfold posterior
  rw [hj, ← hq, mul_div_cancel_right₀ _ hpos.ne']

theorem posterior_equality_of_identical_pure_on_support (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B)
    (v : B → ℂ) (hv : ∑ j, star (v j) * v j = 1)
    (h : ∀ x, 0 < p x → ρ x = pureSignal v hv) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hsF : ∑ y, F y = 1) :
    conditionalSubentropy p hp hs ρ = posteriorAverage p ρ F := by
  let q := fun y => outcomeProbability p ρ (F y)
  let S := Finset.univ.filter (fun y => 0 < q y)
  have hqs : ∑ y ∈ S, q y = 1 :=
    (sum_over_positive q (fun y => outcomeProbability_nonneg p hp ρ (F y) (hF y))
      q (fun _ hz => hz)).trans (sum_outcomeProbability p hp hs ρ F hsF)
  calc
    _ = conditionalSubentropy p hp hs (fun _ => pureSignal v hv) :=
      conditional_congr_on_support p hp hs ρ _ h
    _ = classicalSubentropy p := conditional_identical_pure p hp hs v hv
    _ = ∑ y ∈ S, q y * classicalSubentropy p := by rw [← Finset.sum_mul, hqs, one_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [posterior_of_identical_on_support p hp hs ρ _ h (F y) (Finset.mem_filter.mp hy).2]

end SubentropyCertificates.QuantumEquality
