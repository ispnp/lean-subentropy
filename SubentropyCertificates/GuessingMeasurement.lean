module

public import SubentropyCertificates.QuantumMeasurement
public import SubentropyCertificates.CurveMonotonicity

/-!
# The subentropy curve bound for each guessing measurement

Outcomes Y and labels X are independent finite types. A decision rule assigns
a label to each outcome. Zero outcome probabilities are omitted from the
posterior average, and are proved to contribute zero to success and error.
The classical parameter m represents n-2, as in the retained v4 certificates.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.Discrimination
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.MeasurementPosterior

theorem classical_posterior_bound_finset {X Y : Type*}
    [Fintype X] [DecidableEq X] (m : ℕ) (hn : Fintype.card X = m + 2)
    (S : Finset Y) (q : Y → ℝ) (hq : ∀ y ∈ S, 0 ≤ q y)
    (hs : ∑ y ∈ S, q y = 1) (b : Y → X → ℝ)
    (hb : ∀ y ∈ S, b y ∈ probabilitySimplex X) (selected : Y → X) :
    (∑ y ∈ S, q y * classicalSubentropy (b y)) ≤
      phi m (∑ y ∈ S, q y * (1 - b y (selected y))) := by
  have herr (y : Y) (hy : y ∈ S) : 1 - b y (selected y) ∈ Icc (0 : ℝ) 1 := by
    have hle : b y (selected y) ≤ 1 := by
      rw [← (hb y hy).2]
      exact Finset.single_le_sum (fun i _ => (hb y hy).1 i) (Finset.mem_univ _)
    exact ⟨sub_nonneg.mpr hle, by linarith [(hb y hy).1 (selected y)]⟩
  calc
    _ ≤ ∑ y ∈ S, q y * phi m (1 - b y (selected y)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left
        (classical_coordinate_bound_finite m hn (b y) (hb y hy) (selected y)) (hq y hy)
    _ ≤ _ := (phi_concave m).le_map_sum hq hs herr

theorem sum_over_positive {Y : Type*} [Fintype Y] (q : Y → ℝ)
    (hq : ∀ y, 0 ≤ q y) (f : Y → ℝ) (hz : ∀ y, q y = 0 → f y = 0) :
    (∑ y ∈ Finset.univ.filter (fun y => 0 < q y), f y) = ∑ y, f y := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro y _ hy
  have hn : ¬0 < q y := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hy
  exact hz y (le_antisymm (le_of_not_gt hn) (hq y))

variable {X B Y : Type*} [Fintype X] [DecidableEq X]
  [Fintype B] [DecidableEq B] [Fintype Y]

def decisionSuccess (p : X → ℝ) (ρ : X → DensityState B)
    (F : Y → Matrix B B ℂ) (selected : Y → X) : ℝ :=
  ∑ y, jointProbability p ρ (F y) (selected y)

theorem weighted_posterior (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (F : Matrix B B ℂ) (hF : F.PosSemidef) (x : X) :
    outcomeProbability p ρ F * posterior p ρ F x = jointProbability p ρ F x := by
  by_cases hz : outcomeProbability p ρ F = 0
  · rw [hz, zero_mul, jointProbability_eq_zero_of_outcome_zero p hp ρ F hF hz x]
  · unfold posterior
    exact mul_div_cancel₀ _ hz

theorem decision_success_bounds (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B)
    (F : Y → Matrix B B ℂ) (hF : ∀ y, (F y).PosSemidef)
    (hsF : ∑ y, F y = 1) (selected : Y → X) :
    0 ≤ decisionSuccess p ρ F selected ∧ decisionSuccess p ρ F selected ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun y _ => jointProbability_nonneg p hp ρ (F y) (hF y) _), ?_⟩
  calc
    _ ≤ ∑ y, outcomeProbability p ρ (F y) := by
      apply Finset.sum_le_sum
      intro y _
      rw [← sum_jointProbability p hp ρ (F y)]
      exact Finset.single_le_sum (fun x _ => jointProbability_nonneg p hp ρ (F y) (hF y) x)
        (Finset.mem_univ _)
    _ = 1 := sum_outcomeProbability p hp hs ρ F hsF

theorem posterior_average_error (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B)
    (F : Y → Matrix B B ℂ) (hF : ∀ y, (F y).PosSemidef)
    (hsF : ∑ y, F y = 1) (selected : Y → X) :
    (∑ y ∈ Finset.univ.filter (fun y => 0 < outcomeProbability p ρ (F y)),
      outcomeProbability p ρ (F y) * (1 - posterior p ρ (F y) (selected y))) =
      1 - decisionSuccess p ρ F selected := by
  rw [sum_over_positive (fun y => outcomeProbability p ρ (F y))
    (fun y => outcomeProbability_nonneg p hp ρ (F y) (hF y))
    (fun y => outcomeProbability p ρ (F y) * (1 - posterior p ρ (F y) (selected y)))
    (fun y hz => by rw [hz, zero_mul])]
  simp_rw [mul_sub, mul_one, weighted_posterior p hp ρ _ (hF _)]
  rw [Finset.sum_sub_distrib, sum_outcomeProbability p hp hs ρ F hsF]
  rfl

theorem measurement_curve_bound (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hsF : ∑ y, F y = 1) (selected : Y → X) :
    0 ≤ conditionalSubentropy p hp hs ρ ∧
      conditionalSubentropy p hp hs ρ ≤ phi m (1 - decisionSuccess p ρ F selected) := by
  have hcomp := measurement_posterior_comparison p hp hs ρ F hF hsF
  let q : Y → ℝ := fun y => outcomeProbability p ρ (F y)
  let S : Finset Y := Finset.univ.filter (fun y => 0 < q y)
  have hq (y : Y) : 0 ≤ q y := outcomeProbability_nonneg p hp ρ (F y) (hF y)
  have hsum : ∑ y ∈ S, q y = 1 := by
    rw [sum_over_positive q hq q (fun _ hz => hz)]
    exact sum_outcomeProbability p hp hs ρ F hsF
  have hb (y : Y) (hy : y ∈ S) : posterior p ρ (F y) ∈ probabilitySimplex X :=
    posterior_probability p hp ρ (F y) (hF y) (Finset.mem_filter.mp hy).2
  have hclass := classical_posterior_bound_finset m hn S q (fun y _ => hq y) hsum
    (fun y => posterior p ρ (F y)) hb selected
  have he := posterior_average_error p hp hs ρ F hF hsF selected
  change (∑ y ∈ S, q y * (1 - posterior p ρ (F y) (selected y))) =
    1 - decisionSuccess p ρ F selected at he
  rw [he] at hclass
  exact ⟨hcomp.1, hcomp.2.trans hclass⟩

end SubentropyCertificates.Discrimination
