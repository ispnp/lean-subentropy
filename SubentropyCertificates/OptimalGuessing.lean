module

public import SubentropyCertificates.GuessingMeasurement
public import D5.S3.Quantum.Subentropy.GuessingProbability
public import Mathlib.Topology.Order.Monotone

/-!
# The curve bound at optimal quantum guessing probability

`pGuess` is the supremum of the actual success probabilities of positive
identity-summing labelled POVMs. Continuity extends the measurement bound to
that supremum through the closure of the success set. No attainment of the
supremum is assumed.

The supporting `point_guess_probability_mem` proof is ported from the private
`point_guess_mem` helper in the Omega Institute's GuessingProbability.lean,
revision d3e1e931e66ad4a3f54c95ef96cf723edcd7e792 (Apache-2.0). The supporting
success-set bounds and their original attribution are retained upstream.
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
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.MeasurementPosterior

theorem curve_bound_at_supremum (m : ℕ) (S : Set ℝ)
    (hne : S.Nonempty) (hbounded : BddAbove S) (hS : S ⊆ Icc (0 : ℝ) 1)
    (q : ℝ) (hq : ∀ s ∈ S, q ≤ phi m (1 - s)) :
    q ≤ phi m (1 - sSup S) := by
  have hclosure : closure S ⊆ Icc (0 : ℝ) 1 := closure_minimal hS isClosed_Icc
  have hparam : ContinuousOn (fun s : ℝ => 1 - s) (Icc (0 : ℝ) 1) :=
    (continuous_const.sub continuous_id).continuousOn
  have hphi : ContinuousOn (fun s : ℝ => phi m (1 - s)) (Icc (0 : ℝ) 1) :=
    (phi_continuous m).comp hparam (fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  exact le_on_closure hq continuousOn_const (hphi.mono hclosure)
    (csSup_mem_closure hne hbounded)

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

theorem guessing_curve_bound (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) (M : X → Matrix B B ℂ)
    (hM : ∀ x, (M x).PosSemidef) (hsM : ∑ x, M x = 1) :
    0 ≤ conditionalSubentropy p hp hs ρ ∧
      conditionalSubentropy p hp hs ρ ≤ phi m (1 - successProbability p ρ M) := by
  have h := measurement_curve_bound m hn p hp hs ρ M hM hsM id
  simpa only [decisionSuccess, jointProbability, successProbability, id_eq] using h

theorem guessing_success_bounds (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B)
    (M : X → Matrix B B ℂ) (hM : ∀ x, (M x).PosSemidef) (hsM : ∑ x, M x = 1) :
    0 ≤ successProbability p ρ M ∧ successProbability p ρ M ≤ 1 := by
  have h := decision_success_bounds p hp hs ρ M hM hsM id
  simpa only [decisionSuccess, jointProbability, successProbability, id_eq] using h

omit [DecidableEq X] in
theorem point_guess_probability_mem (p : X → ℝ) (ρ : X → DensityState B) (x : X) :
    p x ∈ successProbabilitySet p ρ := by
  classical
  let M : X → Matrix B B ℂ := fun y => if y = x then 1 else 0
  refine ⟨M, ?_, ?_, ?_⟩
  · intro y
    dsimp [M]
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  · simp [M]
  · have ht : (trace (CStarMatrix.ofMatrix.symm (ρ x).1)).re = 1 :=
      congrArg Complex.re (ρ x).2.2
    unfold successProbability
    rw [Finset.sum_eq_single x]
    · simp [M, ht]
    · intro y _ hy
      simp [M, hy]
    · simp

omit [DecidableEq X] in
theorem pGuess_ge_prior (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (x : X) :
    p x ≤ pGuess p ρ :=
  le_csSup (pGuess_bounds p hp hs ρ).2.1 (point_guess_probability_mem p ρ x)

omit [DecidableEq X] in
theorem optimal_error_range (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) : 1 - pGuess p ρ ∈ Icc 0 (uniformError m) := by
  have hsum : 1 ≤ ((m + 2 : ℕ) : ℝ) * pGuess p ρ := by
    calc
      1 = ∑ x, p x := hs.symm
      _ ≤ ∑ _x : X, pGuess p ρ := Finset.sum_le_sum (fun x _ => pGuess_ge_prior p hp hs ρ x)
      _ = _ := by simp [hn, nsmul_eq_mul]
  have hnR : (0 : ℝ) < (m + 2 : ℕ) := by positivity
  have hlower : 1 / ((m + 2 : ℕ) : ℝ) ≤ pGuess p ρ := (div_le_iff₀ hnR).mpr (by
    simpa only [mul_comm] using hsum)
  have hupper : pGuess p ρ ≤ 1 := (pGuess_bounds p hp hs ρ).2.2.2.1
  exact ⟨sub_nonneg.mpr hupper, by unfold uniformError; linarith⟩

/-- The nonlinear inequality and the admissible optimal-error range.
Pointwise attainment, the full equality characterization and the tangent bound
are separate certification targets. -/
theorem optimal_discrimination_bound (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) :
    0 ≤ conditionalSubentropy p hp hs ρ ∧
      conditionalSubentropy p hp hs ρ ≤ phi m (1 - pGuess p ρ) ∧
      1 - pGuess p ρ ∈ Icc 0 (uniformError m) := by
  have hb := pGuess_bounds p hp hs ρ
  have hS : successProbabilitySet p ρ ⊆ Icc (0 : ℝ) 1 := by
    rintro s ⟨M, hM, hsM, rfl⟩
    exact guessing_success_bounds p hp hs ρ M hM hsM
  have hcurve := curve_bound_at_supremum m (successProbabilitySet p ρ) hb.1 hb.2.1 hS
    (conditionalSubentropy p hp hs ρ) (by
      rintro s ⟨M, hM, hsM, rfl⟩
      exact (guessing_curve_bound m hn p hp hs ρ M hM hsM).2)
  have hzero : 0 ≤ conditionalSubentropy p hp hs ρ := by
    obtain ⟨s, M, hM, hsM, hsuccess⟩ := hb.1
    exact (guessing_curve_bound m hn p hp hs ρ M hM hsM).1
  exact ⟨hzero, hcurve, optimal_error_range m hn p hp hs ρ⟩

/-- A threshold formulation of inversion on the checked increasing branch. -/
theorem error_threshold_lower_bound (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) (r : ℝ) (hr : r ∈ Icc 0 (uniformError m))
    (hcert : phi m r ≤ conditionalSubentropy p hp hs ρ) : r ≤ 1 - pGuess p ρ := by
  have h := optimal_discrimination_bound m hn p hp hs ρ
  by_contra hnle
  have hlt : 1 - pGuess p ρ < r := lt_of_not_ge hnle
  have hcurve := phi_strictMono m h.2.2 hr hlt
  linarith [h.2.1]

end SubentropyCertificates.Discrimination
