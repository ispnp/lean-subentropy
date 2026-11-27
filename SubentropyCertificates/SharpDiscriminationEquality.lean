module

public import SubentropyCertificates.GuessingAttainment
public import SubentropyCertificates.PositiveEquality
public import SubentropyCertificates.ClassicalEquality
public import SubentropyCertificates.CurveInverse

/-! Equality in the sharp discrimination bound. At an optimal labelled POVM both
inequalities in the posterior comparison must be equalities. At positive error
this first identifies the supported signals and then identifies every prior. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.Discrimination
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.MeasurementPosterior
open SubentropyCertificates.QuantumEquality
open SubentropyCertificates.PinchingEquality

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

theorem posteriorAverage_le_guessing_curve (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) (M : X → Matrix B B ℂ)
    (hM : ∀ x, (M x).PosSemidef) (hsM : ∑ x, M x = 1) :
    posteriorAverage p ρ M ≤ phi m (1 - successProbability p ρ M) := by
  let q (x : X) := outcomeProbability p ρ (M x)
  let S := Finset.univ.filter (fun x => 0 < q x)
  have hq (x : X) : 0 ≤ q x := outcomeProbability_nonneg p hp ρ (M x) (hM x)
  have hsum : ∑ x ∈ S, q x = 1 := by
    rw [sum_over_positive q hq q (fun _ hz => hz)]
    exact sum_outcomeProbability p hp hs ρ M hsM
  have hb (x : X) (hx : x ∈ S) : posterior p ρ (M x) ∈ probabilitySimplex X :=
    posterior_probability p hp ρ (M x) (hM x) (Finset.mem_filter.mp hx).2
  have h := classical_posterior_bound_finset m hn S q (fun x _ => hq x) hsum
    (fun x => posterior p ρ (M x)) hb id
  have he := posterior_average_error p hp hs ρ M hM hsM id
  change (∑ x ∈ S, q x * (1 - posterior p ρ (M x) (id x))) =
    1 - successProbability p ρ M at he
  rw [he] at h
  exact h

omit [DecidableEq X] in
/-- A finite ensemble can be guessed perfectly exactly when a labelled POVM
has success one. This includes arbitrary signals at zero-prior labels. -/
theorem pGuess_one_iff_perfect_povm (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :
    pGuess p ρ = 1 ↔ ∃ M : X → Matrix B B ℂ, (∀ x, (M x).PosSemidef) ∧
      ∑ x, M x = 1 ∧ successProbability p ρ M = 1 := by
  constructor
  · intro h
    obtain ⟨M, hM, hsM, he⟩ := exists_optimal_povm p hp hs ρ
    exact ⟨M, hM, hsM, he.trans h⟩
  · rintro ⟨M, hM, hsM, he⟩
    have hb := pGuess_bounds p hp hs ρ
    exact le_antisymm hb.2.2.2.1 (le_csSup hb.2.1 ⟨M, hM, hsM, he.symm⟩)

/-- At error e, all signals are the same pure state and the priors are
1-e for one label and e/(n-1) for every other label. No unique maximizer is required. -/
def extremalPureEnsemble (m : ℕ) (p : X → ℝ) (ρ : X → DensityState B) (e : ℝ) : Prop :=
  ∃ (i : X) (u : B → ℂ) (hu : ∑ b, star (u b) * u b = 1),
    (∀ x, ρ x = pureSignal u hu) ∧ p i = 1 - e ∧ ∀ j, j ≠ i → p j = e / (m + 1 : ℕ)

theorem sharp_equality_iff_of_positive_error (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) (herr : 0 < 1 - pGuess p ρ) :
    conditionalSubentropy p hp hs ρ = phi m (1 - pGuess p ρ) ↔
      extremalPureEnsemble m p ρ (1 - pGuess p ρ) := by
  classical
  constructor
  · intro heq
    have hr := optimal_error_range m hn p hp hs ρ
    have hpos : 0 < conditionalSubentropy p hp hs ρ := by
      rw [heq, ← phi_zero m]
      exact phi_strictMono m ⟨le_rfl, (uniformError_mem m).1⟩ hr herr
    obtain ⟨M, hM, hsM, hopt⟩ := exists_optimal_povm p hp hs ρ
    have hupper := posteriorAverage_le_guessing_curve m hn p hp hs ρ M hM hsM
    rw [hopt, ← heq] at hupper
    have hpost := le_antisymm (measurement_posterior_comparison p hp hs ρ M hM hsM).2 hupper
    obtain ⟨u, hu, hρ⟩ := (positive_posterior_equality_iff p hp hs ρ M hM hsM hpos).mp hpost
    have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
    have hmax (x : X) := hi x (Finset.mem_univ x)
    have hg : pGuess p ρ = p i := (pGuess_congr_on_support p hp ρ _ hρ).trans
      (pGuess_identical p hp hs (pureSignal u hu) i hmax)
    have hc : conditionalSubentropy p hp hs ρ = classicalSubentropy p :=
      (conditional_congr_on_support p hp hs ρ _ hρ).trans (conditional_identical_pure p hp hs u hu)
    rw [hc, hg] at heq
    rw [hg] at herr ⊢
    have hall := positive_priors_of_map_equality m hn p ⟨hp, hs⟩ i hmax herr heq
    exact ⟨i, u, hu, fun x => hρ x (hall x), by ring,
      (classical_coordinate_eq_iff m hn p ⟨hp, hs⟩ i).mp heq⟩
  · rintro ⟨i, u, hu, hρ, hi, htail⟩
    have hc := (conditional_congr_on_support p hp hs ρ _ (fun x _ => hρ x)).trans
      (conditional_identical_pure p hp hs u hu)
    have he : 1 - p i = 1 - pGuess p ρ := by linarith
    rw [hc, ← he]
    exact (classical_coordinate_eq_iff m hn p ⟨hp, hs⟩ i).mpr
      (fun j hj => (htail j hj).trans (congrArg (fun t : ℝ => t / (m + 1 : ℕ)) he.symm))

/-- The zero-error endpoint and the positive-error family exhaust equality. -/
theorem sharp_discrimination_equality_iff (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :
    conditionalSubentropy p hp hs ρ = phi m (1 - pGuess p ρ) ↔
      pGuess p ρ = 1 ∨ extremalPureEnsemble m p ρ (1 - pGuess p ρ) := by
  by_cases h : pGuess p ρ = 1
  · have hb := optimal_discrimination_bound m hn p hp hs ρ
    have hz : conditionalSubentropy p hp hs ρ ≤ 0 := by
      simpa only [h, sub_self, phi_zero] using hb.2.1
    simp [h, phi_zero, le_antisymm hz hb.1]
  · have herr := sub_pos.mpr (lt_of_le_of_ne (pGuess_bounds p hp hs ρ).2.2.2.1 h)
    simpa only [h, false_or] using sharp_equality_iff_of_positive_error m hn p hp hs ρ herr

theorem inverse_discrimination_equality_iff (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :
    phiInverse m (conditionalSubentropy p hp hs ρ) (conditional_subentropy_range m hn p hp hs ρ) =
      1 - pGuess p ρ ↔ pGuess p ρ = 1 ∨ extremalPureEnsemble m p ρ (1 - pGuess p ρ) := by
  rw [← sharp_discrimination_equality_iff m hn p hp hs ρ]
  constructor
  · intro h
    rw [← h, phi_phiInverse]
  · intro h
    apply phi_preimage_unique m (phiInverse_mem m _ _) (optimal_error_range m hn p hp hs ρ)
    rw [phi_phiInverse, h]

end SubentropyCertificates.Discrimination
