module

public import SubentropyCertificates.LinearDiscrimination
public import SubentropyCertificates.ZeroConditional

/-! The manuscript's Sharp guessing bound (thm:guess). With n=m+2 labels the
paper's curve is `phi m` and its error endpoint is `uniformError m`.
The final theorem also states the one-label conclusion. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped BigOperators
namespace SubentropyCertificates.Discrimination
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.ZeroConditional

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

/-- The original ensemble supplies e and q in the paper theorem below.
Attainment and optimality quantify over other ensembles on the same spaces. -/
structure SharpGuessingConclusion (m : ℕ) (p : X → ℝ) (ρ : X → DensityState B)
    (e q : ℝ) : Prop where
  error_range : e ∈ Icc 0 (uniformError m)
  bounds : 0 ≤ q ∧ q ≤ phi m e ∧ phi m e ≤ e ∧ e ≤ -Real.log (pGuess p ρ)
  attainable : ∀ r ∈ Icc 0 (uniformError m),
    ∃ (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hsw : ∑ x, w x = 1) (σ : X → DensityState B),
      1 - pGuess w σ = r ∧ conditionalSubentropy w hw hsw σ = phi m r
  positive_equality : 0 < e → (q = phi m e ↔ extremalPureEnsemble m p ρ e)
  zero_conditional : q = 0 ↔ e = 0
  zero_error : e = 0 ↔ orthogonalSupports p ρ
  strict_tangent : 0 < e → phi m e < e
  optimal_coefficient : ∀ c : ℝ,
    (∀ (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hsw : ∑ x, w x = 1) (σ : X → DensityState B),
      conditionalSubentropy w hw hsw σ ≤ c * (1 - pGuess w σ)) ↔ 1 ≤ c

/-- Relabel the attaining identical-pure ensemble onto any given n-element
label type X. The signal dimension is also fixed. -/
theorem curve_attainable_on_labels [Nonempty B] (m : ℕ) (hn : Fintype.card X = m + 2)
    (r : ℝ) (hr : r ∈ Icc 0 (uniformError m)) :
    ∃ (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (ρ : X → DensityState B),
      1 - pGuess p ρ = r ∧ conditionalSubentropy p hp hs ρ = phi m r := by
  classical
  let f : X ≃ Option (Fin (m + 1)) := Fintype.equivOfCardEq (by simp [hn, Nat.add_assoc])
  let w := extremalVector m r ∘ f
  have hw := simplex_reindex _ (extremal_probability_admissible m hr) f
  let i := f.symm none
  have hi : w i = 1 - r := by simp [w, i, extremalVector]
  have hmax (x : X) : w x ≤ w i := by
    simpa only [w, i, Function.comp_apply, Equiv.apply_symm_apply] using
      extremal_none_largest m hr (f x)
  let b₀ : B := Classical.arbitrary B
  let v (b : B) : ℂ := if b = b₀ then 1 else 0
  have hv : ∑ b, star (v b) * v b = 1 := by simp [v]
  refine ⟨w, hw.1, hw.2, fun _ => pureSignal v hv, ?_, ?_⟩
  · rw [pGuess_identical w hw.1 hw.2 (pureSignal v hv) i hmax, hi]
    ring
  · exact (conditional_identical_pure w hw.1 hw.2 v hv).trans
      (classical_subentropy_reindex (extremalVector m r) f)

theorem single_label_guessing (hn : Fintype.card X = 1)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :
    1 - pGuess p ρ = 0 ∧ conditionalSubentropy p hp hs ρ = 0 := by
  have horth : orthogonalSupports p ρ := fun x y hxy =>
    (hxy (Fintype.card_le_one_iff.mp hn.le x y)).elim
  have hz := zero_conditional_equivalences p hp hs ρ
  have hone := hz.2.1.mpr horth
  exact ⟨sub_eq_zero.mpr hone.symm, hz.1.mpr hone⟩

private theorem curve_le_its_error (m : ℕ) {e : ℝ} (he : e ∈ Icc 0 (uniformError m)) :
    phi m e ≤ e := by
  rcases he.1.eq_or_lt with hz | hpos
  · rw [← hz, phi_zero]
  · exact (phi_lt_error m hpos (he.2.trans (uniformError_mem m).2)).le

/-- The Sharp guessing bound, including all equality, optimality and boundary
clauses, for any finite normalized ensemble. For two or more labels the named
fields of `SharpGuessingConclusion` follow the order of the paper. -/
theorem sharp_guessing_bound (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) :
    let n := Fintype.card X
    let e := 1 - pGuess p ρ
    let q := conditionalSubentropy p hp hs ρ
    (2 ≤ n → SharpGuessingConclusion (n - 2) p ρ e q) ∧ (n = 1 → e = 0 ∧ q = 0) := by
  refine ⟨?_, fun hn => single_label_guessing hn p hp hs ρ⟩
  intro hn
  let m := Fintype.card X - 2
  have hcard : Fintype.card X = m + 2 := by dsimp [m]; omega
  have hX : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty B := by
    by_contra h
    have : IsEmpty B := not_nonempty_iff.mp h
    have ht := (ρ (Classical.choice hX)).2.2
    simp [Matrix.trace] at ht
  have hb := optimal_discrimination_bound m hcard p hp hs ρ
  have hz := zero_conditional_equivalences p hp hs ρ
  have he0 : 1 - pGuess p ρ = 0 ↔ pGuess p ρ = 1 := sub_eq_zero.trans eq_comm
  refine {
    error_range := hb.2.2
    bounds := ⟨hb.1, hb.2.1, curve_le_its_error m hb.2.2, (pGuess_bounds p hp hs ρ).2.2.2.2.1⟩
    attainable := curve_attainable_on_labels m hcard
    positive_equality := sharp_equality_iff_of_positive_error m hcard p hp hs ρ
    zero_conditional := hz.1.trans he0.symm
    zero_error := he0.trans hz.2.1
    strict_tangent := fun h => phi_lt_error m h (hb.2.2.2.trans (uniformError_mem m).2)
    optimal_coefficient := ?_ }
  intro c
  constructor
  · intro hall
    by_contra! hc
    obtain ⟨r, hr, _, hadm, hlt⟩ := smaller_coefficient_fails_near_zero m hc zero_lt_one
    obtain ⟨w, hw, hsw, σ, he, hq⟩ := curve_attainable_on_labels (X := X) (B := B)
      m hcard r ⟨hr.le, hadm⟩
    have h := hall w hw hsw σ
    rw [he, hq] at h
    exact h.not_gt hlt
  · intro hc w hw hsw σ
    have h := optimal_discrimination_bound m hcard w hw hsw σ
    exact (h.2.1.trans (curve_le_its_error m h.2.2)).trans (le_mul_of_one_le_left h.2.2.1 hc)

end SubentropyCertificates.Discrimination
