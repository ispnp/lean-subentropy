module

public import SharpGuessing.Equality
public import SubentropyCertificates.SharpGuessingBound

/-!
# The sharp guessing bound and its optimal inverse

The curve and the equality cases are proved in `SharpGuessing.Curve` and `SharpGuessing.Equality`.
Together with the declarations below, they give the nine statements of the challenge.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set SubentropyCertificates D5.S3.Quantum.Subentropy

namespace SubentropySharpGuessing

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

theorem sharp_guessing_bound (hn : 2 ≤ n) (E : Ensemble n B) :
    let e := error E
    let q := conditionalSubentropy E
    IsGreatest (successProbabilities E) (pGuess E) ∧ e ∈ Icc 0 (maxError n) ∧
      0 ≤ q ∧ q ≤ phi n e ∧ phi n e ≤ e ∧ e ≤ -Real.log (pGuess E) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have spec := (Discrimination.sharp_guessing_bound E.prior E.prior_nonneg E.prior_sum
    (toSignal E)).1 (by simp)
  have bounds := GuessingProbability.pGuess_bounds E.prior E.prior_nonneg E.prior_sum (toSignal E)
  have compact := Discrimination.successProbabilitySet_isCompact E.prior (toSignal E)
  refine ⟨?_, ?_, ?_⟩
  · rw [successProbabilities_bridge, pGuess_bridge]
    exact ⟨compact.sSup_mem bounds.1, fun _ ha ↦ le_csSup bounds.2.1 ha⟩
  · simpa only [error, pGuess_bridge, maxError_bridge, Fintype.card_fin, Nat.add_sub_cancel]
      using spec.error_range
  · simpa only [error, pGuess_bridge, conditional_bridge, phi_bridge, Fintype.card_fin,
      Nat.add_sub_cancel] using spec.bounds

theorem curve_attainable (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B]
    (hn : 2 ≤ n) (e : ℝ) (he : e ∈ Icc 0 (maxError n)) :
    ∃ E : Ensemble n B, error E = e ∧ conditionalSubentropy E = phi n e := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨p, hp, hs, ρ, herr, hq⟩ := Discrimination.curve_attainable_on_labels
    (X := Fin (m + 2)) (B := B) m (Fintype.card_fin _) e (by rwa [← maxError_bridge])
  refine ⟨fromSignals p hp hs ρ, ?_, ?_⟩
  · simpa only [error, fromSignals_pGuess] using herr
  · simpa only [fromSignals_conditional, phi_bridge] using hq

theorem optimal_linear_coefficient (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B]
    (hn : 2 ≤ n) (c : ℝ) :
    (∀ E : Ensemble n B, conditionalSubentropy E ≤ c * error E) ↔ 1 ≤ c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  constructor
  · intro hall
    by_contra! hc
    obtain ⟨e, hpos, _, hmax, hlt⟩ :=
      Discrimination.smaller_coefficient_fails_near_zero m hc zero_lt_one
    obtain ⟨E, he, hq⟩ := curve_attainable B hn e ⟨hpos.le, by rwa [maxError_bridge]⟩
    have h := hall E
    rw [he, hq, phi_bridge] at h
    exact h.not_gt hlt
  · intro hc E
    obtain ⟨_, ⟨he, _⟩, _, hq, hlin, _⟩ := sharp_guessing_bound hn E
    exact (hq.trans hlin).trans (le_mul_of_one_le_left he hc)

theorem single_label (E : Ensemble 1 B) : error E = 0 ∧ conditionalSubentropy E = 0 := by
  simpa only [error, pGuess_bridge, conditional_bridge] using
    Discrimination.single_label_guessing (Fintype.card_fin 1) E.prior E.prior_nonneg
      E.prior_sum (toSignal E)

theorem optimal_inverse_bound (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B]
    (hn : 2 ≤ n) :
    (∀ E : Ensemble n B, conditionalSubentropy E ∈ Icc 0 (phi n (maxError n)) ∧
      phiInverse n (conditionalSubentropy E) ≤ error E) ∧
    ∀ q ∈ Icc 0 (phi n (maxError n)),
      IsLeast {r : ℝ | ∃ E : Ensemble n B, conditionalSubentropy E = q ∧ error E = r}
        (phiInverse n q) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have lower (E : Ensemble (m + 2) B) :
      conditionalSubentropy E ∈ Icc 0 (phi (m + 2) (maxError (m + 2))) ∧
      phiInverse (m + 2) (conditionalSubentropy E) ≤ error E := by
    have range := Discrimination.conditional_subentropy_range m (Fintype.card_fin _)
      E.prior E.prior_nonneg E.prior_sum (toSignal E)
    have bound := Discrimination.inverse_discrimination_bound m (Fintype.card_fin _)
      E.prior E.prior_nonneg E.prior_sum (toSignal E)
    rw [conditional_bridge, error, pGuess_bridge, inverse_bridge m _ range]
    exact ⟨by simpa only [Discrimination.curveRange, maxError_bridge, phi_bridge] using range,
      bound⟩
  refine ⟨lower, fun q hq ↦ ?_⟩
  obtain ⟨hmem, hphi⟩ := (inverse_on_branch hn).2.2.2 q hq
  obtain ⟨E, he, hE⟩ := curve_attainable B hn _ hmem
  exact ⟨⟨E, hE.trans hphi, he⟩, fun _ ⟨F, hF, hr⟩ ↦ hF ▸ hr ▸ (lower F).2⟩

end SubentropySharpGuessing
