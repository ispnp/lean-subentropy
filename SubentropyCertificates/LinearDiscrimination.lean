module

public import SubentropyCertificates.CurveTangent
public import SubentropyCertificates.IdenticalPureSignals

/-! Strictness and optimality of the linear discrimination bound. The
sharpness witnesses are extremal ensembles at arbitrarily small positive error
with the number of labels and signal dimension both fixed. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology
namespace SubentropyCertificates.Discrimination
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.ClassicalCurve

theorem smaller_coefficient_fails_near_zero (m : ℕ) {c δ : ℝ} (hc : c < 1) (hδ : 0 < δ) :
    ∃ e : ℝ, 0 < e ∧ e < δ ∧ e ≤ uniformError m ∧ c * e < phi m e := by
  have hn : (1 : ℝ) < (m + 2 : ℕ) := by exact_mod_cast (by omega : 1 < m + 2)
  have hu : 0 < uniformError m := sub_pos.mpr ((div_lt_one (by positivity)).mpr hn)
  have hnear : ∀ᶠ e : ℝ in 𝓝[>] 0, e ∈ Ioo 0 (min δ (uniformError m)) :=
    Ioo_mem_nhdsGT_of_mem ⟨le_rfl, lt_min hδ hu⟩
  have hratio : ∀ᶠ e : ℝ in 𝓝[>] 0, c < phi m e / e :=
    (phi_div_error_tendsto_one m) (Ioi_mem_nhds hc)
  obtain ⟨e, he, hr⟩ := (hnear.and hratio).exists
  exact ⟨e, he.1, (lt_min_iff.mp he.2).1, (lt_min_iff.mp he.2).2.le, (lt_div_iff₀ he.1).mp hr⟩

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

theorem conditional_lt_positive_error (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (ρ : X → DensityState B)
    (he : 0 < 1 - pGuess p ρ) : conditionalSubentropy p hp hs ρ < 1 - pGuess p ρ := by
  have hb := optimal_discrimination_bound m hn p hp hs ρ
  exact hb.2.1.trans_lt (phi_lt_error m he (hb.2.2.2.trans (uniformError_mem m).2))

/-- Every coefficient below one fails in every positive neighborhood of zero,
even when the label count and a nonempty signal space are prescribed. -/
theorem ensemble_violating_smaller_coefficient [Nonempty B]
    (m : ℕ) {c δ : ℝ} (hc : c < 1) (hδ : 0 < δ) :
    ∃ (p : Option (Fin (m + 1)) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
      (ρ : Option (Fin (m + 1)) → DensityState B),
      0 < 1 - pGuess p ρ ∧ 1 - pGuess p ρ < δ ∧
        c * (1 - pGuess p ρ) < conditionalSubentropy p hp hs ρ := by
  obtain ⟨e, he, hsmall, hadm, hratio⟩ := smaller_coefficient_fails_near_zero m hc hδ
  obtain ⟨p, hp, hs, ρ, herror, hcurve⟩ := curve_attainable_in_dimension (B := B) m e ⟨he.le, hadm⟩
  exact ⟨p, hp, hs, ρ, by rwa [herror], by rwa [herror], by rwa [herror, hcurve]⟩

theorem universal_linear_coefficient_iff [Nonempty B] (m : ℕ) (c : ℝ) :
    (∀ (p : Option (Fin (m + 1)) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
      (ρ : Option (Fin (m + 1)) → DensityState B),
      conditionalSubentropy p hp hs ρ ≤ c * (1 - pGuess p ρ)) ↔ 1 ≤ c := by
  constructor
  · intro h
    by_contra! hc
    obtain ⟨p, hp, hs, ρ, _, _, hlt⟩ :=
      ensemble_violating_smaller_coefficient (B := B) m hc zero_lt_one
    exact (h p hp hs ρ).not_gt hlt
  · intro hc p hp hs ρ
    have hn : Fintype.card (Option (Fin (m + 1))) = m + 2 := by simp [Nat.add_assoc]
    have hb := optimal_discrimination_bound m hn p hp hs ρ
    have he := hb.2.2.1
    have hlin : phi m (1 - pGuess p ρ) ≤ 1 - pGuess p ρ := by
      rcases he.eq_or_lt with hz | hpos
      · rw [← hz, phi_zero]
      · exact (phi_lt_error m hpos (hb.2.2.2.trans (uniformError_mem m).2)).le
    exact (hb.2.1.trans hlin).trans (le_mul_of_one_le_left he hc)

end SubentropyCertificates.Discrimination
