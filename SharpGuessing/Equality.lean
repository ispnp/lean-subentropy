module

public import SharpGuessing.Curve
public import SubentropyCertificates.SharpDiscriminationEquality
public import SubentropyCertificates.ZeroConditional

/-! Equality in the guessing bound, for positive error and for perfect discrimination. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)

namespace SubentropySharpGuessing

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

/-- At positive error the priors have one distinguished coordinate and every signal
is the same rank-one projector. -/
theorem positive_error_equality (hn : 2 ≤ n) (E : Ensemble n B) (he : 0 < error E) :
    conditionalSubentropy E = phi n (error E) ↔
      (∃ k : Fin n, E.prior = extremalPrior n k.val (error E)) ∧
      ∃ v : B → ℂ, (∑ b, star (v b) * v b) = 1 ∧
        ∀ x, E.signal x = Matrix.vecMulVec v (star v) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have herr : error E = 1 - D5.S3.Quantum.Subentropy.GuessingProbability.pGuess
      E.prior (toSignal E) := by rw [error, pGuess_bridge]
  have h := SubentropyCertificates.Discrimination.sharp_equality_iff_of_positive_error m
    (Fintype.card_fin _) E.prior E.prior_nonneg E.prior_sum (toSignal E) (herr ▸ he)
  rw [← herr, ← conditional_bridge E, ← phi_bridge] at h
  refine h.trans ?_
  have hd : ((m + 2 : ℕ) : ℝ) - 1 = (m + 1 : ℕ) := by push_cast; ring
  constructor
  · rintro ⟨k, v, hv, signals, hk, others⟩
    refine ⟨⟨k, funext fun x ↦ ?_⟩, v, hv, fun x ↦ ?_⟩
    · by_cases hx : x = k
      · subst x
        simpa [extremalPrior] using hk
      · have hval : x.val ≠ k.val := fun hval ↦ hx (Fin.ext hval)
        simpa only [extremalPrior, ite_eq_right hval, hd] using others x hx
    · exact congrArg (fun s : DensityState B ↦ CStarMatrix.ofMatrix.symm s.1) (signals x)
  · rintro ⟨⟨k, hp⟩, v, hv, signals⟩
    refine ⟨k, v, hv, fun x ↦ ?_, ?_, fun j hj ↦ ?_⟩
    · apply Subtype.ext
      exact congrArg CStarMatrix.ofMatrix (signals x)
    · simpa [extremalPrior] using congrFun hp k
    · have hval : j.val ≠ k.val := fun hval ↦ hj (Fin.ext hval)
      simpa only [extremalPrior, ite_eq_right hval, hd] using congrFun hp j

/-- At zero error, only the supports of positive-prior signals matter. -/
theorem zero_error_equality (_hn : 2 ≤ n) (E : Ensemble n B) :
    (conditionalSubentropy E = 0 ↔ error E = 0) ∧ (error E = 0 ↔ orthogonalSupports E) := by
  have h := SubentropyCertificates.ZeroConditional.zero_conditional_equivalences
    E.prior E.prior_nonneg E.prior_sum (toSignal E)
  rw [conditional_bridge E, error, pGuess_bridge E, sub_eq_zero, eq_comm (a := 1),
    orthogonal_bridge E]
  exact ⟨h.1, h.2.1⟩

end SubentropySharpGuessing
