module

public import ConditionalContinuity.Definitions
public import SubentropyCertificates.FixedMarginalContinuity

/-!
# Sharp trace-distance continuity bounds for conditional subentropy

The first four declarations specialize the companion proofs of Theorem 14 to finite block
matrices. The last five give Corollary 15 on each fixed quantum marginal.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open SubentropyCertificates.ConditionalContinuity

namespace SubentropyConditionalContinuity

variable {n m : ℕ}

theorem weighted_path_bound (ρ σ : CQState n m) :
    let d := traceDistance ρ σ
    let w := ∫ s in (0 : ℝ)..1, kappa ((1 - s) • marginal ρ + s • marginal σ)
    |conditionalSubentropy σ - conditionalSubentropy ρ| ≤ d * w ∧ d * w ≤ d := by
  have h := cq_path_bound ρ.block σ.block ρ.pos σ.pos ρ.trace_one σ.trace_one
  have weight (M : Matrix (Fin m) (Fin m) ℂ) :
      ‖SubentropyCertificates.ConditionalContinuity.spatialSign M‖ = kappa M := rfl
  simp only [blockSegment, Finset.sum_add_distrib, ← Finset.smul_sum, weight] at h
  exact h

theorem strict_global_bound (ρ σ : CQState n m) (h : joint ρ ≠ joint σ) :
    |conditionalSubentropy σ - conditionalSubentropy ρ| < traceDistance ρ σ := by
  apply cq_subentropy_lt_traceDistance ρ.block σ.block ρ.pos σ.pos ρ.trace_one σ.trace_one
  exact fun he ↦ h (congrArg (fun θ ↦ CStarMatrix.ofMatrix.symm θ.1) he)

theorem optimal_global_coefficient (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    IsLeast {c : ℝ | ∀ ρ σ : CQState n m,
      |conditionalSubentropy σ - conditionalSubentropy ρ| ≤ c * traceDistance ρ σ} 1 := by
  have h := cq_lipschitz_constant_isLeast (X := Fin n) (D := Fin m)
    (by simpa using hn) (by simpa using hm)
  refine ⟨fun ρ σ ↦ h.1 ρ.block σ.block ρ.pos σ.pos ρ.trace_one σ.trace_one, ?_⟩
  intro c hc
  exact h.2 (fun A B ha hb hA hB ↦ hc ⟨A, ha, hA⟩ ⟨B, hb, hB⟩)

theorem single_label (ρ : CQState 1 m) : conditionalSubentropy ρ = 0 := by
  exact blockConditionalQ_eq_zero_of_card_one ρ.block (Fintype.card_fin 1)

/-- The continuity bound on the states with prescribed marginal τ. -/
theorem fixed_marginal_bound (ρ σ : CQState n m) (τ : Matrix (Fin m) (Fin m) ℂ)
    (hρ : marginal ρ = τ) (hσ : marginal σ = τ) :
    |conditionalSubentropy σ - conditionalSubentropy ρ| ≤ kappa τ * traceDistance ρ σ := by
  exact cq_fixed_marginal_bound (Fin n) τ ρ.block σ.block ρ.pos σ.pos ρ.trace_one σ.trace_one hρ hσ

/-- The least coefficient on a fixed marginal, including a singular marginal. -/
theorem optimal_fixed_marginal_coefficient (n : ℕ) (hn : 2 ≤ n)
    (τ : Matrix (Fin m) (Fin m) ℂ) (hτ : τ.PosSemidef) (ht : τ.trace = 1) :
    IsLeast {c : ℝ | ∀ ρ σ : CQState n m, marginal ρ = τ → marginal σ = τ →
      |conditionalSubentropy σ - conditionalSubentropy ρ| ≤ c * traceDistance ρ σ} (kappa τ) := by
  refine ⟨fun ρ σ hρ hσ ↦ fixed_marginal_bound ρ σ τ hρ hσ, ?_⟩
  intro c hc
  have hleast := (cq_fixed_marginal_continuity (Fin n) hτ ht).2.1 (by simpa using hn)
  apply hleast.2
  intro A B ha hb hta htb hA hB
  exact hc ⟨A, ha, hta⟩ ⟨B, hb, htb⟩ hA hB

/-- The maximally mixed marginal has coefficient 1/m. -/
theorem kappa_maximally_mixed (m : ℕ) (hm : 1 ≤ m) :
    kappa ((1 / (m : ℂ)) • (1 : Matrix (Fin m) (Fin m) ℂ)) = 1 / (m : ℝ) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  change ‖SubentropyCertificates.ConditionalContinuity.spatialSign _‖ = _
  simpa only [SubentropyCertificates.SpectralContinuity.maximallyMixed_matrix, Fintype.card_fin]
    using spatialSign_norm_maximallyMixed (Fin m)

/-- A pure marginal has coefficient one. -/
theorem kappa_pure (τ : Matrix (Fin m) (Fin m) ℂ) (hτ : τ.PosSemidef) (ht : τ.trace = 1)
    (hp : τ.rank = 1) : kappa τ = 1 := by
  exact (cq_fixed_marginal_continuity (Fin 2) hτ ht).2.2.2.1 hp

/-- A mixed marginal has coefficient strictly less than one. -/
theorem kappa_mixed (τ : Matrix (Fin m) (Fin m) ℂ) (hτ : τ.PosSemidef) (ht : τ.trace = 1)
    (hmix : 1 < τ.rank) : kappa τ < 1 := by
  exact (cq_fixed_marginal_continuity (Fin 2) hτ ht).2.2.2.2 hmix

end SubentropyConditionalContinuity
