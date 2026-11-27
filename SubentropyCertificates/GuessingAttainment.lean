module

public import SubentropyCertificates.OptimalGuessing
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Compactness of labelled POVMs and attainment of the finite guessing probability. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.Discrimination
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.GuessingProbability

variable {X B : Type*} [Fintype X] [Fintype B] [DecidableEq B]

theorem isCompact_effect_interval :
    IsCompact (Icc (0 : Matrix B B ℂ) 1) := by
  let := FiniteDimensional.proper ℂ (Matrix B B ℂ)
  apply (isCompact_closedBall (0 : Matrix B B ℂ) 1).of_isClosed_subset isClosed_Icc
  intro A hA
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (CStarAlgebra.norm_le_one_iff_of_nonneg A hA.1).2 hA.2

theorem isCompact_labelled_povms :
    IsCompact {M : X → Matrix B B ℂ | (∀ x, (M x).PosSemidef) ∧ ∑ x, M x = 1} := by
  have hc := isCompact_pi_infinite (fun _ : X => isCompact_effect_interval (B := B))
  apply hc.of_isClosed_subset
  · apply IsClosed.inter
    · change IsClosed {M : X → Matrix B B ℂ | ∀ x, (M x).PosSemidef}
      rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro x
      simpa only [← Matrix.nonneg_iff_posSemidef] using
        (isClosed_le continuous_const (continuous_apply x) :
          IsClosed {M : X → Matrix B B ℂ | 0 ≤ M x})
    · exact isClosed_eq (by fun_prop) continuous_const
  · intro M hM x
    refine ⟨(hM.1 x).nonneg, ?_⟩
    rw [← hM.2]
    exact Finset.single_le_sum (fun y _ => (hM.1 y).nonneg) (Finset.mem_univ x)

theorem successProbabilitySet_isCompact (p : X → ℝ) (ρ : X → DensityState B) :
    IsCompact (successProbabilitySet p ρ) := by
  have hc : Continuous (successProbability p ρ) := by
    unfold successProbability
    fun_prop
  convert (isCompact_labelled_povms (X := X) (B := B)).image hc using 1
  ext a
  constructor
  · rintro ⟨M, hM, hsM, rfl⟩
    exact ⟨M, ⟨hM, hsM⟩, rfl⟩
  · rintro ⟨M, ⟨hM, hsM⟩, rfl⟩
    exact ⟨M, hM, hsM, rfl⟩

theorem exists_optimal_povm (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) :
    ∃ M : X → Matrix B B ℂ, (∀ x, (M x).PosSemidef) ∧ ∑ x, M x = 1 ∧
      successProbability p ρ M = pGuess p ρ := by
  obtain ⟨M, hM, hsM, he⟩ :=
    (successProbabilitySet_isCompact p ρ).sSup_mem (pGuess_bounds p hp hs ρ).1
  exact ⟨M, hM, hsM, he.symm⟩

theorem pGuess_congr_on_support (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ σ : X → DensityState B) (h : ∀ x, 0 < p x → ρ x = σ x) :
    pGuess p ρ = pGuess p σ := by
  have he (M : X → Matrix B B ℂ) : successProbability p ρ M = successProbability p σ M := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hz : p x = 0
    · simp [hz]
    · rw [h x (lt_of_le_of_ne (hp x) (Ne.symm hz))]
  unfold pGuess
  congr 1
  ext a
  simp only [successProbabilitySet, mem_ofPred_eq, he]

end SubentropyCertificates.Discrimination
