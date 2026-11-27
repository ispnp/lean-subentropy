module

public import SubentropyCertificates.PureUniformDistance

/-! Theorem 13, plateau equality. A difference spanning the full range of subentropy
forces its two arguments to be a minimizer and a maximizer. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.InputInformationBalance (IsPure)
open D5.S3.Quantum.Subentropy.Basic
open SubentropyCertificates.QuantumEquality
open SubentropyCertificates.Subadditivity (subentropy_nonnegative subentropy_zero_iff_pure)
open SubentropyCertificates.MixedQubit (traceDistance)

variable {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]

private theorem full_gap (ρ σ : DensityState D) :
    |subentropy ρ - subentropy σ| ≤ subentropy (maximallyMixed D) ∧
    (|subentropy ρ - subentropy σ| = subentropy (maximallyMixed D) ↔
      (IsPure ρ ∧ σ = maximallyMixed D) ∨ (ρ = maximallyMixed D ∧ IsPure σ)) := by
  obtain ⟨hr, er⟩ := subentropy_maximum_iff ρ
  obtain ⟨hs, es⟩ := subentropy_maximum_iff σ
  have hr0 := subentropy_nonnegative ρ
  have hs0 := subentropy_nonnegative σ
  have hu := subentropy_nonnegative (maximallyMixed D)
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  constructor
  · intro h
    rcases le_total (subentropy ρ) (subentropy σ) with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h
      exact Or.inl ⟨(subentropy_zero_iff_pure ρ).mp (by linarith), es.mp (by linarith)⟩
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at h
      exact Or.inr ⟨er.mp (by linarith), (subentropy_zero_iff_pure σ).mp (by linarith)⟩
  · rintro (⟨hρ, rfl⟩ | ⟨rfl, hσ⟩)
    · simp [(subentropy_zero_iff_pure ρ).mpr hρ, abs_of_nonneg hu]
    · simp [(subentropy_zero_iff_pure σ).mpr hσ, abs_of_nonneg hu]

private theorem plateau_supremum {δ : ℝ} (hδ : 1 - 1 / (Fintype.card D : ℝ) ≤ δ) :
    sSup (quantumDifferences D δ) = subentropy (maximallyMixed D) := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · let i : D := Classical.choice ‹Nonempty D›
    let τ := diagonalDensity (pointMass i) (pointMass_probability i)
    have ht : IsPure τ := (subentropy_zero_iff_pure τ).mp (pointMass_subentropy i)
    exact ⟨τ, maximallyMixed D, (pure_uniform_traceDistance τ ht).1.le.trans hδ,
      ((full_gap τ _).2.mpr (Or.inl ⟨ht, rfl⟩)).symm⟩
  · rintro v ⟨ρ, σ, _, rfl⟩
    exact (full_gap ρ σ).1

/-- A pair attains the maximum on a plateau ball exactly when it consists, in either
order, of a pure state and I/d. Feasibility is part of the equivalence. -/
theorem quantum_modulus_plateau_eq_iff (ρ σ : DensityState D) {δ : ℝ}
    (hδ : 1 - 1 / (Fintype.card D : ℝ) ≤ δ) :
    (traceDistance ρ σ ≤ δ ∧ |subentropy ρ - subentropy σ| = sSup (quantumDifferences D δ)) ↔
      (IsPure ρ ∧ σ = maximallyMixed D) ∨ (ρ = maximallyMixed D ∧ IsPure σ) := by
  rw [plateau_supremum hδ, (full_gap ρ σ).2]
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  rcases h with ⟨hρ, rfl⟩ | ⟨rfl, hσ⟩
  · exact (pure_uniform_traceDistance ρ hρ).1.le.trans hδ
  · exact (pure_uniform_traceDistance σ hσ).2.le.trans hδ

end SubentropyCertificates.SpectralContinuity
