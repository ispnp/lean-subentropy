module

public import SubentropyCertificates.QuantumModulus
public import SubentropyCertificates.TraceDistanceContinuity
public import SubentropyCertificates.LinearDiscrimination

/-! Theorem 13 at radius zero and the strict, optimal trace-distance Lipschitz bound. -/
@[expose] public section
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.InputInformationBalance (IsPure)
open D5.S3.Quantum.Subentropy.Basic
open SubentropyCertificates.BinarySpectra (densityMatrix)
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.CompactStability (traceDistance_nonneg traceDistance_self)
open SubentropyCertificates.Continuity (modulus_lt_radius)
open SubentropyCertificates.Discrimination (smaller_coefficient_fails_near_zero)
open SubentropyCertificates.MixedQubit (traceDistance)

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Trace distance vanishes exactly when the two states coincide. -/
theorem traceDistance_eq_zero_iff (ρ σ : DensityState D) :
    traceDistance ρ σ = 0 ↔ ρ = σ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ traceDistance_self σ⟩
  let H := (density_posSemidef ρ).isHermitian.sub (density_posSemidef σ).isHermitian
  change (∑ i, |H.eigenvalues i|) / 2 = 0 at h
  have hsum : ∑ i, |H.eigenvalues i| = 0 := by linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ abs_nonneg (H.eigenvalues i))).mp hsum
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  have he : H.eigenvalues = 0 := funext fun i ↦ abs_eq_zero.mp (hz i (by simp))
  exact sub_eq_zero.mp (H.eigenvalues_eq_zero_iff.mp he)

/-- In the closed ball of radius zero the maximizing pairs are precisely the identical pairs. -/
theorem quantum_modulus_zero_eq_iff (ρ σ : DensityState D) :
    (traceDistance ρ σ ≤ 0 ∧ |subentropy ρ - subentropy σ| = sSup (quantumDifferences D 0)) ↔
      ρ = σ := by
  have eq_of_ball (a b : DensityState D) (h : traceDistance a b ≤ 0) : a = b :=
    (traceDistance_eq_zero_iff a b).mp (le_antisymm h (traceDistance_nonneg a b))
  refine ⟨fun h ↦ eq_of_ball ρ σ h.1, ?_⟩
  rintro rfl
  have zero : IsGreatest (quantumDifferences D 0) 0 := by
    refine ⟨⟨ρ, ρ, (traceDistance_self ρ).le, by simp⟩, ?_⟩
    rintro _ ⟨a, b, hd, rfl⟩
    simp [eq_of_ball a b hd]
  simp [traceDistance_self, zero.csSup_eq]

/-- On a space of dimension at most one, all density states coincide. -/
theorem densityState_eq_of_card_le_one (hd : Fintype.card D ≤ 1) (ρ σ : DensityState D) :
    ρ = σ := by
  have : Subsingleton D := Fintype.card_le_one_iff_subsingleton.mp hd
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext i j
  rw [Subsingleton.elim j i]
  have entry (τ : DensityState D) : densityMatrix τ i i = 1 := by
    have ht : (densityMatrix τ).trace = 1 := τ.2.2
    change ∑ j, densityMatrix τ j j = 1 at ht
    rwa [Finset.sum_eq_single i (fun j _ hj ↦ (hj (Subsingleton.elim j i)).elim)
      (fun h ↦ (h (Finset.mem_univ i)).elim)] at ht
  exact (entry ρ).trans (entry σ).symm

/-- Distinct density states have subentropy gap strictly below their trace distance. -/
theorem subentropy_lt_traceDistance (ρ σ : DensityState D) (hne : ρ ≠ σ) :
    |subentropy ρ - subentropy σ| < traceDistance ρ σ := by
  have hpos := lt_of_le_of_ne (traceDistance_nonneg ρ σ) (fun h ↦
    hne ((traceDistance_eq_zero_iff ρ σ).mp h.symm))
  have hd : 2 ≤ Fintype.card D := by
    by_contra! h
    exact hne (densityState_eq_of_card_le_one (by omega) ρ σ)
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card D = m + 2 := ⟨Fintype.card D - 2, by omega⟩
  apply (quantum_continuity_upper ρ σ le_rfl).trans_lt
  rw [hm]
  exact modulus_lt_radius m hpos

/-- The coefficient-one Lipschitz inequality in all finite dimensions. -/
theorem subentropy_le_traceDistance (ρ σ : DensityState D) :
    |subentropy ρ - subentropy σ| ≤ traceDistance ρ σ := by
  by_cases h : ρ = σ
  · simp [h, traceDistance_self]
  · exact (subentropy_lt_traceDistance ρ σ h).le

/-- Every smaller coefficient fails at arbitrarily small positive distance in each fixed
dimension at least two, already for a pure state and a commuting diagonal state. -/
theorem quantum_lipschitz_sharp_near_zero (hd : 2 ≤ Fintype.card D) {c ε : ℝ}
    (hc : c < 1) (hε : 0 < ε) :
    ∃ ρ σ : DensityState D, IsPure σ ∧ Commute (densityMatrix ρ) (densityMatrix σ) ∧
      0 < traceDistance ρ σ ∧ traceDistance ρ σ < ε ∧
      c * traceDistance ρ σ < |subentropy ρ - subentropy σ| := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card D = m + 2 := ⟨Fintype.card D - 2, by omega⟩
  let e : D ≃ Option (Fin (m + 1)) := Fintype.equivOfCardEq (by simp [hm, Nat.add_assoc])
  obtain ⟨u, hu, hεu, hub, hgap⟩ := smaller_coefficient_fails_near_zero m hc hε
  have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.le, hub.trans (uniformError_mem m).2⟩
  obtain ⟨hp, hcomm, hdist, hdiff⟩ := extremal_diagonal_pair e hu1
  refine ⟨extremalDiagonal e u hu1, coordinatePure e, hp, hcomm, ?_⟩
  rw [hdist, hdiff]
  exact ⟨hu, hεu, hgap.trans_le (le_abs_self _)⟩

/-- One is the least Lipschitz coefficient in every fixed dimension at least two. -/
theorem quantum_lipschitz_constant_isLeast (hd : 2 ≤ Fintype.card D) :
    IsLeast {c : ℝ | ∀ ρ σ : DensityState D,
      |subentropy ρ - subentropy σ| ≤ c * traceDistance ρ σ} 1 := by
  refine ⟨fun ρ σ ↦ by simpa using subentropy_le_traceDistance ρ σ, ?_⟩
  intro c hc
  by_contra! h
  obtain ⟨ρ, σ, _, _, _, _, hfail⟩ :=
    quantum_lipschitz_sharp_near_zero hd h (by norm_num : 0 < (1 : ℝ))
  exact hfail.not_ge (hc ρ σ)

/-- The least coefficient uniform over all finite dimensions is one. -/
theorem quantum_lipschitz_universal_isLeast :
    IsLeast {c : ℝ | ∀ d : ℕ, ∀ ρ σ : DensityState (Fin d),
      |subentropy ρ - subentropy σ| ≤ c * traceDistance ρ σ} 1 := by
  refine ⟨fun _ ρ σ ↦ by simpa using subentropy_le_traceDistance ρ σ, ?_⟩
  intro c hc
  exact (quantum_lipschitz_constant_isLeast (D := Fin 2) (by decide)).2 (hc 2)

end SubentropyCertificates.SpectralContinuity
