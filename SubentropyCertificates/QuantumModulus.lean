module

public import SubentropyCertificates.DiagonalTraceDistance

/-! The attained quantum modulus of Theorem 13. Before the uniform endpoint the
explicit pair has distance equal to the prescribed radius. On the plateau the
same pure and maximally mixed states continue to attain the maximum. -/
@[expose] public section
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.InputInformationBalance (IsPure)
open D5.S3.Quantum.Subentropy.Basic
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Continuity
open SubentropyCertificates.BinarySpectra (densityMatrix)
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.QuantumEquality
open SubentropyCertificates.Subadditivity (subentropy_zero_iff_pure)

variable {D : Type*} [Fintype D] [DecidableEq D] {m : ℕ}

/-- A diagonal state with weight 1-u at the distinguished coordinate and equal
weight u/(d-1) at all other coordinates. The equivalence specifies that coordinate. -/
def extremalDiagonal (e : D ≃ Option (Fin (m + 1))) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    DensityState D :=
  diagonalDensity (extremalVector m u ∘ e) (simplex_reindex _ (extremal_probability m hu) e)

/-- The coordinate pure state at the distinguished label of e. -/
def coordinatePure (e : D ≃ Option (Fin (m + 1))) : DensityState D :=
  extremalDiagonal e 0 ⟨le_rfl, zero_le_one⟩

theorem extremalDiagonal_subentropy (e : D ≃ Option (Fin (m + 1)))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : subentropy (extremalDiagonal e u hu) = phi m u :=
  classical_subentropy_reindex (extremalVector m u) e

/-- Both members are diagonal in the same basis. Their actual trace distance is u
and their signed subentropy difference is exactly the curve value. -/
theorem extremal_diagonal_pair (e : D ≃ Option (Fin (m + 1)))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    IsPure (coordinatePure e) ∧
      Commute (densityMatrix (extremalDiagonal e u hu)) (densityMatrix (coordinatePure e)) ∧
      traceDistance (extremalDiagonal e u hu) (coordinatePure e) = u ∧
      subentropy (extremalDiagonal e u hu) - subentropy (coordinatePure e) = phi m u := by
  have hzero : subentropy (coordinatePure e) = 0 :=
    (extremalDiagonal_subentropy e (u := 0) ⟨le_rfl, zero_le_one⟩).trans (phi_zero m)
  refine ⟨(subentropy_zero_iff_pure _).mp hzero, ?_, ?_, ?_⟩
  · exact diagonalDensity_commute _ _ (simplex_reindex _ (extremal_probability m hu) e)
      (simplex_reindex _ (extremal_probability m (u := 0) ⟨le_rfl, zero_le_one⟩) e)
  · unfold coordinatePure extremalDiagonal
    rw [diagonalDensity_traceDistance]
    change (∑ i, |extremalVector m u (e i) - extremalVector m 0 (e i)|) / 2 = u
    rw [e.sum_comp (fun i ↦ |extremalVector m u i - extremalVector m 0 i|)]
    exact extremal_totalVariation m hu.1
  · rw [hzero, sub_zero, extremalDiagonal_subentropy]

/-- At the uniform endpoint the second spectrum is uniform: its density matrix is I/d. -/
theorem extremalDiagonal_uniform (e : D ≃ Option (Fin (m + 1))) :
    densityMatrix (extremalDiagonal e (uniformError m) (uniformError_mem m)) =
      (1 / ((m + 2 : ℕ) : ℝ)) • (1 : Matrix D D ℂ) := by
  change diagonal (fun i ↦ (extremalVector m (uniformError m) (e i) : ℂ)) = _
  rw [extremal_uniform]
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.smul_apply, Complex.real_smul]
  · simp [Matrix.smul_apply, h]

/-- Values of the absolute subentropy difference on the closed trace-distance ball. -/
def quantumDifferences (D : Type*) [Fintype D] [DecidableEq D] (δ : ℝ) : Set ℝ :=
  {v | ∃ ρ σ : DensityState D, traceDistance ρ σ ≤ δ ∧ v = |subentropy ρ - subentropy σ|}

/-- In every positive finite dimension, the quantum modulus is the largest attained
difference on the ball at every nonnegative radius. -/
theorem quantum_modulus_isGreatest (D : Type*) [Fintype D] [DecidableEq D] [Nonempty D]
    {δ : ℝ} (hδ : 0 ≤ δ) :
    IsGreatest (quantumDifferences D δ) (quantumModulus (Fintype.card D) δ) := by
  refine ⟨?_, ?_⟩
  · by_cases hd : Fintype.card D = 1
    · let i : D := Classical.choice ‹Nonempty D›
      let p := pointMass i
      let hp := pointMass_probability i
      refine ⟨diagonalDensity p hp, diagonalDensity p hp, ?_, ?_⟩
      · simpa [diagonalDensity_traceDistance, totalVariation] using hδ
      · simp [hd, quantumModulus]
    · have hpos := Fintype.card_pos (α := D)
      obtain ⟨m, hm⟩ : ∃ m, Fintype.card D = m + 2 := ⟨Fintype.card D - 2, by omega⟩
      let e : D ≃ Option (Fin (m + 1)) := Fintype.equivOfCardEq (by simp [hm, Nat.add_assoc])
      let u := min δ (uniformError m)
      have hu : u ∈ Icc (0 : ℝ) 1 :=
        ⟨le_min hδ (uniformError_mem m).1, (min_le_right ..).trans (uniformError_mem m).2⟩
      obtain ⟨_, _, hdist, hgap⟩ := extremal_diagonal_pair e hu
      refine ⟨extremalDiagonal e u hu, coordinatePure e, hdist.le.trans (min_le_left ..), ?_⟩
      have hnonneg : 0 ≤ phi m u := classical_subentropy_nonneg _ (extremal_probability m hu)
      rw [hgap, abs_of_nonneg hnonneg, hm]
      rfl
  · rintro v ⟨ρ, σ, hdist, rfl⟩
    exact quantum_continuity_upper ρ σ hdist

/-- The supremum in Theorem 13, in the manuscript's closed-ball formulation. -/
theorem quantum_modulus_supremum (D : Type*) [Fintype D] [DecidableEq D] [Nonempty D]
    {δ : ℝ} (hδ : 0 ≤ δ) :
    sSup (quantumDifferences D δ) = quantumModulus (Fintype.card D) δ :=
  (quantum_modulus_isGreatest D hδ).csSup_eq

/-- On the plateau the attained maximum is log d - H_d + 1. -/
theorem quantum_modulus_plateau (D : Type*) [Fintype D] [DecidableEq D]
    (hd : Fintype.card D = m + 2) {δ : ℝ} (hδ : uniformError m ≤ δ) :
    IsGreatest (quantumDifferences D δ)
      (Real.log (m + 2 : ℕ) - (harmonic (m + 2) : ℝ) + 1) := by
  have : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have h := quantum_modulus_isGreatest D ((uniformError_mem m).1.trans hδ)
  simpa only [hd, quantumModulus, modulus, min_eq_right hδ, phi_uniform_endpoint] using h

end SubentropyCertificates.SpectralContinuity
