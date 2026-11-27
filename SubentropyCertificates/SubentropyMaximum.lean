module

public import SubentropyCertificates.QuantumModulus

/-! The maximally mixed state is the unique maximizer of ordinary subentropy. -/
@[expose] public section
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.BinarySpectra (densityMatrix)
open SubentropyCertificates.Subadditivity (subentropy_of_spectrum)

variable {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]

theorem uniform_simplex (D : Type*) [Fintype D] [Nonempty D] :
    (fun _ : D ↦ 1 / (Fintype.card D : ℝ)) ∈ probabilitySimplex D := by
  have hn : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact ⟨fun _ ↦ by positivity, by simp [nsmul_eq_mul, hn]⟩

/-- The density state I/d on a nonempty finite coordinate type. -/
def maximallyMixed (D : Type*) [Fintype D] [DecidableEq D] [Nonempty D] : DensityState D :=
  diagonalDensity _ (uniform_simplex D)

theorem maximallyMixed_matrix (D : Type*) [Fintype D] [DecidableEq D] [Nonempty D] :
    densityMatrix (maximallyMixed D) = (1 / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ) := by
  change diagonal (fun _ : D ↦ ((1 / (Fintype.card D : ℝ) : ℝ) : ℂ)) = _
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

private theorem classical_uniform_max :
    IsMaxOn classicalSubentropy (probabilitySimplex D) (fun _ : D ↦ 1 / (Fintype.card D : ℝ)) := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card D = k + 1 :=
    ⟨Fintype.card D - 1, by have := Fintype.card_pos (α := D); omega⟩
  let e : Fin (k + 1) ≃ D := Fintype.equivOfCardEq (by simp [hk])
  intro p hp
  have h := fin_subentropy_le_uniform k (p ∘ e) (simplex_reindex _ hp e)
  rw [classical_subentropy_reindex] at h
  have hu := classical_subentropy_reindex (fun _ : D ↦ 1 / (Fintype.card D : ℝ)) e
  change classicalSubentropy p ≤ classicalSubentropy (fun _ : D ↦ 1 / (Fintype.card D : ℝ))
  rw [← hu]
  simpa only [Function.comp_def, hk] using h

/-- The subentropy upper endpoint and its equality condition on the original density matrix. -/
theorem subentropy_maximum_iff (ρ : DensityState D) :
    subentropy ρ ≤ subentropy (maximallyMixed D) ∧
    (subentropy ρ = subentropy (maximallyMixed D) ↔ ρ = maximallyMixed D) := by
  let hA := (density_posSemidef ρ).isHermitian
  let p := hA.eigenvalues
  let u := fun _ : D ↦ 1 / (Fintype.card D : ℝ)
  have hp : p ∈ probabilitySimplex D := spectral_prob (density_posSemidef ρ) ρ.2.2
  have hs : subentropy ρ = classicalSubentropy p := subentropy_of_spectrum hA
  have hm : subentropy (maximallyMixed D) = classicalSubentropy u := rfl
  refine ⟨hs.le.trans ((classical_uniform_max hp).trans_eq hm.symm), ⟨?_, fun h ↦ h ▸ rfl⟩⟩
  intro he
  have eq : classicalSubentropy p = classicalSubentropy u := hs.symm.trans (he.trans hm)
  have hpm : IsMaxOn classicalSubentropy (probabilitySimplex D) p :=
    fun q hq ↦ (classical_uniform_max hq).trans_eq eq.symm
  have hpu : p = u :=
    classical_subentropy_strictConcave.eq_of_isMaxOn hpm classical_uniform_max hp
      (uniform_simplex D)
  have hmat : densityMatrix ρ = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (fun i ↦ (p i : ℂ))) := hA.spectral_theorem
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change densityMatrix ρ = densityMatrix (maximallyMixed D)
  rw [hmat, hpu]
  change Unitary.conjStarAlgAut ℂ _ _ (densityMatrix (maximallyMixed D)) = _
  rw [maximallyMixed_matrix, map_smul, map_one]

end SubentropyCertificates.SpectralContinuity
