module

public import SubentropyCertificates.SubentropyMaximum

/-! Distance from any pure state to the maximally mixed state, in both orders. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.InputInformationBalance (IsPure)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Continuity
open SubentropyCertificates.BinarySpectra (densityMatrix)
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.QuantumEquality
open SubentropyCertificates.Subadditivity (subentropy_of_spectrum subentropy_zero_iff_pure)

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Simultaneous unitary conjugation preserves trace distance. -/
theorem traceDistance_eq_of_unitary (ρ σ τ υ : DensityState D) (U : Matrix.unitaryGroup D ℂ)
    (hρ : densityMatrix ρ = Unitary.conjStarAlgAut ℂ _ U (densityMatrix τ))
    (hσ : densityMatrix σ = Unitary.conjStarAlgAut ℂ _ U (densityMatrix υ)) :
    traceDistance ρ σ = traceDistance τ υ := by
  let h := (density_posSemidef ρ).isHermitian.sub (density_posSemidef σ).isHermitian
  let k := (density_posSemidef τ).isHermitian.sub (density_posSemidef υ).isHermitian
  have hc : (densityMatrix ρ - densityMatrix σ).charpoly =
      (densityMatrix τ - densityMatrix υ).charpoly := by
    rw [hρ, hσ, ← map_sub, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc]
    simp
  have he := (h.eigenvalues_eq_eigenvalues_iff k).mpr hc
  change (∑ i, |h.eigenvalues i|) / 2 = (∑ i, |k.eigenvalues i|) / 2
  rw [he]

private theorem pointMass_uniform_distance (i : D) :
    totalVariation (pointMass i) (fun _ : D ↦ 1 / (Fintype.card D : ℝ)) =
      1 - 1 / (Fintype.card D : ℝ) := by
  have : Nonempty D := ⟨i⟩
  let c : ℝ := 1 / (Fintype.card D : ℝ)
  have hn : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h1 : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast Fintype.card_pos (α := D)
  have hc : 0 ≤ c := div_nonneg zero_le_one hn.le
  have hc1 : c ≤ 1 := (div_le_one hn).mpr h1
  have term j : |pointMass i j - c| = c + (if j = i then 1 - 2*c else 0) := by
    by_cases h : j = i
    · simp [pointMass, h, abs_of_nonneg (sub_nonneg.mpr hc1)]
      ring
    · simp [pointMass, h, abs_of_nonneg hc]
  change (∑ j, |pointMass i j - c|) / 2 = 1 - c
  simp_rw [term]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hdc : (Fintype.card D : ℝ) * c = 1 := by simp [c, hn.ne']
  linarith

/-- The distance is exactly 1-1/d for every pure direction, including d=1. -/
theorem pure_uniform_traceDistance [Nonempty D] (ρ : DensityState D) (hρ : IsPure ρ) :
    traceDistance ρ (maximallyMixed D) = 1 - 1 / (Fintype.card D : ℝ) ∧
    traceDistance (maximallyMixed D) ρ = 1 - 1 / (Fintype.card D : ℝ) := by
  let hA := (density_posSemidef ρ).isHermitian
  let p := hA.eigenvalues
  have hp : p ∈ probabilitySimplex D := spectral_prob (density_posSemidef ρ) ρ.2.2
  obtain ⟨i, hi⟩ := (classical_zero_iff_pointMass p hp).mp
    ((subentropy_of_spectrum hA).symm.trans ((subentropy_zero_iff_pure ρ).mpr hρ))
  let U := hA.eigenvectorUnitary
  have hs : densityMatrix ρ = Unitary.conjStarAlgAut ℂ _ U (densityMatrix (diagonalDensity p hp)) :=
    hA.spectral_theorem
  have hu : densityMatrix (maximallyMixed D) =
      Unitary.conjStarAlgAut ℂ _ U (densityMatrix (maximallyMixed D)) := by
    rw [maximallyMixed_matrix, map_smul, map_one]
  constructor
  · rw [traceDistance_eq_of_unitary _ _ _ _ U hs hu]
    unfold maximallyMixed
    rw [diagonalDensity_traceDistance, hi, pointMass_uniform_distance]
  · rw [traceDistance_eq_of_unitary _ _ _ _ U hu hs]
    unfold maximallyMixed
    rw [diagonalDensity_traceDistance, hi, ← pointMass_uniform_distance i]
    unfold totalVariation
    congr 1
    exact Finset.sum_congr rfl (fun j _ ↦ abs_sub_comm _ _)

end SubentropyCertificates.SpectralContinuity
