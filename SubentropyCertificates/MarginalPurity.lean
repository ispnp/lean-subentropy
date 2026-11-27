module

public import SubentropyCertificates.QuantumEquality
public import D5.S3.Quantum.Information.InputInformationBalance

/-! Subentropy vanishes precisely on rank-one density matrices. We use the
spectral probability vector, so zero and repeated eigenvalues are allowed. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace SubentropyCertificates.Subadditivity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.InputInformationBalance
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.QuantumEquality

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem subentropy_of_spectrum {A : Matrix D D ℂ} (hA : A.IsHermitian) :
    matrixSubentropy A = classicalSubentropy hA.eigenvalues := by
  let U : Matrix D D ℂ := hA.eigenvectorUnitary
  have hd : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * U.conjTranspose :=
    hA.spectral_theorem
  exact (congrArg matrixSubentropy hd).trans
    (matrixSubentropy_isometric_embedding _ U (Unitary.coe_star_mul_self hA.eigenvectorUnitary))

private theorem pointMass_iff_one_nonzero (p : D → ℝ) (hp : p ∈ probabilitySimplex D) :
    (∃ i, p = pointMass i) ↔ Fintype.card {i // p i ≠ 0} = 1 := by
  classical
  rw [Fintype.card_eq_one_iff]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨i, by simp [pointMass]⟩, ?_⟩
    intro j
    apply Subtype.ext
    by_contra h
    exact j.2 (by simp [pointMass, h])
  · rintro ⟨i, hi⟩
    have hzero (j : D) (hj : j ≠ i.val) : p j = 0 := by
      by_contra h
      exact hj (congrArg Subtype.val (hi ⟨j,h⟩))
    have hone : p i.val = 1 := by
      have hsum := Finset.sum_eq_single_of_mem i.val (Finset.mem_univ i.val) (fun j _ hj => hzero j hj)
      exact hsum.symm.trans hp.2
    refine ⟨i.val, funext fun j => ?_⟩
    by_cases hj : j = i.val
    · simpa [pointMass, hj] using hone
    · simpa [pointMass, hj] using hzero j hj

theorem matrixSubentropy_zero_iff_rank_one {A : Matrix D D ℂ} (hA : A.PosSemidef)
    (ht : A.trace = 1) : matrixSubentropy A = 0 ↔ A.rank = 1 := by
  rw [subentropy_of_spectrum hA.isHermitian, hA.isHermitian.rank_eq_card_non_zero_eigs,
    classical_zero_iff_pointMass _ (spectral_prob hA ht)]
  exact pointMass_iff_one_nonzero _ (spectral_prob hA ht)

theorem subentropy_zero_iff_rank_one (ρ : DensityState D) :
    subentropy ρ = 0 ↔ (CStarMatrix.ofMatrix.symm ρ.1).rank = 1 :=
  matrixSubentropy_zero_iff_rank_one (density_posSemidef ρ) ρ.2.2

/-- The bundled pure-state predicate is an outer-product representation.
Trace one supplies normalization of its amplitude vector. -/
theorem subentropy_zero_iff_pure (ρ : DensityState D) : subentropy ρ = 0 ↔ IsPure ρ := by
  let A := CStarMatrix.ofMatrix.symm ρ.1
  have hA := (density_posSemidef ρ).isHermitian
  constructor
  · intro hz
    change matrixSubentropy A = 0 at hz
    have hp := spectral_prob (density_posSemidef ρ) ρ.2.2
    obtain ⟨i, he⟩ := (classical_zero_iff_pointMass _ hp).mp
      ((subentropy_of_spectrum hA).symm.trans hz)
    let U : Matrix D D ℂ := hA.eigenvectorUnitary
    have hs : A = U * diagonal (fun j => (hA.eigenvalues j : ℂ)) * U.conjTranspose :=
      hA.spectral_theorem
    refine ⟨fun j => U j i, ?_⟩
    intro a b
    change A a b = _
    rw [hs, he, Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [pointMass, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    · intro j _ hj
      simp [pointMass, hj, Matrix.mul_diagonal]
    · simp
  · rintro ⟨v, hv⟩
    have he : A = vecMulVec v (star v) := Matrix.ext hv
    have ht : (vecMulVec v (star v)).trace = 1 := (congrArg Matrix.trace he).symm.trans ρ.2.2
    change matrixSubentropy A = 0
    rw [he]
    apply matrixSubentropy_pure
    simpa only [trace, diag_apply, vecMulVec_apply, Pi.star_apply, mul_comm] using ht

theorem subentropy_nonnegative (ρ : DensityState D) : 0 ≤ subentropy ρ := by
  unfold subentropy
  rw [subentropy_of_spectrum (density_posSemidef ρ).isHermitian]
  exact classical_subentropy_nonneg _ (spectral_prob (density_posSemidef ρ) ρ.2.2)

end SubentropyCertificates.Subadditivity
