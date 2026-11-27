module

public import SubentropyCertificates.PureSignalBlockEmbedding
public import SubentropyCertificates.PureUniformDistance

/-! A nonnegative table specifies commuting CQ blocks in any prescribed quantum basis. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.ConditionalContinuity
open D5.S3.Quantum.Subentropy.Basic
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Continuity (totalVariation)
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.SpectralContinuity

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- The rows of the table give the spectra of blocks in the common basis U. -/
def spectralBlocks (U : Matrix.unitaryGroup D ℂ) (p : X → D → ℝ) (x : X) : Matrix D D ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (diagonal fun j ↦ (p x j : ℂ))

omit [DecidableEq X] in
theorem spectralBlocks_posSemidef (U : Matrix.unitaryGroup D ℂ) (p : X → D → ℝ)
    (hp : (fun z : D × X ↦ p z.2 z.1) ∈ probabilitySimplex (D × X)) (x : X) :
    (spectralBlocks U p x).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply map_nonneg (Unitary.conjStarAlgAut ℂ _ U)
  exact (PosSemidef.diagonal fun j ↦ Complex.zero_le_real.mpr (hp.1 (j, x))).nonneg

omit [DecidableEq X] in
theorem spectralBlocks_sum (U : Matrix.unitaryGroup D ℂ) (p : X → D → ℝ) :
    ∑ x, spectralBlocks U p x =
      Unitary.conjStarAlgAut ℂ _ U (diagonal fun j ↦ ((∑ x, p x j : ℝ) : ℂ)) := by
  unfold spectralBlocks
  rw [← map_sum]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hij]

omit [DecidableEq X] in
theorem spectralBlocks_trace (U : Matrix.unitaryGroup D ℂ) (p : X → D → ℝ)
    (hp : (fun z : D × X ↦ p z.2 z.1) ∈ probabilitySimplex (D × X)) :
    (∑ x, spectralBlocks U p x).trace = 1 := by
  rw [spectralBlocks_sum, Unitary.conjStarAlgAut_apply, trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  have h := hp.2
  rw [Fintype.sum_prod_type] at h
  simp only [← Complex.ofReal_sum, h, Complex.ofReal_one]

private def jointUnitary (U : Matrix.unitaryGroup D ℂ) : Matrix.unitaryGroup (D × X) ℂ :=
  ⟨blockDiagonal (fun _ : X ↦ (U : Matrix D D ℂ)), by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (blockDiagonal _).conjTranspose * blockDiagonal _ = 1
    rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one]
    congr 1
    funext x
    exact Unitary.coe_star_mul_self U⟩

private theorem joint_eq_conj (U : Matrix.unitaryGroup D ℂ) (p : X → D → ℝ) :
    blockDiagonal (spectralBlocks U p) = Unitary.conjStarAlgAut ℂ _ (jointUnitary (X := X) U)
      (diagonal fun z : D × X ↦ (p z.2 z.1 : ℂ)) := by
  change blockDiagonal (fun x ↦ (U : Matrix D D ℂ) * (diagonal fun j ↦ (p x j : ℂ)) *
    (U : Matrix D D ℂ).conjTranspose) = blockDiagonal _ * _ * (blockDiagonal _).conjTranspose
  rw [← blockDiagonal_diagonal (fun x j ↦ (p x j : ℂ)), blockDiagonal_conjTranspose,
    ← blockDiagonal_mul, ← blockDiagonal_mul]

/-- Joint subentropy is the classical subentropy of the table in the common basis. -/
theorem spectralBlocks_conditionalQ (U : Matrix.unitaryGroup D ℂ) (p : X → D → ℝ) :
    blockConditionalQ (spectralBlocks U p) = classicalSubentropy (fun z : D × X ↦ p z.2 z.1) -
      matrixSubentropy (∑ x, spectralBlocks U p x) := by
  rw [blockConditionalQ, joint_eq_conj]
  congr 1
  exact matrixSubentropy_isometric_embedding _ _ (Unitary.coe_star_mul_self (jointUnitary U))

/-- Joint trace distance for two tables in the same quantum basis is their total variation. -/
theorem spectralBlocks_traceDistance (U : Matrix.unitaryGroup D ℂ) (p q : X → D → ℝ)
    (hp : (fun z : D × X ↦ p z.2 z.1) ∈ probabilitySimplex (D × X))
    (hq : (fun z : D × X ↦ q z.2 z.1) ∈ probabilitySimplex (D × X)) :
    traceDistance
      (blockDensity (spectralBlocks U p) (spectralBlocks_posSemidef U p hp)
        (spectralBlocks_trace U p hp))
      (blockDensity (spectralBlocks U q) (spectralBlocks_posSemidef U q hq)
        (spectralBlocks_trace U q hq)) =
      totalVariation (fun z : D × X ↦ p z.2 z.1) (fun z : D × X ↦ q z.2 z.1) := by
  rw [← diagonalDensity_traceDistance _ _ hp hq]
  exact traceDistance_eq_of_unitary _ _ _ _ (jointUnitary U) (joint_eq_conj U p) (joint_eq_conj U q)

end SubentropyCertificates.ConditionalContinuity
