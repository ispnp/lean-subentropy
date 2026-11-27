module

public import SubentropyCertificates.QuantumContinuity

/-! A classical probability vector embeds as a diagonal density matrix. The
embedding preserves subentropy and takes total variation to trace distance. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.Basic
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Continuity
open SubentropyCertificates.MixedQubit (traceDistance)
open SubentropyCertificates.BinarySpectra (densityMatrix)

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The density matrix with the specified probabilities on its diagonal. -/
def diagonalDensity (p : D → ℝ) (hp : p ∈ probabilitySimplex D) : DensityState D :=
  ⟨CStarMatrix.ofMatrix (diagonal (fun i ↦ (p i : ℂ))),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (diagonal_density hp).1.nonneg,
    (diagonal_density hp).2⟩

theorem diagonalDensity_subentropy (p : D → ℝ) (hp : p ∈ probabilitySimplex D) :
    subentropy (diagonalDensity p hp) = classicalSubentropy p := rfl

theorem diagonalDensity_commute (p q : D → ℝ)
    (hp : p ∈ probabilitySimplex D) (hq : q ∈ probabilitySimplex D) :
    Commute (densityMatrix (diagonalDensity p hp)) (densityMatrix (diagonalDensity q hq)) := by
  change diagonal (fun i ↦ (p i : ℂ)) * diagonal (fun i ↦ (q i : ℂ)) =
    diagonal (fun i ↦ (q i : ℂ)) * diagonal (fun i ↦ (p i : ℂ))
  simp only [diagonal_mul_diagonal, mul_comm]

/-- Summing absolute eigenvalues of a real diagonal matrix only depends on its diagonal
multiset, so no order assumption or distinctness assumption is needed. -/
private theorem sum_abs_diagonal {H : Matrix D D ℂ} (hH : H.IsHermitian) (w : D → ℝ)
    (hw : H = diagonal (fun i ↦ (w i : ℂ))) :
    (∑ i, |hH.eigenvalues i|) = ∑ i, |w i| := by
  have hr : H.charpoly.roots = Finset.univ.val.map (fun i ↦ (w i : ℂ)) := by
    rw [hw, Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h := congrArg (fun r : Multiset ℂ ↦ (r.map (fun z ↦ |z.re|)).sum)
    (hH.roots_charpoly_eq_eigenvalues.symm.trans hr)
  simpa only [Multiset.map_map, Finset.sum_map_val, Function.comp_apply,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using h

/-- Trace distance of two states diagonal in the same basis is total variation
of their diagonal entries in that basis. -/
theorem diagonalDensity_traceDistance (p q : D → ℝ)
    (hp : p ∈ probabilitySimplex D) (hq : q ∈ probabilitySimplex D) :
    traceDistance (diagonalDensity p hp) (diagonalDensity q hq) = totalVariation p q := by
  let hH := (density_posSemidef (diagonalDensity p hp)).isHermitian.sub
    (density_posSemidef (diagonalDensity q hq)).isHermitian
  have hd : densityMatrix (diagonalDensity p hp) - densityMatrix (diagonalDensity q hq) =
      diagonal (fun i ↦ ((p i - q i : ℝ) : ℂ)) := by
    change diagonal (fun i ↦ (p i : ℂ)) - diagonal (fun i ↦ (q i : ℂ)) = _
    simp only [← Matrix.diagonal_sub, Complex.ofReal_sub]
  change (∑ i, |hH.eigenvalues i|) / 2 = (∑ i, |p i - q i|) / 2
  rw [sum_abs_diagonal hH (fun i ↦ p i - q i) hd]

end SubentropyCertificates.SpectralContinuity
