module

public import SubentropyCertificates.MarginalPurity
import all D5.S3.Quantum.Subentropy.EigenbasisBlocks

/-! Diagonalizing both marginals gives a probability table with their
spectra as its row and column sums. Full diagonal pinching bounds the
original state's subentropy by the classical subentropy of the table. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
namespace SubentropyCertificates.QubitDeficit
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.EigenbasisBlocks
open D5.S3.Quantum.Subentropy.PinchingGap
open SubentropyCertificates.ClassicalCurve

variable {D F : Type*} [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]

private theorem reindex_subentropy (M : Matrix D D ℂ) (e : F ≃ D) :
    matrixSubentropy (M.submatrix e e) = matrixSubentropy M := by
  unfold matrixSubentropy subentropyKernel
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have h : 1 + (t⁻¹ : ℝ) • M.submatrix e e = (1 + (t⁻¹ : ℝ) • M).submatrix e e := by
    simp [Matrix.submatrix_add, Matrix.submatrix_smul, Matrix.submatrix_one_equiv]
  dsimp only
  rw [h, Matrix.det_submatrix_equiv_self]

omit [DecidableEq D] [DecidableEq F] in
private theorem reindex_trace (M : Matrix D D ℂ) (e : F ≃ D) :
    (M.submatrix e e).trace = M.trace := e.sum_comp (fun i => M i i)

private theorem diagonal_upper (M : Matrix D D ℂ) (hM : M.PosSemidef)
    (ht : M.trace = 1) (i₀ : D) :
    matrixSubentropy M ≤ classicalSubentropy (fun i => (M i i).re) := by
  let e : D × Unit ≃ D := Equiv.prodUnique D Unit
  let T := M.submatrix e e
  have h := (actual_pinching_gap_laws (i₀, ())).2 T (hM.submatrix e)
    ((reindex_trace M e).trans ht)
  let P := diagonal (fun i => ((M i i).re : ℂ))
  have he : blockPinch T = P.submatrix e e := by
    ext ⟨i, u⟩ ⟨j, v⟩
    cases u; cases v
    change (if i = j then M i j else 0) = P i j
    by_cases hij : i = j
    · subst j
      simp only [ite_true, P, Matrix.diagonal_apply_eq]
      apply Complex.ext
      · rfl
      · exact (RCLike.nonneg_iff.mp (hM.diag_nonneg (i := i))).2
    · simp [hij, P]
  rw [he, reindex_subentropy P e] at h
  change 0 ≤ matrixSubentropy P - matrixSubentropy (M.submatrix e e) at h
  rw [reindex_subentropy M e] at h
  exact sub_nonneg.mp h

private theorem local_subentropy (M : Matrix (D × F) (D × F) ℂ) (U : Matrix D D ℂ)
    (hu : U * U.conjTranspose = 1) :
    matrixSubentropy (localConjugate U M) = matrixSubentropy M := by
  let J := U.conjTranspose ⊗ₖ (1 : Matrix F F ℂ)
  have hJ : J.conjTranspose * J = 1 := by
    simp only [J, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hu,
      Matrix.one_kronecker_one]
  simpa only [J, localConjugate, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] using
    matrixSubentropy_isometric_embedding M J hJ

private theorem eigenbasis_diagonal {M : Matrix D D ℂ} (h : M.IsHermitian) :
    (h.eigenvectorUnitary : Matrix D D ℂ).conjTranspose * M * h.eigenvectorUnitary =
      diagonal (fun i => (h.eigenvalues i : ℂ)) := by
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using h.conjStarAlgAut_star_eigenvectorUnitary

/-- The joint probabilities in a product of marginal eigenbases. Row and
column sums are the actual eigenvalues, including any zero eigenvalues. -/
theorem marginal_eigenbasis_table (ρ : DensityState (D × F)) (i₀ : D × F) :
    let hA := (partialTraceRight_posSemidef (density_posSemidef ρ)).isHermitian
    let hB := (partialTraceLeft_posSemidef (density_posSemidef ρ)).isHermitian
    ∃ p ∈ probabilitySimplex (D × F),
      (∀ i, ∑ j, p (i,j) = hA.eigenvalues i) ∧
      (∀ j, ∑ i, p (i,j) = hB.eigenvalues j) ∧
      subentropy ρ ≤ classicalSubentropy p := by
  let M := CStarMatrix.ofMatrix.symm ρ.1
  have hM := density_posSemidef ρ
  let hA := (partialTraceRight_posSemidef hM).isHermitian
  let hB := (partialTraceLeft_posSemidef hM).isHermitian
  let U : Matrix D D ℂ := hA.eigenvectorUnitary
  let V : Matrix F F ℂ := hB.eigenvectorUnitary
  have hU : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hV : V * V.conjTranspose = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  let e := Equiv.prodComm F D
  let N := M.submatrix e e
  let L := localConjugate V N
  let P := L.submatrix e.symm e.symm
  let K := localConjugate U P
  have hL := local_density V hV N (hM.submatrix e)
  have hK := local_density U hU P (hL.1.submatrix e.symm)
  have ht : K.trace = 1 := hK.2.trans ((reindex_trace L e.symm).trans
    (hL.2.trans ((reindex_trace M e).trans ρ.2.2)))
  have hright : partialTraceRight K = diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    rw [show partialTraceRight K = _ from local_right U P,
      show partialTraceRight P = partialTraceLeft L from rfl, local_left V hV N]
    exact eigenbasis_diagonal hA
  have hleft : partialTraceLeft K = diagonal (fun j => (hB.eigenvalues j : ℂ)) := by
    rw [show partialTraceLeft K = _ from local_left U hU P,
      show partialTraceLeft P = partialTraceRight L from rfl, local_right V N]
    exact eigenbasis_diagonal hB
  let p := fun i => (K i i).re
  refine ⟨p, ⟨fun i => (RCLike.nonneg_iff.mp (hK.1.diag_nonneg (i := i))).1, ?_⟩, ?_, ?_, ?_⟩
  · simpa [p, Matrix.trace, Matrix.diag_apply, Complex.re_sum] using congrArg Complex.re ht
  · intro i
    simpa [p, partialTraceRight, Complex.re_sum] using congrArg (fun A => (A i i).re) hright
  · intro j
    simpa [p, partialTraceLeft, Complex.re_sum] using congrArg (fun A => (A j j).re) hleft
  · have hQ : matrixSubentropy K = matrixSubentropy M :=
      (local_subentropy P U hU).trans ((reindex_subentropy L e.symm).trans
        ((local_subentropy N V hV).trans (reindex_subentropy M e)))
    exact hQ.symm.le.trans (diagonal_upper K hK.1 ht i₀)

end SubentropyCertificates.QubitDeficit
