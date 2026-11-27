module

public import SharpGuessing.Definitions
public import SubentropyCertificates.OrthogonalMeasurement
public import D5.S3.Quantum.Subentropy.ClassicalQuantumGram
public import Mathlib.Analysis.Matrix.Hermitian

/-! Conversions between matrix ensembles and the density states used by the companion proofs. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ComplexOrder

namespace SubentropySharpGuessing

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Subentropy
open scoped MatrixOrder Kronecker

/-- Bundle each signal as the density state used in the companion. -/
def toSignal (E : Ensemble n B) (i : Fin n) : DensityState B :=
  ⟨CStarMatrix.ofMatrix (E.signal i),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (E.signal_pos i).nonneg, E.signal_trace i⟩

/-- Express a companion ensemble in the matrix coordinates used in the challenge. -/
def fromSignals (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : Fin n → DensityState B) : Ensemble n B :=
  ⟨p, hp, hs, fun i ↦ CStarMatrix.ofMatrix.symm (ρ i).1, fun i ↦ density_posSemidef (ρ i),
    fun i ↦ (ρ i).2.2⟩

@[simp] theorem toSignal_fromSignals (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : Fin n → DensityState B) (i : Fin n) : toSignal (fromSignals p hp hs ρ) i = ρ i := rfl

theorem successProbabilities_bridge (E : Ensemble n B) :
    successProbabilities E = GuessingProbability.successProbabilitySet E.prior (toSignal E) := rfl

theorem pGuess_bridge (E : Ensemble n B) :
    pGuess E = GuessingProbability.pGuess E.prior (toSignal E) := rfl

/-- Entrywise expansion, following `record_entries` in The Omega Institute's
`D5.S3.Quantum.Subentropy.ClassicalQuantumGram`. -/
private theorem record_matrix (E : Ensemble n B) :
    CStarMatrix.ofMatrix.symm (recordState E.prior E.prior_nonneg E.prior_sum (toSignal E)).1 =
      jointState E := by
  ext i j
  change (∑ x, E.prior x •
    ((Matrix.diagonal (fun k ↦ if k = x then (1 : ℂ) else 0)) ⊗ₖ E.signal x)) i j = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal, Complex.real_smul]
  by_cases h : i.1 = j.1
  · simp [jointState, h, eq_comm]
  · simp [jointState, h]

theorem conditional_bridge (E : Ensemble n B) :
    conditionalSubentropy E = ClassicalQuantumGram.conditionalSubentropy
      E.prior E.prior_nonneg E.prior_sum (toSignal E) := by
  unfold conditionalSubentropy ClassicalQuantumGram.conditionalSubentropy Basic.subentropy
  rw [record_matrix]
  rfl

@[simp] theorem fromSignals_pGuess (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : Fin n → DensityState B) :
    pGuess (fromSignals p hp hs ρ) = GuessingProbability.pGuess p ρ := rfl

@[simp] theorem fromSignals_conditional (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : Fin n → DensityState B) :
    conditionalSubentropy (fromSignals p hp hs ρ) =
      ClassicalQuantumGram.conditionalSubentropy p hp hs ρ := conditional_bridge _

/-- For a Hermitian matrix, the orthogonal complement of its range is its kernel. -/
private theorem matrix_mul_eq_zero_iff (A D : Matrix B B ℂ) (hA : A.IsHermitian) :
    A * D = 0 ↔ LinearMap.range A.toEuclideanLin ⟂ LinearMap.range D.toEuclideanLin := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le,
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).orthogonal_range, LinearMap.range_le_ker_iff]
  change A * D = 0 ↔ (Matrix.toLpLin 2 2 A).comp (Matrix.toLpLin 2 2 D) = 0
  rw [← Matrix.toLpLin_mul 2 2 2]
  exact (Matrix.toLpLin 2 2).map_eq_zero_iff.symm

theorem orthogonal_bridge (E : Ensemble n B) :
    orthogonalSupports E ↔ SubentropyCertificates.ZeroConditional.orthogonalSupports
      E.prior (toSignal E) := by
  constructor
  · intro h x y hxy hx hy
    exact (matrix_mul_eq_zero_iff _ _ (E.signal_pos x).isHermitian).mp (h x y hxy hx hy)
  · intro h x y hxy hx hy
    exact (matrix_mul_eq_zero_iff _ _ (E.signal_pos x).isHermitian).mpr (h x y hxy hx hy)

end SubentropySharpGuessing
