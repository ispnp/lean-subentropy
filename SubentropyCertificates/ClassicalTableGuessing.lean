module

public import SubentropyCertificates.GuessingMeasurement
import all D5.S3.Quantum.Subentropy.ClassicalQuantumGram

/-! A classical joint law as a diagonal ensemble. Measuring its signal register
in the coordinate basis and guessing the outcome succeeds with its diagonal mass. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.Continuity
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Discrimination
open SubentropyCertificates.MeasurementPosterior
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram

variable {X : Type*} [Fintype X] [DecidableEq X]

private def diagonalState (b : X → ℝ) (hb : b ∈ probabilitySimplex X) : DensityState X :=
  ⟨CStarMatrix.ofMatrix (diagonal (fun i ↦ (b i : ℂ))),
   map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (diagonal_density hb).1.nonneg,
   (diagonal_density hb).2⟩

/-- The lower and upper conditional bounds for a classical joint table. The same
alphabet is used for both marginals so that the guess can be the observed label. -/
theorem classical_joint_guessing (m : ℕ) (hn : Fintype.card X = m + 2)
    (p q : X → ℝ) (hp : p ∈ probabilitySimplex X) (J : X → X → ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hr : ∀ i, ∑ j, J i j = p i) (hc : ∀ j, ∑ i, J i j = q j) :
    let gap := classicalSubentropy (fun u : X × X ↦ J u.1 u.2) - classicalSubentropy q
    0 ≤ gap ∧ gap ≤ phi m (1 - ∑ i, J i i) := by
  let b := fun i j ↦ if p i = 0 then p j else J i j / p i
  have hb i : b i ∈ probabilitySimplex X := by
    by_cases hz : p i = 0
    · simpa [b, hz] using hp
    · refine ⟨fun j ↦ by simp [b, hz, div_nonneg (hJ i j) (hp.1 i)], ?_⟩
      simp [b, hz, ← Finset.sum_div, hr]
  have hmul i j : p i * b i j = J i j := by
    by_cases hz : p i = 0
    · have hle := Finset.single_le_sum (s := Finset.univ) (fun k _ ↦ hJ i k) (Finset.mem_univ j)
      rw [hr, hz] at hle
      simp [hz, le_antisymm hle (hJ i j)]
    · simp [b, hz]
      field_simp
  have hC i j : (p i : ℂ) * (b i j : ℂ) = (J i j : ℂ) := by exact_mod_cast hmul i j
  let ρ := fun i ↦ diagonalState (b i) (hb i)
  have mat i : CStarMatrix.ofMatrix.symm (ρ i).1 = diagonal (fun j ↦ (b i j : ℂ)) := rfl
  have recMat : CStarMatrix.ofMatrix.symm (recordState p hp.1 hp.2 ρ).1 =
      diagonal (fun u : X × X ↦ (J u.1 u.2 : ℂ)) := by
    ext ⟨i,j⟩ ⟨k,l⟩
    rw [record_entries, mat]
    by_cases h : i = k <;> by_cases g : j = l <;>
      simp [h, g, hC]
  have avgMat : CStarMatrix.ofMatrix.symm (mixtureState p hp.1 hp.2 ρ).1 =
      diagonal (fun j ↦ (q j : ℂ)) := by
    ext j k
    change (∑ i, p i • CStarMatrix.ofMatrix.symm (ρ i).1) j k = _
    simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, mat]
    by_cases h : j = k
    · subst k
      simp only [diagonal_apply_eq, hC, ← Complex.ofReal_sum, hc]
    · simp [diagonal_apply_ne _ h]
  let F : X → Matrix X X ℂ := fun j ↦ diagonal (fun k ↦ if k = j then (1 : ℂ) else 0)
  have hF j : (F j).PosSemidef := Matrix.PosSemidef.diagonal (fun k ↦ by
    by_cases h : k = j <;> simp [h])
  have hFs : ∑ j, F j = 1 := by
    ext i k
    by_cases h : i = k
    · subst k
      simp [F, Matrix.sum_apply]
    · simp [F, Matrix.sum_apply, h]
  have success : decisionSuccess p ρ F id = ∑ i, J i i := by
    unfold decisionSuccess jointProbability
    apply Finset.sum_congr rfl
    intro i _
    rw [mat]
    simpa [F, diagonal_mul_diagonal, trace_diagonal, ite_mul] using hmul i i
  have H := measurement_curve_bound m hn p hp.1 hp.2 ρ F hF hFs id
  change 0 ≤ matrixSubentropy _ - matrixSubentropy _ ∧
    matrixSubentropy _ - matrixSubentropy _ ≤ _ at H
  simpa only [recMat, avgMat, success, classicalSubentropy] using H

end SubentropyCertificates.Continuity
