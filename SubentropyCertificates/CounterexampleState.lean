module

public import D5.S3.Quantum.Information.InputInformationBalance
public import D5.S3.Quantum.Subentropy.DensityKernel

/-! The classical binary label and its two pure qubit-pair signals. The
columns below omit the common normalization. Their squared norm is five,
so the equal prior gives the multiplier 1/10 in the density matrix. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped ComplexOrder MatrixOrder BigOperators
namespace SubentropyCertificates.QuantumCounterexample
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.InputInformationBalance

local notation "conjTwo" => (map_ofNat (starRingEnd ℂ) 2)

abbrev Bit := Fin 2
abbrev ABC := (Bit × Bit) × Bit

def signals : Matrix (Bit × Bit) Bit ℂ := fun (b,c) a =>
  if b = c then (if b = a then 2 else 1) else 0

def labelled : Matrix ABC Bit ℂ := fun ((a,b),c) j =>
  if a = j then signals (b,c) j else 0

def mixture {D : Type*} [Fintype D] (V : Matrix D Bit ℂ) : Matrix D D ℂ :=
  (1/10 : ℝ) • (V * V.conjTranspose)

def state : DensityState ABC := by
  refine ⟨CStarMatrix.ofMatrix (mixture labelled), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact ((Matrix.posSemidef_self_mul_conjTranspose labelled).smul
      (by norm_num : (0 : ℝ) ≤ 1/10)).nonneg
  · change (mixture labelled).trace = 1
    norm_num [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, mixture,
      labelled, signals, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.real_smul, conjTwo]

/-- In the computational basis the diagonal label blocks are the two
rank-one signal matrices with the common factor 1/10. -/
theorem state_entries (a d : Bit) (u v : Bit × Bit) :
    state.1 ((a,u.1),u.2) ((d,v.1),v.2) =
      if a=d then (1/10 : ℂ)*signals u a*star (signals v a) else 0 := by
  change mixture labelled ((a,u.1),u.2) ((d,v.1),v.2) = _
  fin_cases a <;> fin_cases d <;>
    simp [mixture, labelled, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.real_smul, mul_assoc]

def stateAB := marginalRight state
def stateB := marginalLeft stateAB
def stateBC := marginalLeft (relabel (Equiv.prodAssoc Bit Bit Bit).symm state)

def abWeight : Bit × Bit → ℝ := fun (a,b) => if a = b then 2/5 else 1/10

/-- The marginals here are obtained by partial trace of the bundled witness. -/
theorem marginal_matrices :
    CStarMatrix.ofMatrix.symm stateAB.1 = diagonal (fun i => (abWeight i : ℂ)) ∧
    CStarMatrix.ofMatrix.symm stateB.1 = diagonal (fun _ => (1/2 : ℂ)) ∧
    CStarMatrix.ofMatrix.symm stateBC.1 = mixture signals := by
  have hab : partialTraceRight (mixture labelled) = diagonal (fun i => (abWeight i : ℂ)) := by
    ext ⟨a,b⟩ ⟨j,k⟩
    fin_cases a <;> fin_cases b <;> fin_cases j <;> fin_cases k <;>
      norm_num [partialTraceRight, mixture, labelled, signals, abWeight, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.real_smul, Matrix.diagonal_apply, conjTwo]
  refine ⟨hab, ?_, ?_⟩
  · change partialTraceLeft (partialTraceRight (mixture labelled)) = _
    rw [hab]
    ext b c
    fin_cases b <;> fin_cases c <;>
      norm_num [partialTraceLeft, Fin.sum_univ_two, Matrix.diagonal_apply, abWeight]
  · ext ⟨b,c⟩ ⟨j,k⟩
    change (∑ a : Bit, mixture labelled ((a,b),c) ((a,j),k)) = mixture signals (b,c) (j,k)
    fin_cases b <;> fin_cases c <;> fin_cases j <;> fin_cases k <;>
      norm_num [mixture, labelled, signals, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Complex.real_smul]

/-- Small Gram matrices of the labelled and unlabelled signals. -/
theorem signal_grams :
    labelled.conjTranspose * labelled = diagonal (fun _ => (5 : ℂ)) ∧
    signals.conjTranspose * signals = (fun i j => if i=j then (5 : ℂ) else 4) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, labelled, signals,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diagonal_apply, conjTwo]

end SubentropyCertificates.QuantumCounterexample
