module
public import SubentropyCertificates.BinaryPureHelstrom

/-! Two-column factorizations of the equal-prior mixture and its classical
record. The record columns are orthogonal even when the signal vectors coincide. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators Kronecker
namespace SubentropyCertificates.BinarySpectra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open SubentropyCertificates.Helstrom
open SubentropyCertificates.PinchingEquality
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev halfPrior := binaryPrior (1/2)
theorem halfPrior_nonneg (i : Fin 2) : 0 ≤ halfPrior i :=
  binary_prior_nonneg (by constructor <;> norm_num) i
theorem halfPrior_sum : ∑ i, halfPrior i = 1 := binary_prior_sum _

abbrev densityMatrix {K : Type*} [Fintype K] [DecidableEq K] (ρ : DensityState K) :=
  CStarMatrix.ofMatrix.symm ρ.1

def columns (v w : D → ℂ) : Matrix D (Fin 2) ℂ := fun i => ![v i,w i]
def tagged (x : Fin 2) (v : D → ℂ) (i : Fin 2 × D) : ℂ := if i.1=x then v i.2 else 0

omit [DecidableEq D] in
theorem tagged_normalized (x : Fin 2) (v : D → ℂ) (hv : amplitude v v = 1) :
    amplitude (tagged x v) (tagged x v) = 1 := by
  simpa [amplitude, dotProduct, tagged, Fintype.sum_prod_type] using hv

omit [DecidableEq D] in
theorem tagged_orthogonal (v w : D → ℂ) : amplitude (tagged 0 v) (tagged 1 w) = 0 := by
  simp [amplitude,dotProduct,tagged,Fintype.sum_prod_type]

omit [DecidableEq D] in
theorem column_gram (v w : D → ℂ) (hv : amplitude v v=1) (hw : amplitude w w=1) :
    (columns v w).conjTranspose * columns v w =
      !![1,amplitude v w; star (amplitude v w),1] := by
  have hc : amplitude w v = star (amplitude v w) := by
    simp [amplitude,dotProduct,star_sum,mul_comm]
  ext i j
  fin_cases i <;> fin_cases j
  · exact hv
  · rfl
  · exact hc
  · exact hw

theorem average_factorization (v w : D → ℂ) (hv : amplitude v v=1) (hw : amplitude w w=1) :
    densityMatrix (mixtureState halfPrior halfPrior_nonneg halfPrior_sum (purePair v w hv hw)) =
      ((1/2 : ℂ) • columns v w) * (columns v w).conjTranspose := by
  ext i j
  change (∑ x : Fin 2, halfPrior x • (purePair v w hv hw x).1) i j = _
  rw [Fin.sum_univ_two]
  change (1/2 : ℝ) • (v i * star (v j)) + (1-1/2 : ℝ) • (w i * star (w j)) = _
  simp [Matrix.mul_apply,Fin.sum_univ_two,columns,Matrix.conjTranspose_apply,Complex.real_smul]
  ring

theorem joint_factorization (v w : D → ℂ) (hv : amplitude v v=1) (hw : amplitude w w=1) :
    let V := columns (tagged 0 v) (tagged 1 w)
    densityMatrix (recordState halfPrior halfPrior_nonneg halfPrior_sum (purePair v w hv hw)) =
      ((1/2 : ℂ) • V) * V.conjTranspose := by
  dsimp only
  ext ⟨x,i⟩ ⟨y,j⟩
  change (∑ k : Fin 2, halfPrior k • ((diagonal (fun a => if a=k then (1:ℂ) else 0)) ⊗ₖ
    (densityMatrix (purePair v w hv hw k)))) (x,i) (y,j) = _
  rw [Fin.sum_univ_two]
  fin_cases x <;> fin_cases y <;>
    norm_num [halfPrior,binaryPrior,purePair,densityMatrix,Discrimination.pureSignal,
      Matrix.kroneckerMap_apply,Matrix.mul_apply,Fin.sum_univ_two,columns,tagged,
      Matrix.conjTranspose_apply,Complex.real_smul,Matrix.vecMulVec_apply] <;> ring

end SubentropyCertificates.BinarySpectra
