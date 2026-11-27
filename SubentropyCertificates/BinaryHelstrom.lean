module

public import SubentropyCertificates.HelstromSpectral
public import SubentropyCertificates.BinaryPureStatistic

/-! Binary Helstrom optimization over the project's original finite-POVM
success set. The spectral test attains the optimum, including ties. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder
namespace SubentropyCertificates.Helstrom
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.GuessingProbability
variable {D : Type*} [Fintype D] [DecidableEq D]

private theorem success_trace (p : ℝ) (ρ : Fin 2 → DensityState D) (M : Fin 2 → Matrix D D ℂ)
    (hs : ∑ i, M i = 1) :
    successProbability (binaryPrior p) ρ M = 1-p + (M 0 * difference p ρ).trace.re := by
  rw [Fin.sum_univ_two] at hs
  have hM : M 1 = 1-M 0 := by rw [← hs]; abel
  have ht : (CStarMatrix.ofMatrix.symm (ρ 1).1).trace = 1 := (ρ 1).2.2
  simp only [successProbability,Fin.sum_univ_two,hM,Matrix.sub_mul,Matrix.one_mul,
    Matrix.trace_sub,ht,Complex.sub_re,Complex.one_re,difference,Quadratic.weighted,
    Matrix.mul_sub,Matrix.mul_smul,Matrix.trace_smul,Complex.smul_re,smul_eq_mul]
  change p*_ + (1-p)*(1-_) = 1-p+(p*_-(1-p)*_)
  ring

/-- The optimal success is one half of one plus the sum of the absolute
eigenvalues of pρ₀-(1-p)ρ₁, its Hermitian trace norm. -/
theorem binary_helstrom {p : ℝ} (hp : p ∈ Icc 0 1) (ρ : Fin 2 → DensityState D) :
    pGuess (binaryPrior p) ρ = (1 + ∑ i, |(difference_hermitian hp ρ).eigenvalues i|)/2 ∧
    ∃ M : Fin 2 → Matrix D D ℂ, (∀ i, (M i).PosSemidef) ∧ ∑ i, M i = 1 ∧
      M 0 * M 0 = M 0 ∧ successProbability (binaryPrior p) ρ M = pGuess (binaryPrior p) ρ := by
  obtain ⟨E,hE,hC,hi,ht,hub⟩ := spectral_test (difference_hermitian hp ρ)
  let M : Fin 2 → Matrix D D ℂ := ![E,1-E]
  have hM (i : Fin 2) : (M i).PosSemidef := by fin_cases i <;> first | exact hE | exact hC
  have hs : ∑ i, M i = 1 := by rw [Fin.sum_univ_two]; change E+(1-E)=1; abel
  let s := successProbability (binaryPrior p) ρ M
  have hm : s ∈ successProbabilitySet (binaryPrior p) ρ := ⟨M,hM,hs,rfl⟩
  have hbound : ∀ a ∈ successProbabilitySet (binaryPrior p) ρ, a ≤ s := by
    rintro _ ⟨F,hF,hFs,rfl⟩
    have hc : 1-F 0=F 1 := by have h := hFs; rw [Fin.sum_univ_two] at h; rw [← h]; abel
    have h := hub (F 0) (hF 0) (hc.symm ▸ hF 1)
    dsimp only [s]
    rw [success_trace _ _ F hFs,success_trace _ _ M hs]
    exact add_le_add_right h _
  have hsup : pGuess (binaryPrior p) ρ = s :=
    le_antisymm (csSup_le ⟨_,hm⟩ hbound) (le_csSup ⟨_,hbound⟩ hm)
  refine ⟨?_,M,hM,hs,hi,hsup.symm⟩
  rw [hsup,show s = _ from success_trace p ρ M hs]
  rw [difference_trace] at ht
  change 1-p+(E*difference p ρ).trace.re = _
  linarith

end SubentropyCertificates.Helstrom
