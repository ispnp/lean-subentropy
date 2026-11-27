module

public import SubentropyCertificates.BinarySignalColumns

/-! The trace distance on density states and a test on the quantum register
of a classical record. All trace pairings below act on the full CQ matrix. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
namespace SubentropyCertificates.MixedQubit
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open SubentropyCertificates.BinarySpectra (densityMatrix)
open SubentropyCertificates.Discrimination
open SubentropyCertificates.Helstrom (spectral_test)
variable {D X : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X]

/-- The trace distance, half the sum of the absolute eigenvalues of the
Hermitian difference. -/
def traceDistance (ρ σ : DensityState D) : ℝ :=
  let H := (density_posSemidef ρ).isHermitian.sub (density_posSemidef σ).isHermitian
  (∑ i, |H.eigenvalues i|)/2

/-- The trace distance is the largest probability difference over all effects. -/
theorem traceDistance_test (ρ σ : DensityState D) :
    let H := densityMatrix ρ - densityMatrix σ
    ∃ E : Matrix D D ℂ, E.PosSemidef ∧ (1-E).PosSemidef ∧
      (E*H).trace.re = traceDistance ρ σ ∧
      ∀ F : Matrix D D ℂ, F.PosSemidef → (1-F).PosSemidef →
        (F*H).trace.re ≤ (E*H).trace.re := by
  let H := densityMatrix ρ - densityMatrix σ
  have htr : H.trace.re = 0 := by
    change ((densityMatrix ρ - densityMatrix σ).trace).re = 0
    rw [Matrix.trace_sub,show (densityMatrix ρ).trace=1 from ρ.2.2,
      show (densityMatrix σ).trace=1 from σ.2.2,sub_self,Complex.zero_re]
  obtain ⟨E,hE,hC,_,hval,hmax⟩ := spectral_test
    ((density_posSemidef ρ).isHermitian.sub (density_posSemidef σ).isHermitian)
  refine ⟨E,hE,hC,?_,hmax⟩
  change 2*(E*H).trace.re-H.trace.re = _ at hval
  unfold traceDistance
  linarith

/-- The CQ density of a constant signal factors into its classical label
distribution and the signal density. -/
theorem constant_record_matrix (p : X → ℝ) (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1)
    (σ : DensityState D) :
    densityMatrix (recordState p hp hs (fun _ => σ)) =
      diagonal (fun x => (p x:ℂ)) ⊗ₖ densityMatrix σ := by
  ext ⟨x,i⟩ ⟨y,j⟩
  change (∑ z,p z • ((diagonal (fun k => if k=z then (1:ℂ) else 0)) ⊗ₖ
    densityMatrix σ)) (x,i) (y,j) = _
  by_cases h : x=y
  · subst y
    simp [Matrix.sum_apply,Matrix.smul_apply,Complex.real_smul,Matrix.kroneckerMap_apply,
      eq_comm]
  · simp [Matrix.sum_apply,Matrix.smul_apply,Matrix.kroneckerMap_apply,h]

/-- The maximally mixed qubit. -/
def mixed : DensityState (Fin 2) := by
  let A := (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  refine ⟨CStarMatrix.ofMatrix A,map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    ((Matrix.PosSemidef.one.smul (by norm_num : (0:ℝ) ≤ 1/2)).nonneg),?_⟩
  change A.trace = 1
  norm_num [A,Matrix.trace_smul,Complex.real_smul]

theorem pure_projector_complement (v : Fin 2 → ℂ) (hv : ∑ i,star (v i)*v i=1) :
    let P := densityMatrix (pureSignal v hv)
    P*P=P ∧ (1-P).PosSemidef ∧ (1-P).trace=1 ∧ (1-P)*P=0 := by
  let P := densityMatrix (pureSignal v hv)
  have hid : P*P=P := by
    change vecMulVec v (star v)*vecMulVec v (star v) = _
    rw [Matrix.vecMulVec_mul_vecMulVec,show (star v ⬝ᵥ v)=1 from hv,one_smul]; rfl
  have hker : (1-P)*P=0 := by rw [Matrix.sub_mul,Matrix.one_mul,hid,sub_self]
  have hsame : (1-P).conjTranspose*(1-P)=1-P := by
    rw [(Matrix.isHermitian_one.sub (density_posSemidef (pureSignal v hv)).isHermitian).eq,
      Matrix.mul_sub,Matrix.mul_one,hker,sub_zero]
  refine ⟨hid,hsame ▸ Matrix.posSemidef_conjTranspose_mul_self (1-P),?_,hker⟩
  rw [Matrix.trace_sub,show P.trace=1 from (pureSignal v hv).2.2]
  norm_num

theorem mixed_ne_pure (v : Fin 2 → ℂ) (hv : ∑ i,star (v i)*v i=1) : mixed ≠ pureSignal v hv := by
  intro he
  have h := (pure_projector_complement v hv).1
  rw [← he] at h
  change ((1/2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))*((1/2:ℝ) • 1) = (1/2:ℝ) • 1 at h
  have entry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  norm_num [Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_apply,Complex.real_smul] at entry

end SubentropyCertificates.MixedQubit
