module
public import SubentropyCertificates.QuantumEquality
public import SubentropyCertificates.PinchingGeometry

/-! A pure Gram matrix gives a common normalized signal vector. We factor
the rectangular row map and take the trace of each weighted signal block,
so zero-prior signals need no restrictions. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.PinchingEquality
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open SubentropyCertificates.MeasurementPosterior
open SubentropyCertificates.Discrimination

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

theorem common_pure_signal_of_gram_projector (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (v : X × B → ℂ) (hv : amplitude v v = 1)
    (hG : (cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ = projector v) :
    ∃ (u : B → ℂ) (hu : ∑ b, star (u b) * u b = 1),
      ∀ x, 0 < p x → ρ x = pureSignal u hu := by
  let M := cqRowSqrt p ρ
  let V : Matrix (X × B) Unit ℂ := fun i _ => v i
  let U := M * V
  let u (b : B) := U b ()
  have hV : V.conjTranspose * V = 1 := by
    ext i j
    change amplitude v v = (1 : Matrix Unit Unit ℂ) i j
    simpa using hv
  have hVV : V * V.conjTranspose = projector v := by
    ext i j
    change (∑ _k : Unit, v i * star (v j)) = _
    simp [projector, vecMulVec]
  have hMV : M.conjTranspose * M = V * V.conjTranspose := hG.trans hVV.symm
  have hU : U.conjTranspose * U = 1 := by
    calc
      _ = V.conjTranspose * (M.conjTranspose * M) * V := by simp only [U, conjTranspose_mul, Matrix.mul_assoc]
      _ = (V.conjTranspose * V) * (V.conjTranspose * V) := by rw [hMV]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV, mul_one]
  have hu : ∑ b, star (u b) * u b = 1 := congrArg (fun A : Matrix Unit Unit ℂ => A () ()) hU
  have horth : (V * V.conjTranspose) * (1 - V * V.conjTranspose) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have hid : V * V.conjTranspose * (V * V.conjTranspose) = V * V.conjTranspose := by
      calc
        _ = V * (V.conjTranspose * V) * V.conjTranspose := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV, Matrix.mul_one]
    rw [hid, sub_self]
  have hzero : M * (1 - V * V.conjTranspose) = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc
      _ = (1 - V * V.conjTranspose).conjTranspose * ((M.conjTranspose * M) *
          (1 - V * V.conjTranspose)) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hMV, horth, Matrix.mul_zero]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hzero
  have hfac : M = U * V.conjTranspose := hzero.trans (Matrix.mul_assoc _ _ _).symm
  have htrace : (U * U.conjTranspose).trace = 1 := by
    rw [Matrix.trace_mul_comm, hU]
    simp
  refine ⟨u, hu, ?_⟩
  intro x hx
  let K := V.conjTranspose * blockProjector (B := B) x * V
  let c := K () ()
  have hK : K = c • (1 : Matrix Unit Unit ℂ) := by
    ext i j
    cases i; cases j; simp [c]
  have hsignal : p x • CStarMatrix.ofMatrix.symm (ρ x).1 = c • (U * U.conjTranspose) := by
    calc
      _ = M * blockProjector x * M.conjTranspose := (row_block_contraction p hp ρ x).symm
      _ = U * K * U.conjTranspose := by
        conv_lhs => rw [hfac]
        simp only [K, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [hK, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hc := congrArg Matrix.trace hsignal
  simp only [Matrix.trace_smul, show (CStarMatrix.ofMatrix.symm (ρ x).1).trace = 1 from (ρ x).2.2,
    htrace, Complex.real_smul, smul_eq_mul, mul_one] at hc
  apply Subtype.ext
  apply Matrix.ext
  intro a b
  have hentry := congrArg (fun A : Matrix B B ℂ => A a b) hsignal
  rw [← hc] at hentry
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_unique] at hentry
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hx.ne') hentry

end SubentropyCertificates.PinchingEquality
