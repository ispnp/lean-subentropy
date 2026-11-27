module

public import SubentropyCertificates.OptimalGuessing

/-!
# Identical pure signals and exact attainment

The common signal is the normalized rank-one density matrix v v*. The
record matrix is an isometric embedding of the diagonal prior matrix,
which proves equality of their subentropies directly from the original
determinant-integral definition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra Kronecker

namespace SubentropyCertificates.Discrimination
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.ClassicalCurve

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

def pureSignal (v : B → ℂ) (hv : ∑ b, star (v b) * v b = 1) : DensityState B := by
  refine ⟨CStarMatrix.ofMatrix (Matrix.vecMulVec v (star v)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact (Matrix.posSemidef_vecMulVec_self_star v).nonneg
  · change (∑ b, v b * star (v b)) = 1
    simpa only [mul_comm] using hv

theorem pureSignal_matrix (v : B → ℂ) (hv : ∑ b, star (v b) * v b = 1) :
    CStarMatrix.ofMatrix.symm (pureSignal v hv).1 = Matrix.vecMulVec v (star v) := rfl

theorem pureSignal_subentropy (v : B → ℂ) (hv : ∑ b, star (v b) * v b = 1) :
    subentropy (pureSignal v hv) = 0 := matrixSubentropy_pure v hv

omit [DecidableEq X] in
theorem mixture_identical (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (σ : DensityState B) : mixtureState p hp hs (fun _ => σ) = σ := by
  apply Subtype.ext
  change (∑ x, p x • σ.1) = σ.1
  rw [← Finset.sum_smul, hs, one_smul]

def recordIsometry (v : B → ℂ) : Matrix (X × B) X ℂ :=
  fun i x => if i.1 = x then v i.2 else 0

omit [DecidableEq B] in
theorem recordIsometry_isometry (v : B → ℂ) (hv : ∑ b, star (v b) * v b = 1) :
    (recordIsometry (X := X) v).conjTranspose * recordIsometry (X := X) v = 1 := by
  ext x z
  by_cases hxz : x = z
  · subst z
    simpa [recordIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, eq_comm] using hv
  · simp [recordIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, hxz, eq_comm]

theorem record_identical_pure_matrix (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (v : B → ℂ) (hv : ∑ b, star (v b) * v b = 1) :
    CStarMatrix.ofMatrix.symm (recordState p hp hs (fun _ => pureSignal v hv)).1 =
      recordIsometry (X := X) v * diagonal (fun x => (p x : ℂ)) *
        (recordIsometry (X := X) v).conjTranspose := by
  ext i j
  change (∑ x, p x • ((Matrix.diagonal (fun k => if k = x then (1 : ℂ) else 0)) ⊗ₖ
    Matrix.vecMulVec v (star v))) i j = _
  simp only [Matrix.sum_apply, Matrix.smul_apply,
    Matrix.diagonal, Complex.real_smul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, recordIsometry]
  by_cases hij : i.1 = j.1
  · simp [hij, eq_comm]
    change v i.2 * (p j.1 : ℂ) * star (v j.2) = (p j.1 : ℂ) * (v i.2 * star (v j.2))
    ring
  · simp [hij, eq_comm]

theorem conditional_identical_pure (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (v : B → ℂ) (hv : ∑ b, star (v b) * v b = 1) :
    conditionalSubentropy p hp hs (fun _ => pureSignal v hv) = classicalSubentropy p := by
  unfold conditionalSubentropy
  rw [mixture_identical]
  change matrixSubentropy
    (CStarMatrix.ofMatrix.symm (recordState p hp hs (fun _ => pureSignal v hv)).1) -
      matrixSubentropy (Matrix.vecMulVec v (star v)) = classicalSubentropy p
  rw [record_identical_pure_matrix p hp hs v hv,
    matrixSubentropy_isometric_embedding _ _ (recordIsometry_isometry v hv),
    matrixSubentropy_pure v hv, sub_zero]
  rfl

omit [DecidableEq X] in
theorem identical_success_upper (p : X → ℝ) (σ : DensityState B)
    (i : X) (hmax : ∀ x, p x ≤ p i) (M : X → Matrix B B ℂ)
    (hM : ∀ x, (M x).PosSemidef) (hsM : ∑ x, M x = 1) :
    successProbability p (fun _ => σ) M ≤ p i := by
  have hn (x : X) : 0 ≤ (trace (M x * CStarMatrix.ofMatrix.symm σ.1)).re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef (hM x) (density_posSemidef σ)
  have ht : ∑ x, (trace (M x * CStarMatrix.ofMatrix.symm σ.1)).re = 1 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hsM, Matrix.one_mul]
    exact congrArg Complex.re σ.2.2
  calc
    _ ≤ ∑ x, p i * (trace (M x * CStarMatrix.ofMatrix.symm σ.1)).re :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hmax x) (hn x))
    _ = p i := by rw [← Finset.mul_sum, ht, mul_one]

omit [DecidableEq X] in
theorem pGuess_identical (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (σ : DensityState B) (i : X) (hmax : ∀ x, p x ≤ p i) :
    pGuess p (fun _ => σ) = p i := by
  apply le_antisymm
  · apply csSup_le (pGuess_bounds p hp hs (fun _ => σ)).1
    rintro a ⟨M, hM, hsM, rfl⟩
    exact identical_success_upper p σ i hmax M hM hsM
  · exact pGuess_ge_prior p hp hs (fun _ => σ) i

theorem extremal_probability_admissible (m : ℕ) {e : ℝ}
    (he : e ∈ Icc 0 (uniformError m)) :
    extremalVector m e ∈ probabilitySimplex (Option (Fin (m + 1))) :=
  extremal_probability m ⟨he.1, he.2.trans (uniformError_mem m).2⟩

theorem extremal_none_largest (m : ℕ) {e : ℝ} (he : e ∈ Icc 0 (uniformError m))
    (i : Option (Fin (m + 1))) : extremalVector m e i ≤ extremalVector m e none := by
  cases i with
  | none => exact le_rfl
  | some i =>
    have hn : (0 : ℝ) < (m + 2 : ℕ) := by positivity
    have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have h : 1 / ((m + 2 : ℕ) : ℝ) ≤ 1 - e := by
      have he' := he.2
      unfold uniformError at he'
      linarith
    have hmul := (div_le_iff₀ hn).mp h
    change e / (m + 1 : ℕ) ≤ 1 - e
    apply (div_le_iff₀ hm).mpr
    push_cast at hmul ⊢
    nlinarith

theorem identical_pure_attains_curve (m : ℕ) (e : ℝ) (he : e ∈ Icc 0 (uniformError m))
    (v : B → ℂ) (hv : ∑ b, star (v b) * v b = 1) :
    1 - pGuess (extremalVector m e) (fun _ => pureSignal v hv) = e ∧
      conditionalSubentropy (extremalVector m e) (extremal_probability_admissible m he).1
        (extremal_probability_admissible m he).2 (fun _ => pureSignal v hv) = phi m e := by
  have hp := extremal_probability_admissible m he
  constructor
  · rw [pGuess_identical _ hp.1 hp.2 (pureSignal v hv) none (extremal_none_largest m he)]
    simp only [extremalVector]
    ring
  · exact conditional_identical_pure _ hp.1 hp.2 v hv

theorem curve_attainable_in_dimension [Nonempty B] (m : ℕ) (e : ℝ)
    (he : e ∈ Icc 0 (uniformError m)) :
    ∃ (p : Option (Fin (m + 1)) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
      (ρ : Option (Fin (m + 1)) → DensityState B),
      1 - pGuess p ρ = e ∧ conditionalSubentropy p hp hs ρ = phi m e := by
  classical
  let b₀ : B := Classical.arbitrary B
  let v : B → ℂ := fun b => if b = b₀ then 1 else 0
  have hv : ∑ b, star (v b) * v b = 1 := by simp [v]
  have hp := extremal_probability_admissible m he
  exact ⟨extremalVector m e, hp.1, hp.2, fun _ => pureSignal v hv,
    identical_pure_attains_curve m e he v hv⟩

end SubentropyCertificates.Discrimination
