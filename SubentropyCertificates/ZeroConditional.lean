module

public import SubentropyCertificates.ZeroPinching
public import SubentropyCertificates.OrthogonalMeasurement
public import SubentropyCertificates.SharpDiscriminationEquality
import all D5.S3.Quantum.Subentropy.ClassicalQuantumGram

/-! Zero conditional subentropy, orthogonal supports and perfect guessing
for finite ensembles. Only labels of strictly positive prior constrain the
supports, and no lower bound on the number of labels is required. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.ZeroConditional
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.PinchingEquality
open SubentropyCertificates.MeasurementPosterior
open SubentropyCertificates.QuantumEquality
open SubentropyCertificates.Discrimination

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

theorem conditional_zero_iff_root_products (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :
    conditionalSubentropy p hp hs ρ = 0 ↔
      ∀ x y, x ≠ y → weightedRoot p ρ x * weightedRoot p ρ y = 0 := by
  rw [conditional_zero_iff_offDiagonal_gram]
  have hentry (x y : X) (b c : B) :
      ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ) (x,b) (y,c) =
        (weightedRoot p ρ x * weightedRoot p ρ y) b c := by
    change ((weightedRoot p ρ x).conjTranspose * weightedRoot p ρ y) b c = _
    rw [root_adjoint]
  simp only [hentry]
  constructor
  · intro h x y hxy
    exact Matrix.ext (h x y hxy)
  · intro h x y hxy b c
    rw [h x y hxy, Matrix.zero_apply]

theorem orthogonal_supports_of_conditional_zero (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (hz : conditionalSubentropy p hp hs ρ = 0) :
    orthogonalSupports p ρ := by
  intro x y hxy hx hy
  let A (j : X) := CStarMatrix.ofMatrix.symm (ρ j).1
  let R := weightedRoot p ρ
  have hr : R x * R y = 0 := (conditional_zero_iff_root_products p hp hs ρ).mp hz x y hxy
  have hscaled : p x • (p y • (A x * A y)) = 0 := by
    calc
      _ = (p x • A x) * (p y • A y) := by rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = (R x * R x) * (R y * R y) := by rw [root_square p hp ρ x, root_square p hp ρ y]
      _ = R x * ((R x * R y) * R y) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hr, Matrix.zero_mul, Matrix.mul_zero]
  have hprod : A x * A y = 0 :=
    (smul_eq_zero.mp ((smul_eq_zero.mp hscaled).resolve_left hx.ne')).resolve_left hy.ne'
  have hlin := congrArg Matrix.toEuclideanLin hprod
  rw [Matrix.toLpLin_mul_same, map_zero] at hlin
  apply Submodule.isOrtho_iff_inner_eq.mpr
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (density_posSemidef (ρ x)).isHermitian
  rw [hsym u _]
  change inner ℂ u (((A x).toEuclideanLin ∘ₗ (A y).toEuclideanLin) v) = 0
  simp [hlin]

theorem conditional_zero_of_perfect_guessing (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (h : pGuess p ρ = 1) :
    conditionalSubentropy p hp hs ρ = 0 := by
  obtain ⟨M, hM, hsM, he⟩ := (pGuess_one_iff_perfect_povm p hp hs ρ).mp h
  have hd : decisionSuccess p ρ M id = 1 := by
    simpa only [decisionSuccess, jointProbability, successProbability, id_eq] using he
  have hpost := (perfect_decision_iff p hp hs ρ M hM hsM id).mp hd
  exact ((zero_and_posterior_equality_iff p hp hs ρ M hM hsM).mpr
    (fun y hy => ⟨y, hpost y hy⟩)).1

theorem pGuess_one_of_orthogonal_supports (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (ho : orthogonalSupports p ρ) :
    pGuess p ρ = 1 := by
  obtain ⟨M, hM, hsM, he⟩ := perfect_projective_measurement_of_orthogonal_supports p hp hs ρ ho
  exact (pGuess_one_iff_perfect_povm p hp hs ρ).mpr
    ⟨M, fun x => (hM x).nonneg.posSemidef, hsM, he⟩

/-- The three equivalent conditions of the zero conditional subentropy corollary. -/
theorem zero_conditional_equivalences (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :
    (conditionalSubentropy p hp hs ρ = 0 ↔ pGuess p ρ = 1) ∧
      (pGuess p ρ = 1 ↔ orthogonalSupports p ρ) ∧
      (conditionalSubentropy p hp hs ρ = 0 ↔ orthogonalSupports p ρ) := by
  have a := orthogonal_supports_of_conditional_zero p hp hs ρ
  have b := pGuess_one_of_orthogonal_supports p hp hs ρ
  have c := conditional_zero_of_perfect_guessing p hp hs ρ
  exact ⟨⟨b ∘ a, c⟩, ⟨a ∘ c, b⟩, ⟨a, c ∘ b⟩⟩

end SubentropyCertificates.ZeroConditional
