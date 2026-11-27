module

public import SubentropyCertificates.PinchingIntegral
import all SubentropyCertificates.PinchingIntegral
import all D5.S3.Quantum.Subentropy.PinchingGap
public import SubentropyCertificates.QuantumMeasurement

/-! Zero gain under block pinching. Strict Jensen equality identifies the
quadratic forms of a matrix and its pinching on the whole Gaussian space. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.PinchingEquality
open D5.S3.Quantum.Subentropy.GaussianQuadratic
open D5.S3.Quantum.Subentropy.EntropyJensenGap
open D5.S3.Quantum.Subentropy.PinchingGap
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Foundation.FiniteStateChannel
open SubentropyCertificates.MeasurementPosterior

private theorem eq_average_of_zero_gap {S : Type*} [Fintype S] [Nonempty S]
    (a : S → ℝ) (ha : ∀ s, 0 ≤ a s) (hz : entropyJensenGap a = 0) (s : S) :
    a s = finiteAverage a := by
  let w := (Fintype.card S : ℝ)⁻¹
  have hw : 0 < w := by dsimp [w]; positivity
  have hs : ∑ _ : S, w = 1 := by
    simp [w, nsmul_eq_mul, (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card S : ℝ) ≠ 0)]
  have h := Real.strictConcaveOn_negMulLog.map_sum_eq_iff' (t := Finset.univ)
    (w := fun _ : S => w) (p := a) (fun _ _ => hw.le) hs (fun i _ => ha i)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  exact h.mp (sub_eq_zero.mp hz) s (Finset.mem_univ _) hw.ne'

private theorem hermitian_eq_of_quadratics {D : Type*} [Fintype D] [DecidableEq D]
    {A C : Matrix D D ℂ} (hA : A.IsHermitian) (hC : C.IsHermitian)
    (h : ∀ z, gaussianQuadratic A z = gaussianQuadratic C z) : A = C := by
  have hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hC
  apply Matrix.toEuclideanLin.injective
  apply (ext_inner_map _ _).mp
  intro z
  rw [hS z z, hT z z, ← hS.coe_re_inner_self_apply z, ← hT.coe_re_inner_self_apply z]
  apply congrArg (fun t : ℝ => (t : ℂ))
  exact (div_left_inj' (by norm_num : (2 : ℝ) ≠ 0)).mp (h z)

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

theorem gain_zero_iff_blockPinch (i₀ : X × B) (A : Matrix (X × B) (X × B) ℂ)
    (hA : A.PosSemidef) (ht : A.trace = 1) : gain A = 0 ↔ A = blockPinch A := by
  constructor
  · intro hz
    have hi := pinch_gap_integral A hA ht i₀
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun z => (sign_orbit_entropy_laws A hA z).2.2.2) hi.1).mp (hi.2.symm.trans hz)
    let : (stdGaussian (EuclideanSpace ℂ (X × B))).IsOpenPosMeasure := gaussian_full_support
    have hall := Measure.eq_of_ae_eq hae (orbit_continuous A) continuous_const
    apply hermitian_eq_of_quadratics hA.isHermitian (pinch_positive A hA).isHermitian
    intro z
    let a := orbit A z
    have hgap : entropyJensenGap a = 0 :=
      (sign_orbit_entropy_laws A hA z).2.2.1.symm.trans (congrFun hall z)
    have ha s : 0 ≤ a s := quadratic_nonnegative (hA.mul_mul_conjTranspose_same _) z
    have he := eq_average_of_zero_gap a ha hgap (fun _ => false)
    have hid : signUnitary (B := B) (fun _ : X => false) = 1 := by
      exact Matrix.diagonal_one
    rw [quadratic_twirl_mean]
    change gaussianQuadratic A z = finiteAverage a
    rw [← he]
    simp only [a, orbit, hid, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  · intro he
    unfold gain
    rw [← he, sub_self]

theorem conditional_zero_iff_gram_fixed (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :
    conditionalSubentropy p hp hs ρ = 0 ↔
      (cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ =
        blockPinch ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ) := by
  classical
  have hX : Nonempty X := by
    by_contra h
    have : IsEmpty X := not_nonempty_iff.mp h
    simp at hs
  let x₀ := Classical.choice hX
  have hB : Nonempty B := by
    by_contra h
    have : IsEmpty B := not_nonempty_iff.mp h
    have ht := (ρ x₀).2.2
    simp [Matrix.trace] at ht
  rw [cq_conditional_eq_pinchingGap]
  exact gain_zero_iff_blockPinch (x₀, Classical.choice hB) _
    (Matrix.posSemidef_conjTranspose_mul_self _) (gram_trace_one p hp hs ρ)

theorem conditional_zero_iff_offDiagonal_gram (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :
    conditionalSubentropy p hp hs ρ = 0 ↔ ∀ x y : X, x ≠ y → ∀ b c : B,
      ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ) (x,b) (y,c) = 0 := by
  rw [conditional_zero_iff_gram_fixed]
  constructor
  · intro he x y hxy b c
    simpa only [blockPinch, ite_eq_right hxy] using congrArg
      (fun G : Matrix (X × B) (X × B) ℂ => G (x,b) (y,c)) he
  · intro h
    ext ⟨x,b⟩ ⟨y,c⟩
    by_cases he : x = y
    · simp [blockPinch, he]
    · simpa only [blockPinch, ite_eq_right he] using h x y he b c

end SubentropyCertificates.PinchingEquality
