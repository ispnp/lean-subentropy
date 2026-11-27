module

public import SubentropyCertificates.MeasurementPosterior

/-!
# Quantum measurements and Born posteriors

The matrix outcome type is independent of the classical signal-label type.
The row_block_contraction helper is ported, with attribution, from the
Omega Institute's POVMGram.lean at the fixed revision in the upstream audit
(Apache-2.0). The generalized Born-trace identities and comparison follow below.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
namespace SubentropyCertificates.MeasurementPosterior
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.PinchingGap
variable {X B Y : Type*} [Fintype X] [DecidableEq X]
  [Fintype B] [DecidableEq B] [Fintype Y]

/-- The coordinate projection selecting a classical label (as in upstream POVMGram). -/
def blockProjector (x : X) : Matrix (X × B) (X × B) ℂ :=
  Matrix.diagonal (fun i => if i.1 = x then 1 else 0)

theorem row_block_contraction (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (x : X) :
    ((cqRowSqrt p ρ * blockProjector (B := B) x : Matrix B (X × B) ℂ) *
      (cqRowSqrt p ρ).conjTranspose : Matrix B B ℂ) =
      p x • CStarMatrix.ofMatrix.symm (ρ x).1 := by
  let R : Matrix B B ℂ := CFC.sqrt (p x • CStarMatrix.ofMatrix.symm (ρ x).1)
  have hR : R.conjTranspose = R :=
    (CFC.sqrt_nonneg (p x • CStarMatrix.ofMatrix.symm (ρ x).1)).isSelfAdjoint.star_eq
  have hRsq : R * R = p x • CStarMatrix.ofMatrix.symm (ρ x).1 :=
    CFC.sqrt_mul_sqrt_self _ ((density_posSemidef (ρ x)).smul (hp x)).nonneg
  have heq : ((cqRowSqrt p ρ * blockProjector (B := B) x : Matrix B (X × B) ℂ) *
      (cqRowSqrt p ρ).conjTranspose : Matrix B B ℂ) =
      R * R.conjTranspose := by
    ext b c
    conv_lhs => rw [Matrix.mul_apply]
    conv_rhs => rw [Matrix.mul_apply]
    simp only [blockProjector, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  rw [heq, hR, hRsq]

def ensembleMatrix (p : X → ℝ) (ρ : X → DensityState B) : Matrix B B ℂ :=
  ∑ x, p x • CStarMatrix.ofMatrix.symm (ρ x).1

def effectGram (p : X → ℝ) (ρ : X → DensityState B) (F : Matrix B B ℂ) :
    Matrix (X × B) (X × B) ℂ :=
  (cqRowSqrt p ρ).conjTranspose * F * cqRowSqrt p ρ

/-- The real Born probability of an outcome. It is proved real and nonnegative below. -/
def outcomeProbability (p : X → ℝ) (ρ : X → DensityState B) (F : Matrix B B ℂ) : ℝ :=
  (trace (F * ensembleMatrix p ρ)).re

def jointProbability (p : X → ℝ) (ρ : X → DensityState B)
    (F : Matrix B B ℂ) (x : X) : ℝ :=
  p x * (trace (F * CStarMatrix.ofMatrix.symm (ρ x).1)).re

/-- Used only for outcomes with positive outcomeProbability. -/
def posterior (p : X → ℝ) (ρ : X → DensityState B) (F : Matrix B B ℂ) (x : X) : ℝ :=
  jointProbability p ρ F x / outcomeProbability p ρ F

omit [DecidableEq X] in
theorem effectGram_posSemidef (p : X → ℝ) (ρ : X → DensityState B)
    (F : Matrix B B ℂ) (hF : F.PosSemidef) : (effectGram p ρ F).PosSemidef :=
  hF.conjTranspose_mul_mul_same _

omit [Fintype X] [DecidableEq X] in
theorem sum_effectGram (p : X → ℝ) (ρ : X → DensityState B)
    (F : Y → Matrix B B ℂ) (hsF : ∑ y, F y = 1) :
    (∑ y, effectGram p ρ (F y)) = (cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ := by
  simp only [effectGram]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hsF, Matrix.mul_one]

theorem effectGram_trace (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (ρ : X → DensityState B)
    (F : Matrix B B ℂ) : (effectGram p ρ F).trace = trace (F * ensembleMatrix p ρ) := by
  let V := cqRowSqrt p ρ
  calc
    _ = trace (V * (V.conjTranspose * F)) := Matrix.trace_mul_comm _ _
    _ = trace ((V * V.conjTranspose) * F) := by rw [Matrix.mul_assoc]
    _ = trace (F * (V * V.conjTranspose)) := Matrix.trace_mul_comm _ _
    _ = _ := by rw [row_mul_adjoint p hp ρ]; rfl

theorem mass_effectGram (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (ρ : X → DensityState B)
    (F : Matrix B B ℂ) : mass (effectGram p ρ F) = outcomeProbability p ρ F := by
  unfold mass outcomeProbability
  rw [effectGram_trace p hp ρ F]

theorem labelMass_eq_projector_trace (G : Matrix (X × B) (X × B) ℂ) (x : X) :
    labelMass G x = (trace (blockProjector (B := B) x * G)).re := by
  simp [labelMass, blockProjector, Matrix.trace, Matrix.diagonal_mul,
    Fintype.sum_prod_type, apply_ite]

theorem labelMass_effectGram (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (ρ : X → DensityState B)
    (F : Matrix B B ℂ) (x : X) : labelMass (effectGram p ρ F) x = jointProbability p ρ F x := by
  let V := cqRowSqrt p ρ
  have ht : trace (blockProjector x * effectGram p ρ F) =
      p x • trace (F * CStarMatrix.ofMatrix.symm (ρ x).1) := by
    calc
      _ = trace ((blockProjector x * V.conjTranspose) * (F * V)) := by
        simp only [effectGram, V, Matrix.mul_assoc]
      _ = trace ((F * V) * (blockProjector x * V.conjTranspose)) := Matrix.trace_mul_comm _ _
      _ = trace (F * ((V * blockProjector (B := B) x) * V.conjTranspose)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [row_block_contraction p hp ρ x, Matrix.mul_smul, Matrix.trace_smul]
  rw [labelMass_eq_projector_trace, ht]
  simp only [jointProbability, Complex.smul_re, smul_eq_mul]

theorem gram_trace_one (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) :
    ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ).trace = 1 := by
  rw [Matrix.trace_mul_comm, row_mul_adjoint p hp ρ, Matrix.trace_sum]
  simp only [Matrix.trace_smul, show ∀ x, trace
    (CStarMatrix.ofMatrix.symm (ρ x).1) = 1 from fun x => (ρ x).2.2,
    Complex.real_smul, mul_one, ← Complex.ofReal_sum, hs, Complex.ofReal_one]

theorem outcomeProbability_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (F : Matrix B B ℂ) (hF : F.PosSemidef) :
    0 ≤ outcomeProbability p ρ F := by
  rw [← mass_effectGram p hp ρ F]
  exact mass_nonneg _ (effectGram_posSemidef p ρ F hF)

theorem jointProbability_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (F : Matrix B B ℂ) (hF : F.PosSemidef) (x : X) :
    0 ≤ jointProbability p ρ F x := by
  rw [← labelMass_effectGram p hp ρ F x]
  exact labelMass_nonneg _ (effectGram_posSemidef p ρ F hF) x

theorem sum_jointProbability (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (F : Matrix B B ℂ) :
    ∑ x, jointProbability p ρ F x = outcomeProbability p ρ F := by
  simp_rw [← labelMass_effectGram p hp ρ F]
  rw [sum_labelMass, mass_effectGram p hp ρ F]

theorem outcome_trace_eq_real_probability (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (F : Matrix B B ℂ) (hF : F.PosSemidef) :
    trace (F * ensembleMatrix p ρ) = (outcomeProbability p ρ F : ℂ) := by
  calc
    _ = trace (effectGram p ρ F) := (effectGram_trace p hp ρ F).symm
    _ = (mass (effectGram p ρ F) : ℂ) :=
      psd_trace_eq_real_mass _ (effectGram_posSemidef p ρ F hF)
    _ = _ := by rw [mass_effectGram p hp ρ F]

theorem sum_outcomeProbability (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B)
    (F : Y → Matrix B B ℂ) (hsF : ∑ y, F y = 1) :
    ∑ y, outcomeProbability p ρ (F y) = 1 := by
  simp_rw [← mass_effectGram p hp ρ]
  simp only [mass, ← Complex.re_sum, ← Matrix.trace_sum]
  rw [sum_effectGram p ρ F hsF, gram_trace_one p hp hs ρ]
  rfl

theorem jointProbability_eq_zero_of_outcome_zero (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (F : Matrix B B ℂ) (hF : F.PosSemidef)
    (hz : outcomeProbability p ρ F = 0) (x : X) : jointProbability p ρ F x = 0 := by
  have hzero : effectGram p ρ F = 0 := psd_eq_zero_of_mass_zero _
    (effectGram_posSemidef p ρ F hF) (by rw [mass_effectGram p hp ρ F]; exact hz)
  rw [← labelMass_effectGram p hp ρ F x, hzero]
  simp [labelMass]

theorem posterior_probability (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (F : Matrix B B ℂ) (hF : F.PosSemidef)
    (hpos : 0 < outcomeProbability p ρ F) :
    (∀ x, 0 ≤ posterior p ρ F x) ∧ ∑ x, posterior p ρ F x = 1 := by
  refine ⟨fun x => div_nonneg (jointProbability_nonneg p hp ρ F hF x) hpos.le, ?_⟩
  simp only [posterior, ← Finset.sum_div, sum_jointProbability p hp ρ F,
    div_self (ne_of_gt hpos)]

/-- The paper's comparison, for mixed signals and arbitrary finite POVMs.
Equality characterizations and the sharp discrimination curve are separate targets. -/
theorem measurement_posterior_comparison
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hsF : ∑ y, F y = 1) :
    0 ≤ conditionalSubentropy p hp hs ρ ∧
    conditionalSubentropy p hp hs ρ ≤
      ∑ y ∈ Finset.univ.filter (fun y => 0 < outcomeProbability p ρ (F y)),
        outcomeProbability p ρ (F y) * matrixSubentropy
          (diagonal (fun x => (posterior p ρ (F y) x : ℂ))) := by
  classical
  have hX : Nonempty X := by
    by_contra h
    have : IsEmpty X := not_nonempty_iff.mp h
    simp at hs
  let x₀ : X := Classical.choice hX
  have hB : Nonempty B := by
    by_contra h
    have : IsEmpty B := not_nonempty_iff.mp h
    have ht := (ρ x₀).2.2
    simp [Matrix.trace] at ht
  let i₀ : X × B := (x₀, Classical.choice hB)
  let G : Y → Matrix (X × B) (X × B) ℂ := fun y => effectGram p ρ (F y)
  have hG (y : Y) : (G y).PosSemidef := effectGram_posSemidef p ρ (F y) (hF y)
  have htotal : (∑ y, G y) = (cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ :=
    sum_effectGram p ρ F hsF
  have htrace := gram_trace_one p hp hs ρ
  refine ⟨?_, ?_⟩
  · rw [cq_conditional_eq_pinchingGap]
    exact (actual_pinching_gap_laws i₀).2 _
      (Matrix.posSemidef_conjTranspose_mul_self _) htrace
  · have ht : (∑ y, G y).trace = 1 := by rw [htotal]; exact htrace
    have h := pinching_gap_le_outcome_average G hG ht x₀ i₀
    rw [htotal] at h
    rw [cq_conditional_eq_pinchingGap]
    simpa only [G, labelPosterior, mass_effectGram p hp ρ,
      labelMass_effectGram p hp ρ, posterior] using h

end SubentropyCertificates.MeasurementPosterior

