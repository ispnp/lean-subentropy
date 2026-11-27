module

public import SubentropyCertificates.PlateauEquality

/-! Alignment at the interior equality case, tested by the projection onto the pure state. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.InputInformationBalance (IsPure)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.BinarySpectra (densityMatrix)
open SubentropyCertificates.MixedQubit (traceDistance traceDistance_test)

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The state formula in Theorem 13; m+1 is the dimension of the orthogonal complement. -/
def extremalMatrix (m : ℕ) (δ : ℝ) (P : Matrix D D ℂ) : Matrix D D ℂ :=
  ((1 - δ : ℝ) : ℂ) • P + ((δ / (m + 1 : ℕ) : ℝ) : ℂ) • (1 - P)

omit [Fintype D] in
theorem extremalMatrix_affine (m : ℕ) (δ : ℝ) (P : Matrix D D ℂ) :
    extremalMatrix m δ P = ((δ / (m + 1 : ℕ) : ℝ) : ℂ) • 1 +
      ((1 - δ - δ / (m + 1 : ℕ) : ℝ) : ℂ) • P := by
  simp only [extremalMatrix, Complex.ofReal_sub, sub_smul, smul_sub]
  abel

private theorem reverse_test (ρ σ : DensityState D) (F : Matrix D D ℂ) :
    ((1-F)*(densityMatrix σ - densityMatrix ρ)).trace.re =
      (F*(densityMatrix ρ - densityMatrix σ)).trace.re := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_sub,
    show (densityMatrix ρ).trace = 1 from ρ.2.2, show (densityMatrix σ).trace = 1 from σ.2.2,
    sub_self, zero_sub, ← Matrix.trace_neg, ← Matrix.mul_neg, neg_sub]

theorem traceDistance_comm (ρ σ : DensityState D) : traceDistance ρ σ = traceDistance σ ρ := by
  suffices h : ∀ a b : DensityState D, traceDistance a b ≤ traceDistance b a from
    le_antisymm (h ρ σ) (h σ ρ)
  intro a b
  obtain ⟨E, he, hc, val, _⟩ := traceDistance_test a b
  obtain ⟨_, _, _, val', bound⟩ := traceDistance_test b a
  rw [← val, ← reverse_test a b E, ← val']
  exact bound (1-E) hc (by simpa using he)

theorem pure_density_projection (ρ : DensityState D) (hρ : IsPure ρ) :
    densityMatrix ρ * densityMatrix ρ = densityMatrix ρ ∧ (1-densityMatrix ρ).PosSemidef := by
  obtain ⟨v, hv⟩ := hρ
  have he : densityMatrix ρ = vecMulVec v (star v) := Matrix.ext hv
  have tr : (vecMulVec v (star v)).trace = 1 := he ▸ ρ.2.2
  have hn : star v ⬝ᵥ v = 1 := by
    simpa only [trace, diag_apply, vecMulVec_apply, dotProduct, mul_comm] using tr
  have hid : densityMatrix ρ * densityMatrix ρ = densityMatrix ρ := by
    rw [he, vecMulVec_mul_vecMulVec, hn, one_smul]
  refine ⟨hid, ?_⟩
  have hherm := Matrix.isHermitian_one.sub (density_posSemidef ρ).isHermitian
  have hsq : (1-densityMatrix ρ).conjTranspose * (1-densityMatrix ρ) = 1-densityMatrix ρ := by
    have hk : (1-densityMatrix ρ)*densityMatrix ρ = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hid, sub_self]
    rw [hherm.eq, Matrix.mul_sub, Matrix.mul_one, hk, sub_zero]
  exact hsq ▸ Matrix.posSemidef_conjTranspose_mul_self _

theorem interior_leading_gap (m : ℕ) {δ : ℝ} (hu : δ < uniformError m) :
    0 < 1 - δ - δ / (m + 1 : ℕ) := by
  have hb : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hd : (0 : ℝ) < (m + 2 : ℕ) := by positivity
  unfold uniformError at hu
  have h : 1 / ((m + 2 : ℕ) : ℝ) < 1 - δ := by linarith
  have := (div_lt_iff₀ hd).mp h
  apply sub_pos.mpr
  apply (div_lt_iff₀ hb).mpr
  push_cast at *
  nlinarith

/-- Distance at most δ forces the pure state to be the distinguished eigenprojection P
when the other state has the two interior eigenvalues on P and its complement. -/
theorem interior_projection_alignment (m : ℕ) {δ : ℝ} (hu : δ < uniformError m)
    (ρ σ : DensityState D) (hρ : IsPure ρ) (P : Matrix D D ℂ) (hp : P.IsHermitian)
    (hp2 : P*P = P) (hpt : P.trace = 1) (hs : densityMatrix σ = extremalMatrix m δ P)
    (hd : traceDistance ρ σ ≤ δ) : densityMatrix ρ = P := by
  let R := densityMatrix ρ
  have hr : R.IsHermitian := (density_posSemidef ρ).isHermitian
  have hrt : R.trace = 1 := ρ.2.2
  obtain ⟨hr2, hrc⟩ := pure_density_projection ρ hρ
  change R*R = R at hr2
  obtain ⟨E, _, _, hval, hmax⟩ := traceDistance_test ρ σ
  have ht := (hmax R (density_posSemidef ρ) hrc).trans (hval.le.trans hd)
  let a : ℝ := δ / (m + 1 : ℕ)
  have hs' : densityMatrix σ = (a : ℂ) • 1 + ((1-δ-a : ℝ) : ℂ) • P :=
    hs.trans (extremalMatrix_affine ..)
  change (R * (R - densityMatrix σ)).trace.re ≤ δ at ht
  rw [hs', Matrix.mul_sub, hr2, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    hrt] at ht
  simp only [smul_eq_mul, mul_one, Complex.sub_re, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.re_ofReal_mul] at ht
  have hgap : 0 < 1 - δ - a := interior_leading_gap m hu
  have hover : 1 ≤ (R*P).trace.re := by
    by_contra! hn
    nlinarith only [ht, mul_pos hgap (sub_pos.mpr hn)]
  let H := R-P
  have hnorm : (H.conjTranspose*H).trace.re = 2-2*(R*P).trace.re := by
    change ((R-P).conjTranspose*(R-P)).trace.re = _
    rw [(hr.sub hp).eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hr2, hp2,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm P R, hrt, hpt]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  have hpos := RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self H).trace_nonneg
  have hlo : 0 ≤ (H.conjTranspose*H).trace.re := hpos.1
  have hz : (H.conjTranspose*H).trace = 0 := Complex.ext
    (show (H.conjTranspose*H).trace.re = 0 by linarith only [hnorm, hover, hlo]) hpos.2
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz : H = 0)

end SubentropyCertificates.SpectralContinuity
