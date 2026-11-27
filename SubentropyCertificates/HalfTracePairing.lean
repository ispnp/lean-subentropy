module

public import SubentropyCertificates.HelstromSpectral
public import SubentropyCertificates.SpatialSignBlockDiagonal

/-! Trace pairings of a positive operator with a traceless Hermitian perturbation. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity

variable {D X : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X]

/-- For a traceless perturbation, the tests F and I - F give opposite trace pairings. -/
private theorem effect_pairing_half {F H : Matrix D D ℂ} (hh : H.IsHermitian)
    (ht : H.trace = 0) (hf : 0 ≤ F) (hu : F ≤ 1) :
    |(F * H).trace.re| ≤ (∑ i, |hh.eigenvalues i|) / 2 := by
  obtain ⟨E, _, _, _, he, hmax⟩ := SubentropyCertificates.Helstrom.spectral_test hh
  have hupper := hmax F hf.posSemidef (sub_nonneg.mpr hu).posSemidef
  have hother : (1 - (1 - F)).PosSemidef := by simpa using hf.posSemidef
  have hlower := hmax (1 - F) (sub_nonneg.mpr hu).posSemidef hother
  rw [Matrix.sub_mul, Matrix.one_mul, trace_sub, ht, zero_sub, Complex.neg_re] at hlower
  rw [ht, Complex.zero_re, sub_zero] at he
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- If 0 ≤ B ≤ k I and H is Hermitian with trace zero, the absolute trace pairing is
bounded by k times half the sum of the absolute eigenvalues of H. -/
theorem trace_pairing_half_bound {B H : Matrix D D ℂ} (k : ℝ) (hk : 0 ≤ k)
    (hb : 0 ≤ B) (hu : B ≤ k • 1) (hh : H.IsHermitian) (ht : H.trace = 0) :
    |(B * H).trace.re| ≤ k * ((∑ i, |hh.eigenvalues i|) / 2) := by
  rcases hk.eq_or_lt with h | h
  · subst k
    have he : B = 0 := le_antisymm (by simpa using hu) hb
    simp [he]
  · let F := k⁻¹ • B
    have hp : 0 ≤ F := smul_nonneg (inv_nonneg.mpr hk) hb
    have hf : F ≤ 1 := by
      simpa [F, smul_smul, h.ne'] using smul_le_smul_of_nonneg_left hu (inv_nonneg.mpr hk)
    have he := effect_pairing_half hh ht hp hf
    have hb' : k • F = B := by simp [F, smul_smul, h.ne']
    rw [← hb', Matrix.smul_mul, trace_smul]
    simpa [Complex.real_smul, abs_mul, abs_of_nonneg hk] using mul_le_mul_of_nonneg_left he hk

omit [Fintype D] [DecidableEq D] [Fintype X] in
/-- A direct sum of Hermitian blocks is Hermitian. -/
theorem blockHermitian (H : X → Matrix D D ℂ) (hh : ∀ x, (H x).IsHermitian) :
    (blockDiagonal H).IsHermitian := by
  change (blockDiagonal H)ᴴ = blockDiagonal H
  rw [blockDiagonal_conjTranspose]
  exact congrArg blockDiagonal (funext fun x ↦ (hh x).eq)

/-- The half-trace bound for a whole block family only needs the total trace to vanish. -/
theorem block_pairing_half_bound (B H : X → Matrix D D ℂ) (k : ℝ) (hk : 0 ≤ k)
    (hb : ∀ x, 0 ≤ B x) (hu : ∀ x, B x ≤ k • 1) (hh : ∀ x, (H x).IsHermitian)
    (ht : (∑ x, H x).trace = 0) :
    |∑ x, ((B x * H x).trace).re| ≤ k * ((∑ i, |(blockHermitian H hh).eigenvalues i|) / 2) := by
  have hp := (blocks_posSemidef B (fun x ↦ (hb x).posSemidef)).nonneg
  have hu' : blockDiagonal B ≤ k • 1 := by
    have h := (blocks_posSemidef (k • (1 : X → Matrix D D ℂ) - B)
      (fun x ↦ (sub_nonneg.mpr (hu x)).posSemidef)).nonneg
    rw [blockDiagonal_sub, blockDiagonal_smul, blockDiagonal_one] at h
    exact sub_nonneg.mp h
  have htr : (blockDiagonal H).trace = 0 := by
    simpa only [trace_blockDiagonal, trace_sum] using ht
  simpa only [← blockDiagonal_mul, trace_blockDiagonal, Complex.re_sum] using
    trace_pairing_half_bound k hk hp hu' (blockHermitian H hh) htr

end SubentropyCertificates.ConditionalContinuity
