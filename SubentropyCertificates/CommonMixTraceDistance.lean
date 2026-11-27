module

public import SubentropyCertificates.PositiveBlockSegment
public import SubentropyCertificates.QubitTraceDistance

/-! Exact scaling of the joint trace distance under common mixing. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open SubentropyCertificates.BinarySpectra (densityMatrix)
open SubentropyCertificates.MixedQubit (traceDistance traceDistance_test)

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

omit [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D] in
/-- Every convex combination of positive semidefinite blocks is positive semidefinite. -/
theorem blockSegment_posSemidef (A B : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef)
    {s : ℝ} (hs : s ∈ Icc 0 1) (x : X) : (blockSegment A B s x).PosSemidef :=
  ((ha x).smul (sub_nonneg.mpr hs.2)).add ((hb x).smul hs.1)

private theorem traceDistance_of_scaled_difference (ρ σ ρ' σ' : DensityState D)
    (k : ℝ) (hk : 0 ≤ k)
    (hd : densityMatrix ρ' - densityMatrix σ' = k • (densityMatrix ρ - densityMatrix σ)) :
    traceDistance ρ' σ' = k * traceDistance ρ σ := by
  have hpair (T : Matrix D D ℂ) :
      (T * (densityMatrix ρ' - densityMatrix σ')).trace.re =
        k * (T * (densityMatrix ρ - densityMatrix σ)).trace.re := by
    rw [hd, Matrix.mul_smul, trace_smul, Complex.smul_re, smul_eq_mul]
  obtain ⟨E, he, hc, hv, hm⟩ := traceDistance_test ρ σ
  obtain ⟨F, hf, hf', hw, hn⟩ := traceDistance_test ρ' σ'
  rw [← hv, ← hw, hpair F]
  exact le_antisymm (mul_le_mul_of_nonneg_left (hm F hf hf') hk)
    (by simpa only [hpair] using hn E he hc)

/-- Mixing two CQ states with the same normalized state scales their joint trace distance
by the retained weight, including when some blocks have zero rank. -/
theorem commonMix_traceDistance (A B U : X → Matrix D D ℂ)
    (ha : ∀ x, (A x).PosSemidef) (hb : ∀ x, (B x).PosSemidef) (hu : ∀ x, (U x).PosSemidef)
    (hta : (∑ x, A x).trace = 1) (htb : (∑ x, B x).trace = 1) (htu : (∑ x, U x).trace = 1)
    {e : ℝ} (he : e ∈ Icc 0 1) :
    traceDistance
      (blockDensity (blockSegment A U e) (blockSegment_posSemidef A U ha hu he)
        (blockSegment_trace A U e hta htu))
      (blockDensity (blockSegment B U e) (blockSegment_posSemidef B U hb hu he)
        (blockSegment_trace B U e htb htu)) =
      (1 - e) * traceDistance (blockDensity A ha hta) (blockDensity B hb htb) := by
  apply traceDistance_of_scaled_difference _ _ _ _ _ (sub_nonneg.mpr he.2)
  change blockDiagonal (blockSegment A U e) - blockDiagonal (blockSegment B U e) =
    (1 - e) • (blockDiagonal A - blockDiagonal B)
  rw [← blockDiagonal_sub, ← blockDiagonal_sub, ← blockDiagonal_smul]
  congr 1
  funext x
  change ((1 - e) • A x + e • U x) - ((1 - e) • B x + e • U x) = (1 - e) • (A x - B x)
  rw [add_sub_add_right_eq_sub, smul_sub]

end SubentropyCertificates.ConditionalContinuity

