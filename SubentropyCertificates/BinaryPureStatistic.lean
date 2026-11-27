module

public import SubentropyCertificates.QuadraticDiscrimination
public import SubentropyCertificates.PinchingGeometry

/-! Exact moments of the weighted difference of two pure-state densities
and the quadratic statistic of their binary ensemble. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder
namespace SubentropyCertificates.Helstrom
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open SubentropyCertificates.Quadratic
open SubentropyCertificates.Discrimination
open SubentropyCertificates.PinchingEquality
variable {D : Type*} [Fintype D] [DecidableEq D]

def binaryPrior (p : ℝ) : Fin 2 → ℝ := ![p,1-p]

theorem binary_prior_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (i : Fin 2) : 0 ≤ binaryPrior p i := by
  fin_cases i <;> simp [binaryPrior,hp.1,sub_nonneg.mpr hp.2]

theorem binary_prior_sum (p : ℝ) : ∑ i, binaryPrior p i = 1 := by
  simp [binaryPrior,Fin.sum_univ_two]

def difference (p : ℝ) (ρ : Fin 2 → DensityState D) :=
  weighted (binaryPrior p) ρ 0 - weighted (binaryPrior p) ρ 1

theorem difference_hermitian {p : ℝ} (hp : p ∈ Icc 0 1) (ρ : Fin 2 → DensityState D) :
    (difference p ρ).IsHermitian :=
  ((density_posSemidef (ρ 0)).smul hp.1).isHermitian.sub
    ((density_posSemidef (ρ 1)).smul (sub_nonneg.mpr hp.2)).isHermitian

theorem difference_trace (p : ℝ) (ρ : Fin 2 → DensityState D) :
    (difference p ρ).trace.re = 2*p-1 := by
  have ht (i : Fin 2) : (CStarMatrix.ofMatrix.symm (ρ i).1).trace = 1 := (ρ i).2.2
  simp [difference,weighted,binaryPrior,Matrix.trace_sub,Matrix.trace_smul,ht,Complex.real_smul]
  ring

def purePair (v w : D → ℂ) (hv : ∑ i, star (v i)*v i=1) (hw : ∑ i, star (w i)*w i=1) :
    Fin 2 → DensityState D := ![pureSignal v hv, pureSignal w hw]

omit [DecidableEq D] in
theorem projector_overlap (v w : D → ℂ) :
    (projector v * projector w).trace.re = ‖amplitude v w‖^2 := by
  have hstar : v ⬝ᵥ star w = star (amplitude v w) := by
    simp [amplitude,dotProduct,star_sum,mul_comm]
  change (vecMulVec v (star v) * vecMulVec w (star w)).trace.re = _
  rw [Matrix.vecMulVec_mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_smul,smul_eq_mul,hstar]
  change (amplitude v w * star (amplitude v w)).re = _
  rw [Complex.star_def,Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]

omit [DecidableEq D] in
/-- Weighted projector traces are prior products times squared overlaps. -/
private theorem scaled_overlap (a b : ℝ) (v w : D → ℂ) :
    ((a • projector v)*(b • projector w)).trace.re = a*b*‖amplitude v w‖^2 := by
  rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_smul,Matrix.trace_smul]
  simp only [Complex.smul_re,smul_eq_mul,projector_overlap]
  ring

theorem binary_pure_statistic {p : ℝ} (hp : p ∈ Icc 0 1) (v w : D → ℂ)
    (hv : ∑ i, star (v i)*v i=1) (hw : ∑ i, star (w i)*w i=1) :
    statistic (binaryPrior p) (binary_prior_nonneg hp) (binary_prior_sum p) (purePair v w hv hw) =
      p*(1-p)*‖amplitude v w‖^2 := by
  rw [statistic_eq_unordered]
  simp only [Fin.sum_univ_two,lt_self_iff_false,Fin.zero_lt_one,not_lt_of_ge (Fin.zero_le 1),
    ite_true,ite_false,zero_add,add_zero]
  exact scaled_overlap p (1-p) v w

theorem difference_second_moment (p : ℝ) (v w : D → ℂ)
    (hv : ∑ i, star (v i)*v i=1) (hw : ∑ i, star (w i)*w i=1) :
    let H := difference p (purePair v w hv hw)
    (H*H).trace.re = p^2 + (1-p)^2 - 2*(p*(1-p)*‖amplitude v w‖^2) := by
  let A := p • projector v
  let B := (1-p) • projector w
  change ((A-B)*(A-B)).trace.re = _
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_sub,
    Matrix.trace_mul_comm B A]
  simp only [Complex.sub_re]
  have hᵥ : amplitude v v = 1 := hv
  have hᵥ' : amplitude w w = 1 := hw
  simp only [A,B,scaled_overlap,hᵥ,hᵥ',norm_one,one_pow,mul_one]
  ring

end SubentropyCertificates.Helstrom
