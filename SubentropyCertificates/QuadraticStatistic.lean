module

public import SubentropyCertificates.QuadraticGram
import all D5.S3.Quantum.Subentropy.ClassicalQuantumGram

/-! Identify the overlap statistic with the two state purities and with
the off-block squared norm of the ensemble Gram matrix. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped ComplexOrder MatrixOrder BigOperators
namespace SubentropyCertificates.Quadratic
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

def purity {D : Type*} [Fintype D] [DecidableEq D] (σ : DensityState D) : ℝ :=
  let R := CStarMatrix.ofMatrix.symm σ.1
  (R*R).trace.re

def statistic (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :=
  (purity (mixtureState p hp hs ρ) - purity (recordState p hp hs ρ))/2

def weighted (p : X → ℝ) (ρ : X → DensityState B) (x : X) : Matrix B B ℂ :=
  p x • CStarMatrix.ofMatrix.symm (ρ x).1

def overlap (p : X → ℝ) (ρ : X → DensityState B) (x z : X) :=
  ((weighted p ρ x * weighted p ρ z).trace).re

theorem statistic_eq_overlaps (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) :
    statistic p hp hs ρ = (∑ z ∈ distinctPairs X, overlap p ρ z.1 z.2)/2 := by
  have hmix : purity (mixtureState p hp hs ρ) = ∑ x, ∑ z, overlap p ρ x z := by
    change (((∑ x, weighted p ρ x) * ∑ x, weighted p ρ x).trace).re = _
    rw [Matrix.sum_mul]
    simp only [Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum,overlap]
  let R := CStarMatrix.ofMatrix.symm (recordState p hp hs ρ).1
  have hentry (x z : X) (b d : B) : R (x,b) (z,d) = if x=z then weighted p ρ x b d else 0 := by
    simpa only [weighted,Matrix.smul_apply,Complex.real_smul] using
      record_entries p hp hs ρ (x,b) (z,d)
  have hrec : purity (recordState p hp hs ρ) = ∑ x, overlap p ρ x x := by
    change (R*R).trace.re = _
    simp only [overlap,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fintype.sum_prod_type,
      hentry,Complex.re_sum]
    congr 1
    funext x
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_eq_single x]
    · simp
    · intro z _ hz
      simp [hz,Ne.symm hz]
    · simp
  rw [statistic,hmix,hrec,distinct_sum]

theorem statistic_eq_gram (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) :
    statistic p hp hs ρ = offSquare ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ)/2 := by
  rw [statistic_eq_overlaps]
  congr 1
  apply Finset.sum_congr rfl
  intro xz _
  let U := weightedRoot p ρ xz.1
  let V := weightedRoot p ρ xz.2
  let W := U.conjTranspose * V
  have hU : U.conjTranspose = U := root_adjoint p ρ _
  have hV : V.conjTranspose = V := root_adjoint p ρ _
  have hUU : U*U = weighted p ρ xz.1 := root_square p hp ρ _
  have hVV : V*V = weighted p ρ xz.2 := root_square p hp ρ _
  have htrace : (W*W.conjTranspose).trace = (weighted p ρ xz.1 * weighted p ρ xz.2).trace := by
    simp only [W,Matrix.conjTranspose_mul,hU,hV]
    rw [show (U*V)*(V*U) = (U*(V*V))*U by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm (U*(V*V)) U, ← Matrix.mul_assoc, hUU,hVV]
  change (weighted p ρ xz.1 * weighted p ρ xz.2).trace.re =
    ∑ k : B × B, Complex.normSq (W k.1 k.2)
  rw [← htrace]
  have hc (v : ℂ) : v * star v = (Complex.normSq v : ℂ) := Complex.mul_conj v
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Complex.re_sum,hc,Complex.ofReal_re,Fintype.sum_prod_type]

/-- With an ordering of the labels the statistic sums each distinct pair once. -/
theorem statistic_eq_unordered {L : Type*} [Fintype L] [LinearOrder L]
    (p : L → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (ρ : L → DensityState B) :
    statistic p hp hs ρ = ∑ x, ∑ z, if x<z then overlap p ρ x z else 0 := by
  rw [statistic_eq_overlaps]
  let f (x z : L) := if x<z then overlap p ρ x z else 0
  have split (x z : L) : (if x≠z then overlap p ρ x z else 0) = f x z + f z x := by
    rcases lt_trichotomy x z with h|h|h
    · simp [f,h,h.ne,not_lt_of_ge h.le]
    · simp [f,h]
    · simp [f,h,h.ne',not_lt_of_ge h.le,overlap,Matrix.trace_mul_comm (weighted p ρ x) (weighted p ρ z)]
  simp only [distinctPairs,Finset.sum_filter,Fintype.sum_prod_type,split,Finset.sum_add_distrib]
  change ((∑ x, ∑ z, f x z) + (∑ x, ∑ z, f z x))/2 = ∑ x, ∑ z, f x z
  rw [Finset.sum_comm (f := fun x z => f z x)]
  ring

end SubentropyCertificates.Quadratic
