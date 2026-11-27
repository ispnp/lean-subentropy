module
public import D5.S3.Quantum.Subentropy.EntropyJensenGap
import all D5.S3.Quantum.Subentropy.EntropyJensenGap

/-! Equality in the finite entropy gap. Each row is a nonnegative sign orbit.
The cross-multiplied conclusion also applies to rows of zero mass. -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SubentropyCertificates.PinchingEquality
open D5.S3.Quantum.Subentropy.EntropyJensenGap
variable {I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

private theorem normalized_gap (a : S → ℝ) (ha : ∀ s, 0 ≤ a s) :
    entropyJensenGap a = -finiteAverage a * finiteAverage (fun s =>
      Real.negMulLog (a s / finiteAverage a)) := by
  by_cases hz : finiteAverage a = 0
  · have h := (average_zero_iff a ha).mp hz
    simp [h, finiteAverage, entropyJensenGap]
  · exact gap_normalized a hz

theorem orbit_ratios_of_gap_equality (a : I → S → ℝ) (ha : ∀ i s, 0 ≤ a i s)
    (he : entropyJensenGap (fun s => ∑ i, a i s) = ∑ i, entropyJensenGap (a i)) :
    ∀ i j s, a i s * finiteAverage (a j) = a j s * finiteAverage (a i) := by
  let b i := finiteAverage (a i)
  let t := ∑ i, b i
  let A s := ∑ i, a i s
  have hb i : 0 ≤ b i := average_nonneg _ (ha i)
  have hA s : 0 ≤ A s := Finset.sum_nonneg (fun i _ => ha i s)
  have ht : finiteAverage A = t := by
    simp only [A, b, t, finiteAverage, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hzero i (hi : b i = 0) (s : S) : a i s = 0 :=
    congrFun ((average_zero_iff _ (ha i)).mp hi) s
  by_cases htz : t = 0
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).mp htz
    intro i j s
    change _ * b j = _ * b i
    rw [hall i (Finset.mem_univ _), hall j (Finset.mem_univ _), mul_zero, mul_zero]
  have htpos : 0 < t := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hb i)) (Ne.symm htz)
  let w i := b i / t
  let r i s := a i s / b i
  have hw i : 0 ≤ w i := div_nonneg (hb i) htpos.le
  have hws : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div]
    exact div_self htz
  have hmean s : ∑ i, w i • r i s = A s / t := by
    change (∑ i, b i / t * (a i s / b i)) = A s / t
    rw [show A s / t = ∑ i, a i s / t by rw [← Finset.sum_div]]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : b i = 0
    · simp [hi, hzero i hi]
    · field_simp
  let L s := ∑ i, w i * Real.negMulLog (r i s)
  let U s := Real.negMulLog (A s / t)
  have hle s : L s ≤ U s := by
    have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := w) (p := fun i => r i s) (fun i _ => hw i) hws
      (fun i _ => div_nonneg (ha i s) (hb i))
    rwa [hmean] at h
  have hsum : finiteAverage L = ∑ i, w i * finiteAverage (fun s => Real.negMulLog (r i s)) := by
    simp only [L, finiteAverage, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_left_comm]
  have heq : finiteAverage L = finiteAverage U := by
    change entropyJensenGap A = _ at he
    rw [normalized_gap A hA, ht] at he
    simp_rw [fun i => normalized_gap (a i) (ha i)] at he
    change -t * finiteAverage U = ∑ i, -b i * finiteAverage (fun s => Real.negMulLog (r i s)) at he
    rw [hsum]
    apply mul_left_cancel₀ (neg_ne_zero.mpr htz)
    rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [w]
    field_simp
  have hcount : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have heach := (Finset.sum_eq_sum_iff_of_le (fun s _ => hle s)).mp
    (mul_left_cancel₀ (inv_ne_zero hcount) heq)
  have hratio i s (hi : b i ≠ 0) : r i s = A s / t := by
    have h := Real.strictConcaveOn_negMulLog.map_sum_eq_iff' (t := Finset.univ)
      (w := w) (p := fun i => r i s) (fun i _ => hw i) hws
      (fun i _ => div_nonneg (ha i s) (hb i))
    rw [hmean] at h
    exact h.mp (heach s (Finset.mem_univ _)).symm i (Finset.mem_univ _) (div_ne_zero hi htz)
  intro i j s
  change a i s * b j = a j s * b i
  by_cases hi : b i = 0
  · simp [hi, hzero i hi]
  by_cases hj : b j = 0
  · simp [hj, hzero j hj]
  exact (div_eq_div_iff hi hj).mp ((hratio i s hi).trans (hratio j s hj).symm)

end SubentropyCertificates.PinchingEquality
