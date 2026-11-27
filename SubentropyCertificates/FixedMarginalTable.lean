module

public import SubentropyCertificates.BinarySharpPriors
public import SubentropyCertificates.DeterminantRepresentation
import all SubentropyCertificates.BinarySharpPriors
import all SubentropyCertificates.CounterexampleDeterminants

/-! Moving mass from one label to another along a single eigenvector of a fixed marginal. -/
@[expose] public section
noncomputable section
open Matrix Set MeasureTheory
open scoped BigOperators
namespace SubentropyCertificates.ConditionalContinuity
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Continuity (totalVariation)
open SubentropyCertificates.Representations
open SubentropyCertificates.QuantumCounterexample (det_diag)

variable {X D : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]

/-- Move mass e from label a to b in spectral coordinate i, keeping every column sum fixed. -/
def splitTable (a b : X) (w : D → ℝ) (i : D) (e : ℝ) (x : X) (j : D) : ℝ :=
  if x = a then w j - (if j = i then e else 0)
  else if x = b ∧ j = i then e else 0

/-- The flattened joint spectrum, in the order of the CQ block direct sum. -/
def splitPrior (a b : X) (w : D → ℝ) (i : D) (e : ℝ) (z : D × X) : ℝ :=
  splitTable a b w i e z.2 z.1

omit [Fintype D] in
theorem splitTable_column (a b : X) (hab : a ≠ b) (w : D → ℝ) (i : D) (e : ℝ) (j : D) :
    ∑ x, splitTable a b w i e x j = w j := by
  rw [sum_on_pair a b hab _ (fun x ha hb ↦ by simp [splitTable, ha, hb])]
  by_cases h : j = i <;> simp [splitTable, hab.symm, h]

theorem splitPrior_probability (a b : X) (hab : a ≠ b) {w : D → ℝ}
    (hw : w ∈ probabilitySimplex D) (i : D) {e : ℝ} (he : e ∈ Icc 0 (w i)) :
    splitPrior a b w i e ∈ probabilitySimplex (D × X) := by
  constructor
  · rintro ⟨j,x⟩
    by_cases hj : j = i
    · subst j
      by_cases ha : x = a <;> by_cases hb : x = b <;>
        simp [splitPrior, splitTable, ha, hb, hab.symm, he.1, he.2]
    · by_cases ha : x = a <;> simp [splitPrior, splitTable, ha, hj, hw.1]
  · simpa only [splitPrior, Fintype.sum_prod_type, splitTable_column a b hab] using hw.2

theorem splitPrior_distance (a b : X) (hab : a ≠ b) (w : D → ℝ) (i : D) {e : ℝ} (he : 0 ≤ e) :
    totalVariation (splitPrior a b w i 0) (splitPrior a b w i e) = e := by
  have row (j : D) : (∑ x, |splitTable a b w i 0 x j - splitTable a b w i e x j|) =
      if j = i then e + e else 0 := by
    rw [sum_on_pair a b hab _ (fun x ha hb ↦ by simp [splitTable, ha, hb])]
    by_cases h : j = i <;> simp [splitTable, hab.symm, h, abs_of_nonneg he]
  simp [totalVariation, splitPrior, Fintype.sum_prod_type, row]

private theorem splitProduct (a b : X) (hab : a ≠ b) (w : D → ℝ) (i : D) (e t : ℝ) :
    (∏ z, (1+t*splitPrior a b w i e z)⁻¹) =
      (∏ j ∈ Finset.univ.erase i, (1+t*w j)⁻¹) * ((1+t*(w i-e))⁻¹ * (1+t*e)⁻¹) := by
  let f (j : D) (x : X) := (1+t*splitTable a b w i e x j)⁻¹
  have row (j : D) : (∏ x, f j x) = f j a * f j b := by
    calc
      _ = ∏ x ∈ ({a,b} : Finset X), f j x := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro x _ hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        simp [f, splitTable, hx.1, hx.2]
      _ = _ := by simp [hab]
  change (∏ z : D × X, f z.1 z.2) = _
  rw [Fintype.prod_prod_type, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j hj
    rw [row]
    simp [f, splitTable, (Finset.mem_erase.mp hj).1, hab.symm]
  · rw [row]
    simp [f, splitTable, hab.symm]

private theorem diagonal_integrand (p : D → ℝ) (t : ℝ) :
    determinantIntegrand (diagonal fun j ↦ (p j : ℂ)) t =
    (1/(1+t) - ∏ j, (1+t*p j)⁻¹) / t^2 := by
  simp only [determinantIntegrand, det_diag, Complex.ofReal_re, one_div, Finset.prod_inv_distrib]

/-- Exact subentropy increment after splitting an eigenvalue; no full-rank assumption is needed. -/
theorem splitPrior_increment (a b : X) (hab : a ≠ b) {w : D → ℝ}
    (hw : w ∈ probabilitySimplex D) (i : D) {e : ℝ} (he : e ∈ Icc 0 (w i)) :
    classicalSubentropy (splitPrior a b w i e) - classicalSubentropy (splitPrior a b w i 0) =
      e * ∫ t in Ioi (0 : ℝ), (w i-e) / ((1+t*(w i-e))*(1+t*e)) * ∏ j, (1+t*w j)⁻¹ := by
  have h0 := diagonal_density (splitPrior_probability a b hab hw i (e := 0) ⟨le_rfl, hw.1 i⟩)
  have h1 := diagonal_density (splitPrior_probability a b hab hw i he)
  obtain ⟨hi0, hq0⟩ := reciprocal_determinant_integral _ h0.1 h0.2
  obtain ⟨hi1, hq1⟩ := reciprocal_determinant_integral _ h1.1 h1.2
  unfold classicalSubentropy
  rw [hq1, hq0, ← integral_sub hi1 hi0, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [diagonal_integrand, splitProduct a b hab, sub_zero, mul_zero, add_zero, inv_one,
    mul_one]
  rw [← Finset.prod_erase_mul _ (fun j ↦ (1+t*w j)⁻¹) (Finset.mem_univ i)]
  have h₁ : 0 < 1+t*(w i-e) := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr he.2)]
  have h₂ : 0 < 1+t*e := by nlinarith [mul_nonneg ht.le he.1]
  have h₃ : 0 < 1+t*w i := by nlinarith [mul_nonneg ht.le (hw.1 i)]
  have h₄ : 0 < 1+t := by linarith [show 0 < t from ht]
  generalize (∏ j ∈ Finset.univ.erase i, (1+t*w j)⁻¹) = k
  field_simp [h₁.ne', h₂.ne', h₃.ne', h₄.ne', ht.ne']
  ring

end SubentropyCertificates.ConditionalContinuity
