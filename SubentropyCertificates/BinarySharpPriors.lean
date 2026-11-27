module

public import SubentropyCertificates.MaximalCoupling
public import SubentropyCertificates.QuantumEquality

/-! Two-label priors, padded by zero on a prescribed finite alphabet. -/
@[expose] public section
noncomputable section
open Matrix Set MeasureTheory
open scoped BigOperators

namespace SubentropyCertificates.ConditionalContinuity
open D5.S3.Quantum.Subentropy.Basic
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Continuity (totalVariation)
open SubentropyCertificates.QuantumEquality (pointMass pointMass_probability pointMass_subentropy)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The prior with masses 1-e and e on the designated labels and zero elsewhere. -/
def binaryPrior (a b : X) (e : ℝ) (x : X) : ℝ :=
  if x = a then 1 - e else if x = b then e else 0

private theorem sum_on_pair (a b : X) (hab : a ≠ b) (f : X → ℝ)
    (h : ∀ x, x ≠ a → x ≠ b → f x = 0) : (∑ x, f x) = f a + f b := by
  calc
    _ = ∑ x ∈ ({a,b} : Finset X), f x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact h x hx.1 hx.2
    _ = _ := by simp [hab]

/-- The determinant factors outside the two occupied labels are one, so the subentropy
is the binary curve in every ambient dimension. -/
theorem binaryPrior_subentropy (a b : X) (hab : a ≠ b) (e : ℝ) :
    classicalSubentropy (binaryPrior a b e) = phi 0 e := by
  unfold phi classicalSubentropy matrixSubentropy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [kernel_diagonal _ t ht.ne', kernel_diagonal _ t ht.ne']
  congr 1
  let f (x : X) := t / (t + binaryPrior a b e x)
  change (∏ x, f x) = _
  calc
    _ = ∏ x ∈ ({a,b} : Finset X), f x := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp [f, binaryPrior, hx.1, hx.2, ht.ne']
    _ = _ := by simp [f, binaryPrior, hab, hab.symm, Fintype.prod_option, extremalVector]

/-- The two priors have total variation distance e and subentropy difference Φ₂(e). -/
theorem binaryPrior_pair (a b : X) (hab : a ≠ b) {e : ℝ} (he : e ∈ Icc 0 1) :
    pointMass a ∈ probabilitySimplex X ∧ binaryPrior a b e ∈ probabilitySimplex X ∧
      totalVariation (pointMass a) (binaryPrior a b e) = e ∧
      classicalSubentropy (pointMass a) = 0 ∧ classicalSubentropy (binaryPrior a b e) = phi 0 e := by
  refine ⟨pointMass_probability a, ⟨?_, ?_⟩, ?_, pointMass_subentropy a,
    binaryPrior_subentropy a b hab e⟩
  · intro x
    by_cases hxa : x = a
    · simp [binaryPrior, hxa, he.2]
    · simp only [binaryPrior, ite_eq_right hxa]
      split
      · exact he.1
      · exact le_rfl
  · rw [sum_on_pair a b hab _ (fun x hxa hxb ↦ by simp [binaryPrior, hxa, hxb])]
    simp [binaryPrior, hab.symm]
  · unfold totalVariation
    rw [sum_on_pair a b hab _ (fun x hxa hxb ↦ by simp [pointMass, binaryPrior, hxa, hxb])]
    simp [pointMass, binaryPrior, hab.symm, abs_of_nonneg he.1]

end SubentropyCertificates.ConditionalContinuity
