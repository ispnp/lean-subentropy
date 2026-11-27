module

public import SubentropyCertificates.ClassicalStrongSubadditivity

/-! Theorem 22 for scalar probability tables, via subentropy of diagonal matrices. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace SubentropyClassicalSSA

/-- The reciprocal product associated with a finite vector of masses. -/
def kernel {D : Type*} [Fintype D] (t : ℝ) (w : D → ℝ) : ℝ :=
  ∏ i, (1 + w i * t)⁻¹

/-- Classical subentropy of a probability vector, in its determinant integral form. -/
def subentropy {D : Type*} [Fintype D] (w : D → ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (1 + s⁻¹)⁻¹ - kernel s⁻¹ w

variable {A B C : Type*}

def marginalAB [Fintype C] (p : A × B × C → ℝ) (u : A × B) : ℝ := ∑ k, p (u.1, u.2, k)
def marginalBC [Fintype A] (p : A × B × C → ℝ) (u : B × C) : ℝ := ∑ i, p (i, u.1, u.2)
def marginalB [Fintype A] [Fintype C] (p : A × B × C → ℝ) (j : B) : ℝ := ∑ i, ∑ k, p (i, j, k)

/-- On the support, one of the two outer labels is a function of the middle label. -/
def determined (p : A × B × C → ℝ) : Prop :=
  (∃ f : B → A, ∀ i j k, 0 < p (i, j, k) → i = f j) ∨
  (∃ g : B → C, ∀ i j k, 0 < p (i, j, k) → k = g j)

open SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.Basic in
private theorem subentropy_eq_classicalSubentropy {D : Type*} [Fintype D] [DecidableEq D]
    (w : D → ℝ) : subentropy w = classicalSubentropy w := by
  unfold subentropy classicalSubentropy matrixSubentropy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hs' : s ≠ 0 := ne_of_gt hs
  have ratio (x : ℝ) : s / (s + x) = (1 + x * s⁻¹)⁻¹ := by
    rw [show 1 + x * s⁻¹ = (s + x) / s by field_simp]
    simp
  rw [kernel_diagonal w s hs', add_comm (1 : ℝ) s, ratio 1, one_mul]
  simp only [kernel, ratio]

variable [Fintype A] [Fintype B] [Fintype C]

/-- Subentropy is strongly subadditive for finite classical distributions, with equality
exactly when one outer label is determined by the middle label. -/
theorem classical_strong_subadditivity (p : A × B × C → ℝ)
    (hp : ∀ u, 0 ≤ p u) (hmass : ∑ u, p u = 1) :
    subentropy (marginalB p) + subentropy p ≤
      subentropy (marginalAB p) + subentropy (marginalBC p) ∧
    (subentropy (marginalB p) + subentropy p =
      subentropy (marginalAB p) + subentropy (marginalBC p) ↔ determined p) := by
  classical
  simp only [subentropy_eq_classicalSubentropy]
  exact SubentropyCertificates.ClassicalSSA.classical_strong_subadditivity p ⟨hp, hmass⟩

/-- The pointwise comparison holds for every nonnegative table of any total mass. -/
theorem classical_ssa_kernel (p : A × B × C → ℝ) (hp : ∀ u, 0 ≤ p u) {t : ℝ} (ht : 0 ≤ t) :
    kernel t (marginalAB p) + kernel t (marginalBC p) ≤ kernel t p + kernel t (marginalB p) := by
  exact SubentropyCertificates.ClassicalSSA.classical_ssa_kernel p hp ht

/-- At each positive parameter the pointwise comparison has the same equality condition.
Nonempty outer alphabets allow the functions to be defined on zero-mass slices. -/
theorem classical_ssa_kernel_eq_iff [Nonempty A] [Nonempty C]
    (p : A × B × C → ℝ) (hp : ∀ u, 0 ≤ p u) {t : ℝ} (ht : 0 < t) :
    (kernel t (marginalAB p) + kernel t (marginalBC p) =
      kernel t p + kernel t (marginalB p)) ↔ determined p := by
  exact SubentropyCertificates.ClassicalSSA.classical_ssa_kernel_eq_iff p hp ht

end SubentropyClassicalSSA
