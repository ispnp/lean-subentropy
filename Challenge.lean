module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Classical strong subadditivity of subentropy

Theorem 22 of Pratik Patil, *Quantum Subentropy: Subadditivity and Sharp Bounds on
Discrimination Error* (arXiv:2611.30220). The reciprocal product is defined for any finite
table. The subentropy integral below uses the variable `s = 1/t` in the paper's Lemma 3.
-/

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

variable [Fintype A] [Fintype B] [Fintype C]

/-- Subentropy is strongly subadditive for finite classical distributions, with equality
exactly when one outer label is determined by the middle label. -/
theorem classical_strong_subadditivity (p : A × B × C → ℝ)
    (hp : ∀ u, 0 ≤ p u) (hmass : ∑ u, p u = 1) :
    subentropy (marginalB p) + subentropy p ≤
      subentropy (marginalAB p) + subentropy (marginalBC p) ∧
    (subentropy (marginalB p) + subentropy p =
      subentropy (marginalAB p) + subentropy (marginalBC p) ↔ determined p) := by
  sorry

/-- The pointwise comparison holds for every nonnegative table of any total mass. -/
theorem classical_ssa_kernel (p : A × B × C → ℝ) (hp : ∀ u, 0 ≤ p u) {t : ℝ} (ht : 0 ≤ t) :
    kernel t (marginalAB p) + kernel t (marginalBC p) ≤ kernel t p + kernel t (marginalB p) := by
  sorry

/-- At each positive parameter the pointwise comparison has the same equality condition.
Nonempty outer alphabets allow the functions to be defined on zero-mass slices. -/
theorem classical_ssa_kernel_eq_iff [Nonempty A] [Nonempty C]
    (p : A × B × C → ℝ) (hp : ∀ u, 0 ≤ p u) {t : ℝ} (ht : 0 < t) :
    (kernel t (marginalAB p) + kernel t (marginalBC p) =
      kernel t p + kernel t (marginalB p)) ↔ determined p := by
  sorry

end SubentropyClassicalSSA
