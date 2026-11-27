module

public import SubentropyCertificates.ClassicalCurve
import Mathlib.Tactic.Linarith

/-! A maximal coupling of two probability vectors on a common finite alphabet. -/
@[expose] public section
noncomputable section
open scoped BigOperators

namespace SubentropyCertificates.Continuity
open SubentropyCertificates.ClassicalCurve

variable {X : Type*} [Fintype X]

def totalVariation (p q : X → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

/-- The diagonal of a maximal coupling is the common mass at each coordinate. -/
theorem exists_maximal_coupling (p q : X → ℝ) (hp : p ∈ probabilitySimplex X)
    (hq : q ∈ probabilitySimplex X) :
    ∃ J : X → X → ℝ, (∀ i j, 0 ≤ J i j) ∧ (∀ i, ∑ j, J i j = p i) ∧
      (∀ j, ∑ i, J i j = q j) ∧ (∀ i, J i i = min (p i) (q i)) ∧
      1 - ∑ i, J i i = totalVariation p q := by
  classical
  let s := fun i ↦ min (p i) (q i)
  let r := fun i ↦ p i - s i
  let c := fun i ↦ q i - s i
  let t := 1 - ∑ i, s i
  have hr i : 0 ≤ r i := sub_nonneg.mpr (min_le_left _ _)
  have hc i : 0 ≤ c i := sub_nonneg.mpr (min_le_right _ _)
  have hrs : ∑ i, r i = t := by simp [r, t, Finset.sum_sub_distrib, hp.2]
  have hcs : ∑ i, c i = t := by simp [c, t, Finset.sum_sub_distrib, hq.2]
  have ht : 0 ≤ t := hrs ▸ Finset.sum_nonneg (fun i _ ↦ hr i)
  have hab i : r i + c i = |p i - q i| := by
    rcases le_total (p i) (q i) with h | h
    · simp [r, c, s, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    · simp [r, c, s, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  have htv : t = totalVariation p q := by
    simp only [totalVariation, ← hab, Finset.sum_add_distrib, hrs, hcs]
    ring
  have cancel (f : X → ℝ) (hf : ∀ i, 0 ≤ f i) (hs : ∑ i, f i = t) (i : X) :
      f i * t / t = f i := by
    by_cases hz : t = 0
    · have hle := Finset.single_le_sum (s := Finset.univ) (fun j _ ↦ hf j) (Finset.mem_univ i)
      rw [hs, hz] at hle
      simp [le_antisymm hle (hf i)]
    · field_simp
  let J := fun i j ↦ (if i = j then s i else 0) + r i * c j / t
  have diag i : J i i = s i := by
    rcases le_total (p i) (q i) with h | h
    · simp [J, r, s, min_eq_left h]
    · simp [J, c, s, min_eq_right h]
  refine ⟨J, ?_, ?_, ?_, diag, ?_⟩
  · intro i j
    exact add_nonneg (by split <;> simp [s, hp.1, hq.1])
      (div_nonneg (mul_nonneg (hr i) (hc j)) ht)
  · intro i
    simp only [J, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hcs]
    simp [cancel r hr hrs, r]
  · intro j
    simp only [J, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, hrs]
    rw [mul_comm t (c j), cancel c hc hcs]
    simp [c]
  · simpa only [diag] using htv

end SubentropyCertificates.Continuity
