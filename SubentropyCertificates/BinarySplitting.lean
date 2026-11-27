module

public import SubentropyCertificates.FourCell
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Binary splitting of reciprocal products and its strict form. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SubentropyCertificates.ClassicalSSA
open SubentropyCertificates.FourCell
variable {I : Type*}

def factor (t x : ℝ) : ℝ := (1+x*t)⁻¹

@[simp]
theorem factor_zero (t : ℝ) : factor t 0 = 1 := by simp [factor]

theorem factor_pos {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) : 0 < factor t x := by
  unfold factor; positivity

private theorem factor_pair {t x y : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    factor t x * factor t y ≤ factor t (x+y) := by
  unfold factor
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  nlinarith only [mul_nonneg (mul_nonneg hx hy) (sq_nonneg t)]

theorem refinement {t : ℝ} (ht : 0 ≤ t) (s : Finset I) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∏ i ∈ s, factor t (x i) ≤ factor t (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (mul_le_mul_of_nonneg_left ih (factor_pos ht (hx i)).le).trans
      (factor_pair ht (hx i) (Finset.sum_nonneg fun j _ => hx j))

/-- Before using the four-cell inequality, collapse the old indices to a
single pair of masses X,Y and keep the new pair x,y separate. -/
private theorem collapse_previous {A B X Y x y t : ℝ} (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ih : A-B ≤ factor t (X+Y) - factor t X * factor t Y)
    (hB : B ≤ factor t X * factor t Y) :
    factor t (x+y)*A - (factor t x*factor t y)*B ≤
      factor t (x+y)*factor t (X+Y) - (factor t x*factor t y)*(factor t X*factor t Y) := by
  linarith only [mul_le_mul_of_nonneg_left ih (factor_pos ht (add_nonneg hx hy)).le,
    mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr (factor_pair ht hx hy))]

private theorem four_cell_factors {x y X Y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (ht : 0 ≤ t) :
    factor t (x+y)*factor t (X+Y) - (factor t x*factor t y)*(factor t X*factor t Y) ≤
      factor t ((x+X)+(y+Y)) - factor t (x+X)*factor t (y+Y) := by
  have h := four_cell x y X Y t hx hy hX hY ht
  simp only [rowKernel, columnKernel, cellKernel, totalKernel, one_div, mul_inv] at h
  unfold factor
  rw [show (x+X)+(y+Y) = x+y+X+Y by ring, mul_comm (x+y+X+Y) t]
  linarith only [h]

/-- Binary splitting (lem:split), with the parameter t absorbed into
each factor. Taking t=1 gives the manuscript's displayed formula. -/
theorem binary_splitting {t : ℝ} (ht : 0 ≤ t) (s : Finset I) (x y : I → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    (∏ i ∈ s, factor t (x i+y i)) - (∏ i ∈ s, factor t (x i))*(∏ i ∈ s, factor t (y i)) ≤
      factor t ((∑ i ∈ s, x i)+(∑ i ∈ s, y i)) -
        factor t (∑ i ∈ s, x i)*factor t (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [mul_mul_mul_comm (factor t (x i)) _ (factor t (y i))]
    have hB := mul_le_mul (refinement ht s x hx) (refinement ht s y hy)
      (Finset.prod_nonneg fun j _ => (factor_pos ht (hy j)).le)
      (factor_pos ht (Finset.sum_nonneg fun j _ => hx j)).le
    exact (collapse_previous ht (hx i) (hy i) ih hB).trans
      (four_cell_factors (hx i) (hy i) (Finset.sum_nonneg fun j _ => hx j)
        (Finset.sum_nonneg fun j _ => hy j) ht)

/-- Strict splitting when both column totals are positive and two
different rows have positive mass. -/
theorem binary_splitting_strict {t : ℝ} (ht : 0 < t) (s : Finset I) (x y : I → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hX : 0 < ∑ i ∈ s, x i) (hY : 0 < ∑ i ∈ s, y i)
    {i j : I} (hi : i ∈ s) (hj : j ∈ s) (hne : j ≠ i)
    (hpi : 0 < x i+y i) (hpj : 0 < x j+y j) :
    (∏ k ∈ s, factor t (x k+y k)) - (∏ k ∈ s, factor t (x k))*(∏ k ∈ s, factor t (y k)) <
      factor t ((∑ k ∈ s, x k)+(∑ k ∈ s, y k)) -
        factor t (∑ k ∈ s, x k)*factor t (∑ k ∈ s, y k) := by
  classical
  let r := s.erase i
  have hir : i ∉ r := Finset.notMem_erase i s
  have he : s = insert i r := (Finset.insert_erase hi).symm
  let X := ∑ k ∈ r, x k
  let Y := ∑ k ∈ r, y k
  have hnX : 0 ≤ X := Finset.sum_nonneg fun k _ => hx k
  have hnY : 0 ≤ Y := Finset.sum_nonneg fun k _ => hy k
  have hjr : j ∈ r := Finset.mem_erase.mpr ⟨hne,hj⟩
  have hXY : 0 < X+Y := by
    linarith only [hpj, Finset.single_le_sum (fun k (_ : k ∈ r) => hx k) hjr,
      Finset.single_le_sum (fun k (_ : k ∈ r) => hy k) hjr]
  rw [he, Finset.sum_insert hir] at hX hY
  rw [he]
  simp only [Finset.prod_insert hir, Finset.sum_insert hir]
  rw [mul_mul_mul_comm (factor t (x i)) _ (factor t (y i))]
  have hB := mul_le_mul (refinement ht.le r x hx) (refinement ht.le r y hy)
    (Finset.prod_nonneg fun k _ => (factor_pos ht.le (hy k)).le) (factor_pos ht.le hnX).le
  apply lt_of_le_of_lt (collapse_previous ht.le (hx i) (hy i) (binary_splitting ht.le r x y hx hy) hB)
  have hf := (four_cell_strict_iff (x i) (y i) X Y t (hx i) (hy i) hnX hnY ht).mpr
    ⟨hpi,hXY,hX,hY⟩
  simp only [rowKernel, columnKernel, cellKernel, totalKernel, one_div, mul_inv] at hf
  change factor t (x i+y i)*factor t (X+Y) - _ < factor t ((x i+X)+(y i+Y)) - _
  unfold factor
  rw [show (x i+X)+(y i+Y) = x i+y i+X+Y by ring, mul_comm (x i+y i+X+Y) t]
  linarith only [hf]

/-- Two distinct positive entries in the indicated marginal. -/
def varies (s : Finset I) (x : I → ℝ) : Prop :=
  ∃ i ∈ s, ∃ j ∈ s, j ≠ i ∧ 0 < x i ∧ 0 < x j

theorem refinement_eq_iff {t : ℝ} (ht : 0 < t) (s : Finset I) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∏ i ∈ s, factor t (x i)) = factor t (∑ i ∈ s, x i) ↔ ¬ varies s x := by
  classical
  constructor
  · rintro he ⟨i, hi, j, hj, hji, hxi, hxj⟩
    let r := s.erase i
    have hir : i ∉ r := Finset.notMem_erase i s
    have heq : s = insert i r := (Finset.insert_erase hi).symm
    have hxr : 0 < ∑ k ∈ r, x k := hxj.trans_le (Finset.single_le_sum
      (fun k (_ : k ∈ r) => hx k) (Finset.mem_erase.mpr ⟨hji,hj⟩))
    rw [heq, Finset.prod_insert hir, Finset.sum_insert hir] at he
    apply ne_of_lt _ he
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (refinement ht.le r x hx) (factor_pos ht.le hxi.le).le)
    unfold factor
    rw [← mul_inv]
    apply inv_strictAnti₀ (by positivity)
    nlinarith only [mul_pos (mul_pos hxi hxr) (sq_pos_of_pos ht)]
  · intro h
    by_cases hex : ∃ i ∈ s, 0 < x i
    · obtain ⟨i,hi,hxi⟩ := hex
      have hz (j) (hj : j ∈ s) (hji : j ≠ i) : x j = 0 := by
        by_contra h0
        exact h ⟨i,hi,j,hj,hji,hxi,lt_of_le_of_ne (hx j) (Ne.symm h0)⟩
      rw [Finset.sum_eq_single_of_mem i hi hz, Finset.prod_eq_single_of_mem i hi]
      intro j hj hji
      simp [hz j hj hji]
    · have hz (j) (hj : j ∈ s) : x j = 0 := le_antisymm
        (le_of_not_gt (fun h => hex ⟨j,hj,h⟩)) (hx j)
      rw [Finset.sum_eq_zero hz, Finset.prod_eq_one (fun j hj => by simp [hz j hj]), factor_zero]

end SubentropyCertificates.ClassicalSSA
