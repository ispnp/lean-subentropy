module

public import SubentropyCertificates.BinarySplitting
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite nonnegative tables, including zero mass. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SubentropyCertificates.ClassicalSSA
variable {I J : Type*} [Fintype J]

def kernel {D : Type*} [Fintype D] (t : ℝ) (w : D → ℝ) := ∏ i, factor t (w i)
def rowMass (p : I → J → ℝ) (i : I) := ∑ j, p i j
def colMass (s : Finset I) (p : I → J → ℝ) (j : J) := ∑ i ∈ s, p i j
def mass (s : Finset I) (p : I → J → ℝ) := ∑ i ∈ s, rowMass p i
def rows (t : ℝ) (s : Finset I) (p : I → J → ℝ) := ∏ i ∈ s, factor t (rowMass p i)
def cols (t : ℝ) (s : Finset I) (p : I → J → ℝ) := kernel t (colMass s p)
def cells (t : ℝ) (s : Finset I) (p : I → J → ℝ) := ∏ i ∈ s, kernel t (p i)

theorem sum_colMass (s : Finset I) (p : I → J → ℝ) : (∑ j, colMass s p j) = mass s p :=
  Finset.sum_comm

theorem row_nonneg {p : I → J → ℝ} (hp : ∀ i j, 0 ≤ p i j) (i : I) : 0 ≤ rowMass p i :=
  Finset.sum_nonneg fun j _ => hp i j

omit [Fintype J] in
theorem col_nonneg {p : I → J → ℝ} (hp : ∀ i j, 0 ≤ p i j) (s : Finset I) (j : J) :
    0 ≤ colMass s p j := Finset.sum_nonneg fun i _ => hp i j

theorem kernel_pos {D : Type*} [Fintype D] {t : ℝ} (ht : 0 ≤ t) {w : D → ℝ}
    (hw : ∀ i, 0 ≤ w i) : 0 < kernel t w := Finset.prod_pos fun i _ => factor_pos ht (hw i)

private theorem collapse_rows {u v a x y d : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hxd : x ≤ d) (h : x+y ≤ a+d) :
    u*y - u*a ≤ v*d - v*x := by
  linarith only [mul_le_mul_of_nonneg_left h hu,
    mul_le_mul_of_nonneg_right huv (sub_nonneg.mpr hxd)]

/-- Collapsing the old rows to one can only decrease the deficit.
Here u and v are the cell and row products of the rows left untouched. -/
private theorem collapse_old {t : ℝ} (ht : 0 ≤ t) (s : Finset I) (p : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (i : I)
    (ih : rows t s p + cols t s p ≤ cells t s p + factor t (mass s p)) :
    kernel t (p i)*cols t s p - kernel t (p i)*cells t s p ≤
      factor t (rowMass p i)*factor t (mass s p) - factor t (rowMass p i)*rows t s p :=
  collapse_rows (kernel_pos ht (hp i)).le (refinement ht Finset.univ _ (hp i))
    (refinement ht s _ (row_nonneg hp)) ih

theorem table_subadditivity {t : ℝ} (ht : 0 ≤ t) (s : Finset I) (p : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) :
    rows t s p + cols t s p ≤ cells t s p + factor t (mass s p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rows, cols, cells, mass, colMass, kernel]
  | @insert i s hi ih =>
    have hc := collapse_old ht s p hp i ih
    have hs := binary_splitting ht Finset.univ (p i) (colMass s p) (hp i) (col_nonneg hp s)
    rw [sum_colMass] at hs
    change kernel t (fun j => p i j + colMass s p j) - kernel t (p i)*cols t s p ≤
      factor t (rowMass p i + mass s p) - factor t (rowMass p i)*factor t (mass s p) at hs
    change (∏ k ∈ insert i s, factor t (rowMass p k)) + kernel t (colMass (insert i s) p) ≤
      (∏ k ∈ insert i s, kernel t (p k)) + factor t (∑ k ∈ insert i s, rowMass p k)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi,
      show colMass (insert i s) p = fun j => p i j + colMass s p j by funext j; simp [colMass, hi]]
    change factor t (rowMass p i)*rows t s p + _ ≤ kernel t (p i)*cells t s p + factor t (rowMass p i + mass s p)
    linarith only [hs, hc]

/-- Merging all rows in s to one, with the rows in r left separate:
the cell-product gain is at most the row-product gain. The column sums
and the total mass are identical on the two sides of the merge. -/
theorem row_merging {t : ℝ} (ht : 0 ≤ t) (s r : Finset I) (p : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) :
    cells t r p * cols t s p - cells t r p * cells t s p ≤
      rows t r p * factor t (mass s p) - rows t r p * rows t s p := by
  apply collapse_rows (Finset.prod_nonneg fun i _ => (kernel_pos ht (hp i)).le) _
    (refinement ht s _ (row_nonneg hp)) (table_subadditivity ht s p hp)
  exact Finset.prod_le_prod₀ (fun i _ => (kernel_pos ht (hp i)).le)
    (fun i _ => refinement ht Finset.univ _ (hp i))

omit [Fintype J] in
/-- The same merge for a group of columns, written in the transposed table. -/
theorem column_merging [Fintype I] {t : ℝ} (ht : 0 ≤ t) (s r : Finset J) (p : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) :
    let q := fun j i => p i j
    cells t r q * cols t s q - cells t r q * cells t s q ≤
      rows t r q * factor t (mass s q) - rows t r q * rows t s q :=
  row_merging ht s r _ (fun j i => hp i j)

theorem table_subadditivity_strict {t : ℝ} (ht : 0 < t) (s : Finset I) (p : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (hrow : varies s (rowMass p))
    (hcol : varies Finset.univ (colMass s p)) :
    rows t s p + cols t s p < cells t s p + factor t (mass s p) := by
  classical
  rcases hrow with ⟨i,hi,l,hl,hli,hai,hal⟩
  rcases hcol with ⟨j,hj,k,hk,hkj,hbj,hbk⟩
  let r := s.erase i
  have hir : i ∉ r := Finset.notMem_erase i s
  have he : s = insert i r := (Finset.insert_erase hi).symm
  have hr : 0 < mass r p := hal.trans_le (Finset.single_le_sum
    (fun l (_ : l ∈ r) => row_nonneg hp l) (Finset.mem_erase.mpr ⟨hli,hl⟩))
  have hcolsum : colMass s p = fun j => p i j + colMass r p j := by
    conv_lhs => rw [he]
    funext j
    simp [colMass, hir]
  rw [hcolsum] at hbj hbk
  have hc := collapse_old ht.le r p hp i (table_subadditivity ht.le r p hp)
  have hs := binary_splitting_strict ht Finset.univ (p i) (colMass r p) (hp i) (col_nonneg hp r)
    hai ((sum_colMass r p).symm ▸ hr) hj hk hkj hbj hbk
  rw [sum_colMass] at hs
  change kernel t (fun j => p i j + colMass r p j) - kernel t (p i)*cols t r p <
    factor t (rowMass p i + mass r p) - factor t (rowMass p i)*factor t (mass r p) at hs
  change (∏ k ∈ s, factor t (rowMass p k)) + kernel t (colMass s p) <
    (∏ k ∈ s, kernel t (p k)) + factor t (∑ k ∈ s, rowMass p k)
  rw [hcolsum]
  conv_lhs => lhs; rw [he, Finset.prod_insert hir]
  conv_rhs => lhs; rw [he, Finset.prod_insert hir]
  conv_rhs => rhs; arg 2; rw [he, Finset.sum_insert hir]
  change factor t (rowMass p i)*rows t r p + _ < kernel t (p i)*cells t r p + factor t (rowMass p i + mass r p)
  linarith only [hc, hs]

end SubentropyCertificates.ClassicalSSA
