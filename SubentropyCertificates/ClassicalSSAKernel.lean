module

public import SubentropyCertificates.SliceProducts
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Strong subadditivity of the reciprocal determinant products for finite
classical tables. Indices are ordered A, B, C and B is the middle label. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SubentropyCertificates.ClassicalSSA
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

def marginalAB (p : A × B × C → ℝ) (u : A × B) := ∑ k, p (u.1,u.2,k)
def marginalBC (p : A × B × C → ℝ) (u : B × C) := ∑ i, p (i,u.1,u.2)
def marginalB (p : A × B × C → ℝ) (j : B) := ∑ i, ∑ k, p (i,j,k)

/-- Positive joint mass occurs only when the first (respectively last)
label is the selected function of the middle label. -/
def determined (p : A × B × C → ℝ) : Prop :=
  (∃ f : B → A, ∀ i j k, 0 < p (i,j,k) → i = f j) ∨
  (∃ g : B → C, ∀ i j k, 0 < p (i,j,k) → k = g j)

private theorem kernel_factors (t : ℝ) (p : A × B × C → ℝ) :
    let q := fun j i k => p (i,j,k)
    kernel t (marginalAB p) = (∏ j, rows t Finset.univ (q j)) ∧
    kernel t (marginalBC p) = (∏ j, cols t Finset.univ (q j)) ∧
    kernel t p = (∏ j, cells t Finset.univ (q j)) ∧
    kernel t (marginalB p) = ∏ j, factor t (mass Finset.univ (q j)) := by
  simp only [kernel, rows, cols, cells, marginalAB, marginalBC, marginalB, mass, rowMass,
    colMass, Fintype.prod_prod_type]
  exact ⟨Finset.prod_comm, trivial, Finset.prod_comm, trivial⟩

/-- The pointwise part of thm:classical_ssa. No normalization is needed. -/
theorem classical_ssa_kernel (p : A × B × C → ℝ) (hp : ∀ u, 0 ≤ p u) {t : ℝ} (ht : 0 ≤ t) :
    kernel t (marginalAB p) + kernel t (marginalBC p) ≤ kernel t p + kernel t (marginalB p) := by
  rcases ht.eq_or_lt with h | h
  · subst t; simp [kernel, factor]
  obtain ⟨hx,hy,ha,hd⟩ := kernel_factors t p
  rw [hx,hy,ha,hd]
  exact (slice_product_comparison h _ (fun j i k => hp (i,j,k))).1

omit [Fintype B] in
private theorem select_label [Nonempty A] (q : B → A → C → ℝ) (hq : ∀ j i k, 0 ≤ q j i k) :
    (∀ j, ¬ varies Finset.univ (rowMass (q j))) ↔
      ∃ f : B → A, ∀ j i k, 0 < q j i k → i = f j := by
  classical
  have hpos (j : B) (i : A) : 0 < rowMass (q j) i ↔ ∃ k, 0 < q j i k := by
    constructor
    · intro h
      by_contra! hn
      have hz := Finset.sum_eq_zero (s := Finset.univ) (fun k _ => le_antisymm (hn k) (hq j i k))
      exact h.ne' hz
    · rintro ⟨k,h⟩
      exact h.trans_le (Finset.single_le_sum (fun k _ => hq j i k) (Finset.mem_univ k))
  constructor
  · intro H
    have chooseLabel (j : B) : ∃ i : A, ∀ l k, 0 < q j l k → l=i := by
      by_cases has : ∃ i, 0 < rowMass (q j) i
      · obtain ⟨i,hi⟩ := has
        refine ⟨i,fun l k hk => ?_⟩
        by_contra hn
        exact H j ⟨i,Finset.mem_univ _,l,Finset.mem_univ _,hn,hi,(hpos j l).mpr ⟨k,hk⟩⟩
      · exact ⟨Classical.arbitrary A,fun l k h => False.elim (has ⟨l,(hpos j l).mpr ⟨k,h⟩⟩)⟩
    choose f hf using chooseLabel
    exact ⟨f,hf⟩
  · rintro ⟨f,hf⟩ j ⟨i,_,l,_,hli,hi,hl⟩
    obtain ⟨k,hk⟩ := (hpos j i).mp hi
    obtain ⟨m,hm⟩ := (hpos j l).mp hl
    exact hli ((hf j l m hm).trans (hf j i k hk).symm)

/-- At every positive t, equality is precisely global determinism on
one side. The nonempty outer alphabets allow total functions on zero slices. -/
theorem classical_ssa_kernel_eq_iff [Nonempty A] [Nonempty C]
    (p : A × B × C → ℝ) (hp : ∀ u, 0 ≤ p u) {t : ℝ} (ht : 0 < t) :
    kernel t (marginalAB p) + kernel t (marginalBC p) = kernel t p + kernel t (marginalB p) ↔
      determined p := by
  obtain ⟨hx,hy,ha,hd⟩ := kernel_factors t p
  rw [hx,hy,ha,hd, (slice_product_comparison ht _ (fun j i k => hp (i,j,k))).2]
  unfold determined
  apply or_congr
  · rw [select_label _ (fun j i k => hp (i,j,k))]
    exact exists_congr fun _ => forall_comm
  · change (∀ j, ¬ varies Finset.univ (rowMass (fun k i => p (i,j,k)))) ↔ _
    rw [select_label _ (fun j k i => hp (i,j,k))]
    apply exists_congr
    intro g
    constructor
    · exact fun h i j k => h j k i
    · exact fun h j k i => h i j k

end SubentropyCertificates.ClassicalSSA
