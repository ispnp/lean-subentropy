module

public import SubentropyCertificates.TableMerging
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Combining the reciprocal products over the middle label. The four
nonnegative terms in the product identity correspond to the four outcomes
of the auxiliary event construction in the manuscript. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SubentropyCertificates.ClassicalSSA

private structure Comparison (x y a d : ℝ) : Prop where
  pos : 0 < a
  ax : a ≤ x
  ay : a ≤ y
  xd : x ≤ d
  yd : y ≤ d
  le : x+y ≤ a+d
  rigid : x+y = a+d → x=d ∨ y=d

private theorem Comparison.eq_iff {x y a d : ℝ} (h : Comparison x y a d) :
    x+y = a+d ↔ x=d ∨ y=d := by
  refine ⟨h.rigid, ?_⟩
  rintro (hx | hy)
  · linarith only [hx, h.le, h.ay]
  · linarith only [hy, h.le, h.ax]

private theorem Comparison.mul {x y a d X Y A D : ℝ}
    (h : Comparison x y a d) (H : Comparison X Y A D) :
    Comparison (x*X) (y*Y) (a*A) (d*D) := by
  have hd := (h.pos.trans_le h.ax).trans_le h.xd
  have hD := (H.pos.trans_le H.ax).trans_le H.xd
  have h₁ := mul_nonneg h.pos.le (sub_nonneg.mpr H.le)
  have h₂ := mul_nonneg (sub_nonneg.mpr h.ax) (sub_nonneg.mpr H.xd)
  have h₃ := mul_nonneg (sub_nonneg.mpr h.ay) (sub_nonneg.mpr H.yd)
  have h₄ := mul_nonneg (sub_nonneg.mpr h.le) hD.le
  refine ⟨mul_pos h.pos H.pos,
    mul_le_mul h.ax H.ax H.pos.le (h.pos.trans_le h.ax).le,
    mul_le_mul h.ay H.ay H.pos.le (h.pos.trans_le h.ay).le,
    mul_le_mul h.xd H.xd (H.pos.trans_le H.ax).le hd.le,
    mul_le_mul h.yd H.yd (H.pos.trans_le H.ay).le hd.le, ?_, ?_⟩
  · linarith only [h₁,h₂,h₃,h₄]
  · intro he
    have z₁ : a*(A+D-(X+Y)) = 0 := by linarith only [he,h₁,h₂,h₃,h₄]
    have z₄ : (a+d-(x+y))*D = 0 := by linarith only [he,h₁,h₂,h₃,h₄]
    have z₂ : (x-a)*(D-X) = 0 := by linarith only [he,h₁,h₂,h₃,h₄]
    have z₃ : (y-a)*(D-Y) = 0 := by linarith only [he,h₁,h₂,h₃,h₄]
    have e := h.rigid (sub_eq_zero.mp ((mul_eq_zero.mp z₄).resolve_right hD.ne')).symm
    have E := H.rigid (sub_eq_zero.mp ((mul_eq_zero.mp z₁).resolve_left h.pos.ne')).symm
    rcases e with e | e <;> rcases E with E | E
    · exact Or.inl (by rw [e,E])
    · rcases mul_eq_zero.mp z₂ with u | v
      · right; rw [E]; have := sub_eq_zero.mp u; rw [show y=d by linarith only [e,this,h.ay,h.yd]]
      · left; rw [e, sub_eq_zero.mp v]
    · rcases mul_eq_zero.mp z₃ with u | v
      · left; rw [E]; have := sub_eq_zero.mp u; rw [show x=d by linarith only [e,this,h.ax,h.xd]]
      · right; rw [e, sub_eq_zero.mp v]
    · exact Or.inr (by rw [e,E])

private theorem comparison_prod {B : Type*} (s : Finset B) {x y a d : B → ℝ}
    (hs : ∀ j, Comparison (x j) (y j) (a j) (d j)) :
    Comparison (∏ j ∈ s, x j) (∏ j ∈ s, y j) (∏ j ∈ s, a j) (∏ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (show Comparison 1 1 1 1 from ⟨zero_lt_one, le_rfl, le_rfl,
      le_rfl, le_rfl, le_rfl, fun _ => Or.inl rfl⟩)
  | @insert j s hj ih =>
    simpa only [Finset.prod_insert hj] using (hs j).mul ih

private theorem prod_eq_all {B : Type*} [Fintype B] (x d : B → ℝ) (hx : ∀ j, 0 < x j)
    (hd : ∀ j, x j ≤ d j) : (∏ j, x j) = ∏ j, d j ↔ ∀ j, x j = d j := by
  constructor
  · intro he j
    by_contra hn
    exact (Finset.prod_lt_prod₀ (fun k _ => hx k) (fun k _ => hd k)
      ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hd j) hn⟩).ne he
  · intro he; rw [funext he]

variable {I B J : Type*} [Fintype I] [Fintype B] [Fintype J]

private theorem slice_comparison {t : ℝ} (ht : 0 < t) (p : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) :
    Comparison (rows t Finset.univ p) (cols t Finset.univ p)
      (cells t Finset.univ p) (factor t (mass Finset.univ p)) := by
  let s : Finset I := Finset.univ
  have hx := refinement ht.le s (rowMass p) (row_nonneg hp)
  have hy := refinement ht.le Finset.univ (colMass s p) (col_nonneg hp s)
  rw [sum_colMass] at hy
  refine ⟨Finset.prod_pos (fun i _ => kernel_pos ht.le (hp i)), ?_, ?_, hx, hy,
    table_subadditivity ht.le s p hp, ?_⟩
  · exact Finset.prod_le_prod₀ (fun i _ => (kernel_pos ht.le (hp i)).le)
      (fun i _ => refinement ht.le Finset.univ _ (hp i))
  · unfold cells cols kernel
    rw [Finset.prod_comm]
    exact Finset.prod_le_prod₀ (fun j _ => (Finset.prod_pos fun i _ => factor_pos ht.le (hp i j)).le)
      (fun j _ => refinement ht.le _ _ (fun i => hp i j))
  · intro he
    by_contra! hn
    have hrow : varies s (rowMass p) := by
      by_contra hn'
      exact hn.1 ((refinement_eq_iff ht s (rowMass p) (row_nonneg hp)).mpr hn')
    have hcol : varies Finset.univ (colMass s p) := by
      by_contra hn'
      have eq := (refinement_eq_iff ht Finset.univ _ (col_nonneg hp s)).mpr hn'
      rw [sum_colMass] at eq
      exact hn.2 eq
    exact (table_subadditivity_strict ht s p hp hrow hcol).ne he

/-- The two-variable comparison is an equality at positive t exactly when
there is at most one positive row or at most one positive column. -/
theorem table_subadditivity_eq_iff {t : ℝ} (ht : 0 < t) (p : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) :
    rows t Finset.univ p + cols t Finset.univ p = cells t Finset.univ p + factor t (mass Finset.univ p) ↔
      ¬ varies Finset.univ (rowMass p) ∨ ¬ varies Finset.univ (colMass Finset.univ p) := by
  rw [(slice_comparison ht p hp).eq_iff]
  apply or_congr (refinement_eq_iff ht _ _ (row_nonneg hp))
  have h := refinement_eq_iff ht Finset.univ _ (col_nonneg hp Finset.univ)
  rw [sum_colMass] at h
  exact h

/-- Equality for the slice products requires the same marginal to be
concentrated in every slice. Zero slices satisfy both alternatives. -/
theorem slice_product_comparison {t : ℝ} (ht : 0 < t) (p : B → I → J → ℝ)
    (hp : ∀ b i j, 0 ≤ p b i j) :
    let s : Finset I := Finset.univ
    let x := fun b => rows t s (p b)
    let y := fun b => cols t s (p b)
    let a := fun b => cells t s (p b)
    let d := fun b => factor t (mass s (p b))
    ((∏ b, x b) + (∏ b, y b) ≤ (∏ b, a b) + ∏ b, d b) ∧
    (((∏ b, x b) + (∏ b, y b) = (∏ b, a b) + ∏ b, d b) ↔
      (∀ b, ¬ varies s (rowMass (p b))) ∨ (∀ b, ¬ varies Finset.univ (colMass s (p b)))) := by
  dsimp only
  have h := fun b => slice_comparison ht (p b) (hp b)
  have H := comparison_prod Finset.univ h
  refine ⟨H.le, H.eq_iff.trans ?_⟩
  rw [prod_eq_all _ _ (fun b => (h b).pos.trans_le (h b).ax) (fun b => (h b).xd),
    prod_eq_all _ _ (fun b => (h b).pos.trans_le (h b).ay) (fun b => (h b).yd)]
  apply or_congr
  · exact forall_congr' (fun b => refinement_eq_iff ht _ _ (row_nonneg (hp b)))
  · apply forall_congr'
    intro b
    have eq := refinement_eq_iff ht Finset.univ _ (col_nonneg (hp b) Finset.univ)
    rw [sum_colMass] at eq
    exact eq

end SubentropyCertificates.ClassicalSSA
