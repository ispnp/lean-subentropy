module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
The normalized four-cell inequality in Appendix A of
"Quantum Subentropy: Subadditivity and Sharp Bounds on Discrimination Error".

These are scalar real inequalities. No subentropy functional or quantum state
is defined here; the analytic and matrix bridges are separate targets.
-/

namespace SubentropyCertificates.FourCell

def U (a b c d : ℝ) : ℝ := (a + b) * (c + d)
def V (a b c d : ℝ) : ℝ := (a + c) * (b + d)
def W (a b c d : ℝ) : ℝ := a*b + a*c + a*d + b*c + b*d + c*d
def X (a b c d : ℝ) : ℝ := a*b*c + a*b*d + a*c*d + b*c*d
def Y (a b c d : ℝ) : ℝ := a*b*c*d
def E (a b c d : ℝ) : ℝ := a*d + b*c

def rowDen (a b c d t : ℝ) : ℝ := 1 + t + U a b c d * t^2
def colDen (a b c d t : ℝ) : ℝ := 1 + t + V a b c d * t^2
def cellDen (a b c d t : ℝ) : ℝ :=
  1 + t + W a b c d * t^2 + X a b c d * t^3 + Y a b c d * t^4

def numerator (a b c d t : ℝ) : ℝ :=
  E a b c d * t^2 + (2*E a b c d - X a b c d) * t^3 +
  (E a b c d - 2*X a b c d - Y a b c d + 2*U a b c d*V a b c d) * t^4 +
  (-X a b c d - 2*Y a b c d + 2*U a b c d*V a b c d) * t^5 +
  (-Y a b c d + U a b c d*V a b c d*W a b c d) * t^6 +
  U a b c d*V a b c d*X a b c d * t^7 +
  U a b c d*V a b c d*Y a b c d * t^8

/-- The expansion in Appendix A, before dividing by positive denominators. -/
theorem numerator_identity (a b c d t : ℝ) :
    rowDen a b c d t * colDen a b c d t * (1 + t + cellDen a b c d t) -
    (1 + t) * cellDen a b c d t * (rowDen a b c d t + colDen a b c d t) =
    numerator a b c d t := by
  unfold rowDen colDen cellDen numerator U V W X Y E
  ring

/-- Grouping the two diagonals gives the quartic identity used in the proof. -/
theorem uv_identity (a b c d : ℝ) (hnorm : a+b+c+d = 1) :
    U a b c d * V a b c d = X a b c d + (a*d-b*c)^2 := by
  unfold U V X
  linear_combination (a*b*c + a*b*d + a*c*d + b*c*d) * hnorm

/-- The only difficult coefficient estimate in Appendix A. -/
theorem xw_lower_bound (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hnorm : a+b+c+d = 1) :
    4 * Y a b c d ≤ X a b c d * W a b c d := by
  let m := a*d
  let n := b*c
  let s := a+d
  let k := b+c
  have hm : 0 ≤ m := mul_nonneg ha hd
  have hn : 0 ≤ n := mul_nonneg hb hc
  have hs : 0 ≤ s := add_nonneg ha hd
  have hk : 0 ≤ k := add_nonneg hb hc
  have hsk : s+k = 1 := by dsimp [s, k]; linarith
  have hms : 0 ≤ s^2-4*m := by dsimp [s, m]; nlinarith [sq_nonneg (a-d)]
  have hnk : 0 ≤ k^2-4*n := by dsimp [k, n]; nlinarith [sq_nonneg (b-c)]
  have hx : X a b c d = m*k+n*s := by dsimp [X, m, n, k, s]; ring
  have hw : W a b c d = m+n+s*k := by dsimp [W, m, n, k, s]; ring
  have hy : Y a b c d = m*n := by dsimp [Y, m, n]; ring
  have hxpos : 0 ≤ m*k+n*s := by positivity
  have hfirst : (m*k+n*s)*(s*k) ≤ (m*k+n*s)*(m+n+s*k) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hxpos
  have hsecond : 4*(m*n)*(s+k) ≤ (m*k+n*s)*(s*k) := by
    nlinarith [mul_nonneg (mul_nonneg hm hs) hnk,
      mul_nonneg (mul_nonneg hn hk) hms]
  rw [hsk] at hsecond
  rw [hx, hw, hy]
  nlinarith

/-- The polynomial is bounded below by its quadratic term. -/
theorem numerator_lower_bound (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hnorm : a+b+c+d = 1) (ht : 0 ≤ t) :
    E a b c d * t^2 ≤ numerator a b c d t := by
  have ha1 : a ≤ 1 := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hd1 : d ≤ 1 := by linarith
  have hu : 0 ≤ U a b c d := by unfold U; positivity
  have hv : 0 ≤ V a b c d := by unfold V; positivity
  have hw : 0 ≤ W a b c d := by unfold W; positivity
  have hx : 0 ≤ X a b c d := by unfold X; positivity
  have hy : 0 ≤ Y a b c d := by unfold Y; positivity
  have hmn : a*d ≤ 1 := le_trans (mul_le_of_le_one_right ha hd1) ha1
  have he_y : Y a b c d ≤ E a b c d := by
    have hbc : 0 ≤ b*c := mul_nonneg hb hc
    have hmul := mul_le_of_le_one_left hbc hmn
    dsimp [Y, E]
    nlinarith [mul_nonneg ha hd]
  have hx_e : X a b c d ≤ E a b c d := by
    have h1 := mul_nonneg (mul_nonneg ha hd) (show 0 ≤ 1-b-c by linarith)
    have h2 := mul_nonneg (mul_nonneg hb hc) (show 0 ≤ 1-a-d by linarith)
    dsimp [X, E]
    nlinarith
  have huv := uv_identity a b c d hnorm
  have hcoeff4 : 0 ≤ E a b c d - 2*X a b c d - Y a b c d +
      2*U a b c d*V a b c d := by nlinarith [sq_nonneg (a*d-b*c)]
  have hcoeff5 : 0 ≤ -X a b c d - 2*Y a b c d +
      2*U a b c d*V a b c d := by
    have h1 : 0 ≤ a*d*(b+c-b*c) := by
      have hbc := mul_le_of_le_one_right hb hc1
      exact mul_nonneg (mul_nonneg ha hd) (by linarith)
    have h2 : 0 ≤ b*c*(a+d-a*d) := by
      have had := mul_le_of_le_one_right ha hd1
      exact mul_nonneg (mul_nonneg hb hc) (by linarith)
    have hexpand : X a b c d - 2*Y a b c d =
        a*d*(b+c-b*c) + b*c*(a+d-a*d) := by unfold X Y; ring
    nlinarith [sq_nonneg (a*d-b*c)]
  have hcoeff6 : 0 ≤ -Y a b c d + U a b c d*V a b c d*W a b c d := by
    have hbound := xw_lower_bound a b c d ha hb hc hd hnorm
    have hprod := mul_nonneg (sq_nonneg (a*d-b*c)) hw
    nlinarith [congrArg (fun z : ℝ => z * W a b c d) huv]
  have hcoeff3 : 0 ≤ 2*E a b c d - X a b c d := by linarith
  have htail : 0 ≤
      (2*E a b c d - X a b c d) * t^3 +
      (E a b c d - 2*X a b c d - Y a b c d + 2*U a b c d*V a b c d) * t^4 +
      (-X a b c d - 2*Y a b c d + 2*U a b c d*V a b c d) * t^5 +
      (-Y a b c d + U a b c d*V a b c d*W a b c d) * t^6 +
      U a b c d*V a b c d*X a b c d * t^7 +
      U a b c d*V a b c d*Y a b c d * t^8 := by positivity
  unfold numerator
  linarith

/-- All seven numerator coefficients are nonnegative, including boundary cases. -/
theorem numerator_nonneg (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hnorm : a+b+c+d = 1) (ht : 0 ≤ t) :
    0 ≤ numerator a b c d t := by
  have h := numerator_lower_bound a b c d t ha hb hc hd hnorm ht
  have he : 0 ≤ E a b c d * t^2 := by unfold E; positivity
  linarith

/-- Appendix A's normalized four-cell scalar inequality. -/
theorem normalized_four_cell (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hnorm : a+b+c+d = 1) (ht : 0 ≤ t) :
    1 / rowDen a b c d t + 1 / colDen a b c d t ≤
    1 / cellDen a b c d t + 1 / (1+t) := by
  have hr : 0 < rowDen a b c d t := by unfold rowDen U; positivity
  have hc' : 0 < colDen a b c d t := by unfold colDen V; positivity
  have hp : 0 < cellDen a b c d t := by unfold cellDen W X Y; positivity
  have hz : 0 < 1+t := by positivity
  have hnum := numerator_nonneg a b c d t ha hb hc hd hnorm ht
  have hid := numerator_identity a b c d t
  have hleft : 1 / rowDen a b c d t + 1 / colDen a b c d t =
      (rowDen a b c d t + colDen a b c d t) /
      (rowDen a b c d t * colDen a b c d t) := by
    field_simp [ne_of_gt hr, ne_of_gt hc']
    ring
  have hright : 1 / cellDen a b c d t + 1 / (1+t) =
      (1+t+cellDen a b c d t) / (cellDen a b c d t * (1+t)) := by
    field_simp [ne_of_gt hp, ne_of_gt hz]
  rw [hleft, hright]
  apply (div_le_div_iff₀ (mul_pos hr hc') (mul_pos hp hz)).mpr
  nlinarith

/-- The same inequality with the actual reciprocal-product denominators. -/
theorem normalized_four_cell_products (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hnorm : a+b+c+d = 1) (ht : 0 ≤ t) :
    1 / ((1+(a+b)*t)*(1+(c+d)*t)) +
      1 / ((1+(a+c)*t)*(1+(b+d)*t)) ≤
    1 / ((1+a*t)*(1+b*t)*(1+c*t)*(1+d*t)) + 1/(1+t) := by
  have hr : rowDen a b c d t = (1+(a+b)*t)*(1+(c+d)*t) := by
    unfold rowDen U
    linear_combination -t * hnorm
  have hc' : colDen a b c d t = (1+(a+c)*t)*(1+(b+d)*t) := by
    unfold colDen V
    linear_combination -t * hnorm
  have hp : cellDen a b c d t = (1+a*t)*(1+b*t)*(1+c*t)*(1+d*t) := by
    unfold cellDen W X Y
    linear_combination -t * hnorm
  simpa only [hr, hc', hp] using normalized_four_cell a b c d t ha hb hc hd hnorm ht

/-- Strictness follows from the quadratic coefficient when both diagonals have mass. -/
theorem normalized_four_cell_products_strict (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hnorm : a+b+c+d = 1) (ht : 0 < t) (he : 0 < E a b c d) :
    1 / ((1+(a+b)*t)*(1+(c+d)*t)) +
      1 / ((1+(a+c)*t)*(1+(b+d)*t)) <
    1 / ((1+a*t)*(1+b*t)*(1+c*t)*(1+d*t)) + 1/(1+t) := by
  have hr : 0 < rowDen a b c d t := by unfold rowDen U; positivity
  have hc' : 0 < colDen a b c d t := by unfold colDen V; positivity
  have hp : 0 < cellDen a b c d t := by unfold cellDen W X Y; positivity
  have hz : 0 < 1+t := by positivity
  have hbound := numerator_lower_bound a b c d t ha hb hc hd hnorm (le_of_lt ht)
  have hnum : 0 < numerator a b c d t := lt_of_lt_of_le (by positivity) hbound
  have hid := numerator_identity a b c d t
  have hrprod : rowDen a b c d t = (1+(a+b)*t)*(1+(c+d)*t) := by
    unfold rowDen U
    linear_combination -t * hnorm
  have hcprod : colDen a b c d t = (1+(a+c)*t)*(1+(b+d)*t) := by
    unfold colDen V
    linear_combination -t * hnorm
  have hpprod : cellDen a b c d t = (1+a*t)*(1+b*t)*(1+c*t)*(1+d*t) := by
    unfold cellDen W X Y
    linear_combination -t * hnorm
  rw [← hrprod, ← hcprod, ← hpprod]
  have hleft : 1 / rowDen a b c d t + 1 / colDen a b c d t =
      (rowDen a b c d t + colDen a b c d t) /
      (rowDen a b c d t * colDen a b c d t) := by
    field_simp [ne_of_gt hr, ne_of_gt hc']
    ring
  have hright : 1 / cellDen a b c d t + 1 / (1+t) =
      (1+t+cellDen a b c d t) / (cellDen a b c d t * (1+t)) := by
    field_simp [ne_of_gt hp, ne_of_gt hz]
  rw [hleft, hright]
  apply (div_lt_div_iff₀ (mul_pos hr hc') (mul_pos hp hz)).mpr
  nlinarith

noncomputable def rowKernel (a b c d t : ℝ) : ℝ := 1 / ((1+(a+b)*t)*(1+(c+d)*t))
noncomputable def columnKernel (a b c d t : ℝ) : ℝ := 1 / ((1+(a+c)*t)*(1+(b+d)*t))
noncomputable def cellKernel (a b c d t : ℝ) : ℝ :=
  1 / ((1+a*t)*(1+b*t)*(1+c*t)*(1+d*t))
noncomputable def totalKernel (a b c d t : ℝ) : ℝ := 1 / (1+t*(a+b+c+d))

/-- Vanishing cross mass is exactly support in a single row or column. -/
theorem cross_zero_iff_marginal_zero (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    E a b c d = 0 ↔ a+b = 0 ∨ c+d = 0 ∨ a+c = 0 ∨ b+d = 0 := by
  constructor
  · intro he
    have had : a*d = 0 := by unfold E at he; nlinarith [mul_nonneg ha hd, mul_nonneg hb hc]
    have hbc : b*c = 0 := by unfold E at he; nlinarith [mul_nonneg ha hd, mul_nonneg hb hc]
    rcases mul_eq_zero.mp had with ha0 | hd0
    · rcases mul_eq_zero.mp hbc with hb0 | hc0
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · rcases mul_eq_zero.mp hbc with hb0 | hc0
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
      · exact Or.inr (Or.inl (by linarith))
  · rintro (h | h | h | h)
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      simp [E, ha0, hb0]
    · have hc0 : c = 0 := by linarith
      have hd0 : d = 0 := by linarith
      simp [E, hc0, hd0]
    · have ha0 : a = 0 := by linarith
      have hc0 : c = 0 := by linarith
      simp [E, ha0, hc0]
    · have hb0 : b = 0 := by linarith
      have hd0 : d = 0 := by linarith
      simp [E, hb0, hd0]

/-- Positive cross mass is equivalent to positivity of all four marginal entries. -/
theorem cross_pos_iff_marginals_pos (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 < E a b c d ↔ 0 < a+b ∧ 0 < c+d ∧ 0 < a+c ∧ 0 < b+d := by
  constructor
  · intro he
    have hp : 0 < a*d ∨ 0 < b*c := by
      by_cases h : 0 < a*d
      · exact Or.inl h
      · right; unfold E at he; linarith
    rcases hp with hp | hp
    · rcases mul_pos_iff.mp hp with ⟨ha', hd'⟩ | ⟨ha', hd'⟩
      · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · linarith
    · rcases mul_pos_iff.mp hp with ⟨hb', hc'⟩ | ⟨hb', hc'⟩
      · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · linarith
  · rintro ⟨hr1, hr2, hc1, hc2⟩
    have he : 0 ≤ E a b c d := by unfold E; positivity
    by_contra h
    have hz : E a b c d = 0 := by linarith
    rcases (cross_zero_iff_marginal_zero a b c d ha hb hc hd).mp hz with h | h | h | h <;>
      linarith

private theorem normalized_kernel_rescaling (a b c d t M : ℝ)
    (hM : a+b+c+d = M) (hMpos : 0 < M) :
    rowKernel (a/M) (b/M) (c/M) (d/M) (t*M) = rowKernel a b c d t ∧
    columnKernel (a/M) (b/M) (c/M) (d/M) (t*M) = columnKernel a b c d t ∧
    cellKernel (a/M) (b/M) (c/M) (d/M) (t*M) = cellKernel a b c d t ∧
    totalKernel (a/M) (b/M) (c/M) (d/M) (t*M) = totalKernel a b c d t := by
  have hn : a/M+b/M+c/M+d/M = 1 := by
    rw [← add_div, ← add_div, ← add_div, hM, div_self (ne_of_gt hMpos)]
  have hscale (x : ℝ) : x/M*(t*M) = x*t := by
    calc
      _ = x*t*(M/M) := by ring
      _ = x*t := by rw [div_self (ne_of_gt hMpos), mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rowKernel, ← add_div, hscale]
  · simp only [columnKernel, ← add_div, hscale]
  · simp only [cellKernel, hscale]
  · simp only [totalKernel, hn, mul_one, hM]

/-- The non-strict inequality in the manuscript's four-cell lemma, for any mass. -/
theorem four_cell (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    rowKernel a b c d t + columnKernel a b c d t ≤
    cellKernel a b c d t + totalKernel a b c d t := by
  by_cases hz : a+b+c+d = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    have hd0 : d = 0 := by linarith
    simp [rowKernel, columnKernel, cellKernel, totalKernel, ha0, hb0, hc0, hd0]
  · let M := a+b+c+d
    have hMpos : 0 < M := by dsimp [M]; exact lt_of_le_of_ne (by positivity) (Ne.symm hz)
    have hn : a/M+b/M+c/M+d/M = 1 := by
      rw [← add_div, ← add_div, ← add_div, show a+b+c+d = M from rfl,
        div_self (ne_of_gt hMpos)]
    have h := normalized_four_cell_products (a/M) (b/M) (c/M) (d/M) (t*M)
      (by positivity) (by positivity) (by positivity) (by positivity) hn (by positivity)
    have h' : rowKernel (a/M) (b/M) (c/M) (d/M) (t*M) +
        columnKernel (a/M) (b/M) (c/M) (d/M) (t*M) ≤
        cellKernel (a/M) (b/M) (c/M) (d/M) (t*M) +
        totalKernel (a/M) (b/M) (c/M) (d/M) (t*M) := by
      simpa only [rowKernel, columnKernel, cellKernel, totalKernel, hn, mul_one] using h
    rcases normalized_kernel_rescaling a b c d t M rfl hMpos with ⟨hr, hc', hp, hz'⟩
    simpa only [hr, hc', hp, hz'] using h'

theorem four_cell_eq_of_cross_zero (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : E a b c d = 0) :
    rowKernel a b c d t + columnKernel a b c d t =
    cellKernel a b c d t + totalKernel a b c d t := by
  rcases (cross_zero_iff_marginal_zero a b c d ha hb hc hd).mp he with h | h | h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [rowKernel, columnKernel, cellKernel, totalKernel, ha0, hb0, add_comm]
    ring
  · have hc0 : c = 0 := by linarith
    have hd0 : d = 0 := by linarith
    simp [rowKernel, columnKernel, cellKernel, totalKernel, hc0, hd0, add_comm]
    ring
  · have ha0 : a = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp [rowKernel, columnKernel, cellKernel, totalKernel, ha0, hc0]
    ring
  · have hb0 : b = 0 := by linarith
    have hd0 : d = 0 := by linarith
    simp [rowKernel, columnKernel, cellKernel, totalKernel, hb0, hd0]
    ring

theorem four_cell_strict_of_cross_pos (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : 0 < t) (he : 0 < E a b c d) :
    rowKernel a b c d t + columnKernel a b c d t <
    cellKernel a b c d t + totalKernel a b c d t := by
  let M := a+b+c+d
  have hmarg := (cross_pos_iff_marginals_pos a b c d ha hb hc hd).mp he
  have hMpos : 0 < M := by dsimp [M]; linarith [hmarg.1, hmarg.2.1]
  have hn : a/M+b/M+c/M+d/M = 1 := by
    rw [← add_div, ← add_div, ← add_div, show a+b+c+d = M from rfl,
      div_self (ne_of_gt hMpos)]
  have he' : 0 < E (a/M) (b/M) (c/M) (d/M) := by
    calc
      0 < E a b c d * (M⁻¹*M⁻¹) := by positivity
      _ = E (a/M) (b/M) (c/M) (d/M) := by unfold E; simp only [div_eq_mul_inv]; ring
  have h := normalized_four_cell_products_strict (a/M) (b/M) (c/M) (d/M) (t*M)
    (by positivity) (by positivity) (by positivity) (by positivity) hn (by positivity) he'
  have h' : rowKernel (a/M) (b/M) (c/M) (d/M) (t*M) +
      columnKernel (a/M) (b/M) (c/M) (d/M) (t*M) <
      cellKernel (a/M) (b/M) (c/M) (d/M) (t*M) +
      totalKernel (a/M) (b/M) (c/M) (d/M) (t*M) := by
    simpa only [rowKernel, columnKernel, cellKernel, totalKernel, hn, mul_one] using h
  rcases normalized_kernel_rescaling a b c d t M rfl hMpos with ⟨hr, hc', hp, hz⟩
  simpa only [hr, hc', hp, hz] using h'

/-- Strictness is exactly positivity of both entries of both binary marginals. -/
theorem four_cell_strict_iff (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (ht : 0 < t) :
    (rowKernel a b c d t + columnKernel a b c d t <
      cellKernel a b c d t + totalKernel a b c d t) ↔
    0 < a+b ∧ 0 < c+d ∧ 0 < a+c ∧ 0 < b+d := by
  rw [← cross_pos_iff_marginals_pos a b c d ha hb hc hd]
  constructor
  · intro h
    have he : 0 ≤ E a b c d := by unfold E; positivity
    by_contra h'
    have hz : E a b c d = 0 := by linarith
    have heq := four_cell_eq_of_cross_zero a b c d t ha hb hc hd hz
    linarith
  · exact four_cell_strict_of_cross_pos a b c d t ha hb hc hd ht

/-- Equality holds precisely at t = 0 or for support in one row or column. -/
theorem four_cell_eq_iff (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    (rowKernel a b c d t + columnKernel a b c d t =
      cellKernel a b c d t + totalKernel a b c d t) ↔
    t = 0 ∨ a+b = 0 ∨ c+d = 0 ∨ a+c = 0 ∨ b+d = 0 := by
  rw [← cross_zero_iff_marginal_zero a b c d ha hb hc hd]
  constructor
  · intro heq
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    · right
      have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have he : 0 ≤ E a b c d := by unfold E; positivity
      by_contra h'
      have hpos : 0 < E a b c d := lt_of_le_of_ne he (Ne.symm h')
      have hlt := four_cell_strict_of_cross_pos a b c d t ha hb hc hd htpos hpos
      linarith
  · rintro (ht0 | he0)
    · simp [rowKernel, columnKernel, cellKernel, totalKernel, ht0]
    · exact four_cell_eq_of_cross_zero a b c d t ha hb hc hd he0

end SubentropyCertificates.FourCell
