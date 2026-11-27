module

public import SubentropyCertificates.FourCell
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Quantitative four-cell comparison for the two-qubit deficit. -/
@[expose] public section
noncomputable section
namespace SubentropyCertificates.FourCell

/-- Retaining the cubic term as well as the quadratic term in the
four-cell numerator yields the factor needed after integration. -/
theorem numerator_cubic_lower_bound (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hnorm : a+b+c+d = 1) (ht : 0 ≤ t) :
    E a b c d * t^2 * (1+t) ≤ numerator a b c d t := by
  have hu : 0 ≤ U a b c d := by unfold U; positivity
  have hv : 0 ≤ V a b c d := by unfold V; positivity
  have hw : 0 ≤ W a b c d := by unfold W; positivity
  have hx : 0 ≤ X a b c d := by unfold X; positivity
  have hy : 0 ≤ Y a b c d := by unfold Y; positivity
  have hx_e : X a b c d ≤ E a b c d := by
    unfold X E
    nlinarith only [mul_nonneg (mul_nonneg ha hd) (show 0 ≤ 1-b-c by linarith),
      mul_nonneg (mul_nonneg hb hc) (show 0 ≤ 1-a-d by linarith)]
  have hxy : 2 * Y a b c d ≤ X a b c d := by
    unfold X Y
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) (show 0 ≤ 1-d by linarith),
      mul_nonneg (mul_nonneg (mul_nonneg ha hb) hd) (show 0 ≤ 1-c by linarith),
      mul_nonneg (mul_nonneg ha hc) hd, mul_nonneg (mul_nonneg hb hc) hd]
  have hxuv : X a b c d ≤ U a b c d * V a b c d := by
    rw [uv_identity a b c d hnorm]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hcoeff4 : 0 ≤ E a b c d - 2*X a b c d - Y a b c d + 2*U a b c d*V a b c d := by
    linarith only [hx_e, hxy, hxuv, hy]
  have hcoeff5 : 0 ≤ -X a b c d - 2*Y a b c d + 2*U a b c d*V a b c d := by
    linarith only [hxy, hxuv]
  have hcoeff6 : 0 ≤ -Y a b c d + U a b c d*V a b c d*W a b c d := by
    linarith only [xw_lower_bound a b c d ha hb hc hd hnorm,
      mul_le_mul_of_nonneg_right hxuv hw, hy]
  have htail : 0 ≤
      (E a b c d - 2*X a b c d - Y a b c d + 2*U a b c d*V a b c d) * t^4 +
      (-X a b c d - 2*Y a b c d + 2*U a b c d*V a b c d) * t^5 +
      (-Y a b c d + U a b c d*V a b c d*W a b c d) * t^6 +
      U a b c d*V a b c d*X a b c d * t^7 +
      U a b c d*V a b c d*Y a b c d * t^8 := by positivity
  unfold numerator
  nlinarith only [htail, mul_nonneg (sub_nonneg.mpr hx_e) (pow_nonneg ht 3)]

theorem marginal_product_le_cross_mass (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : a+b+c+d = 1) : U a b c d * V a b c d ≤ E a b c d := by
  have had : a*d ≤ a := mul_le_of_le_one_right ha (by linarith)
  have hbc : b*c ≤ b := mul_le_of_le_one_right hb (by linarith)
  have hid := uv_identity a b c d hs
  unfold X E at *
  nlinarith only [hid, mul_nonneg (mul_nonneg ha hd) (show 0 ≤ 1-b-c-a*d by linarith),
    mul_nonneg (mul_nonneg hb hc) (show 0 ≤ 1-a-d-b*c by linarith),
    mul_nonneg (mul_nonneg ha hd) (mul_nonneg hb hc)]

private theorem exp_product_bound (x y : ℝ) (hy : 0 ≤ y) :
    (1+x)*(1+y) ≤ Real.exp (x+y) := by
  rw [Real.exp_add]
  exact mul_le_mul (by linarith [Real.add_one_le_exp x]) (by linarith [Real.add_one_le_exp y])
    (by positivity : 0 ≤ 1+y) (Real.exp_nonneg _)

/-- Pointwise lower bound at the paper's reciprocal-determinant parameter. -/
theorem four_cell_exponential_bound (a b c d t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : a+b+c+d = 1) (ht : 0 ≤ t) :
    U a b c d * V a b c d * t^2 * Real.exp (-(3*t)) ≤
      cellKernel a b c d t + 1/(1+t) - rowKernel a b c d t - columnKernel a b c d t := by
  let r := rowDen a b c d t
  let s := colDen a b c d t
  let p := cellDen a b c d t
  have hr : 0 < r := by dsimp [r, rowDen, U]; positivity
  have hs' : 0 < s := by dsimp [s, colDen, V]; positivity
  have hp : 0 < p := by dsimp [p, cellDen, W, X, Y]; positivity
  have hR : r = (1+(a+b)*t)*(1+(c+d)*t) := by
    dsimp [r, rowDen, U]; linear_combination -t * hs
  have hS : s = (1+(a+c)*t)*(1+(b+d)*t) := by
    dsimp [s, colDen, V]; linear_combination -t * hs
  have hP : p = (1+a*t)*(1+b*t)*(1+c*t)*(1+d*t) := by
    dsimp [p, cellDen, W, X, Y]; linear_combination -t * hs
  have heR : r ≤ Real.exp t := by
    calc r = _ := hR
         _ ≤ Real.exp ((a+b)*t+(c+d)*t) := exp_product_bound _ _ (by positivity)
         _ = _ := by congr 1; linear_combination t * hs
  have heS : s ≤ Real.exp t := by
    calc s = _ := hS
         _ ≤ Real.exp ((a+c)*t+(b+d)*t) := exp_product_bound _ _ (by positivity)
         _ = _ := by congr 1; linear_combination t * hs
  have heP : p ≤ Real.exp t := by
    rw [hP, mul_assoc ((1+a*t)*(1+b*t))]
    calc
      _ ≤ Real.exp (a*t+b*t) * Real.exp (c*t+d*t) :=
        mul_le_mul (exp_product_bound _ _ (by positivity)) (exp_product_bound _ _ (by positivity))
          (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; linear_combination t * hs
  have hexp : r*s*p ≤ Real.exp (3*t) := by
    calc r*s*p ≤ (Real.exp t * Real.exp t) * Real.exp t :=
          mul_le_mul (mul_le_mul heR heS hs'.le (Real.exp_nonneg _)) heP hp.le (by positivity)
         _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hN := numerator_cubic_lower_bound a b c d t ha hb hc hd hs ht
  have hid := numerator_identity a b c d t
  change r*s*(1+t+p) - (1+t)*p*(r+s) = _ at hid
  have hz : 0 < 1+t := by positivity
  have hD : E a b c d * t^2 / (r*s*p) ≤ 1/p + 1/(1+t) - 1/r - 1/s := by
    field_simp [hr.ne', hs'.ne', hp.ne', hz.ne']
    -- All cleared factors are positive.
    nlinarith only [hid, hN]
  unfold cellKernel rowKernel columnKernel
  rw [← hP, ← hR, ← hS, Real.exp_neg, ← div_eq_mul_inv]
  refine le_trans ?_ hD
  exact div_le_div₀ (by unfold E; positivity)
    (mul_le_mul_of_nonneg_right (marginal_product_le_cross_mass a b c d ha hb hc hd hs) (sq_nonneg _))
    (by positivity) hexp

end SubentropyCertificates.FourCell
