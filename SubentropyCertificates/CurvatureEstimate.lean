module
public import SubentropyCertificates.QuadraticCurve
public import SubentropyCertificates.ClassicalStrict
public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Algebra.Order.Chebyshev

/-! Directional curvature of the reciprocal determinant on the simplex.
The trace-zero constraint gives the dimension-dependent improvement. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators
namespace SubentropyCertificates.StrongConcavity
open SubentropyCertificates.ClassicalCurve
variable {D : Type*} [Fintype D]

def energy (h : D → ℝ) := ∑ i, h i^2
def fraction (d : ℕ) : ℝ := ((d:ℝ)-1)/d
def rate (d : ℕ) : ℝ := 1+2*fraction d
def mu (d : ℕ) : ℝ := d/(3*(d:ℝ)-2)
def laplace (t : ℝ) (p : D → ℝ) := Real.exp (-(∑ i, Real.log (1+t*p i)))

theorem inv_rate {d : ℕ} (hd : 2 ≤ d) : (rate d)⁻¹ = mu d := by
  have h : 2 ≤ (d:ℝ) := by exact_mod_cast hd
  unfold rate fraction mu
  field_simp
  ring

theorem rate_pos {d : ℕ} (hd : 2 ≤ d) : 0 < rate d := by
  have h : 2 ≤ (d:ℝ) := by exact_mod_cast hd
  have hpos : 0 ≤ fraction d := div_nonneg (by linarith) (by positivity)
  unfold rate; linarith

theorem mu_ge_third {d : ℕ} (hd : 2 ≤ d) : 1/3 ≤ mu d := by
  have h : 2 ≤ (d:ℝ) := by exact_mod_cast hd
  apply (le_div_iff₀ (show 0 < 3*(d:ℝ)-2 by linarith)).mpr
  linarith

theorem variance_coefficient_ge_sixth {d : ℕ} (hd : 2 ≤ d) : 1/6 ≤ mu d/2 := by
  linarith [mu_ge_third hd]

/-- Converting a Jensen gap into a squared deviation in Proposition 12. -/
theorem inverse_variance_coefficient {d : ℕ} (hd : 2 ≤ d) :
    (mu d/2)⁻¹ = 6-4/(d:ℝ) := by
  have h : 2 ≤ (d:ℝ) := by exact_mod_cast hd
  have h₁ : (d:ℝ) ≠ 0 := by linarith
  have h₂ : 3*(d:ℝ)-2 ≠ 0 := by linarith
  unfold mu
  field_simp
  ring

theorem coordinate_energy (hd : 2 ≤ Fintype.card D) {h : D → ℝ} (hh : ∑ i, h i=0) (i : D) :
    h i^2 ≤ fraction (Fintype.card D)*energy h := by
  classical
  let S := Finset.univ.erase i
  have hc : (S.card:ℝ) = (Fintype.card D:ℝ)-1 := by
    simp [S,Finset.card_erase_of_mem,Nat.cast_sub (show 1 ≤ Fintype.card D by omega)]
  have ht : ∑ j ∈ S, h j = -h i := by
    have he := Finset.sum_erase_add (s := Finset.univ) h (Finset.mem_univ i)
    linarith [hh]
  have he : ∑ j ∈ S, h j^2 = energy h - h i^2 := by
    have e := Finset.sum_erase_add (s := Finset.univ) (fun j => h j^2) (Finset.mem_univ i)
    unfold energy; linarith
  have hcauchy := sq_sum_le_card_mul_sum_sq (s := S) (f := h)
  rw [hc,ht,he] at hcauchy
  have hd' : 2 ≤ (Fintype.card D:ℝ) := by exact_mod_cast hd
  unfold fraction
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < (Fintype.card D:ℝ) by linarith)).mpr
  nlinarith only [hcauchy]

private theorem laplace_lower {t : ℝ} (ht : 0 ≤ t) {p : D → ℝ} (hp : p ∈ probabilitySimplex D) :
    Real.exp (-t) ≤ laplace t p := by
  apply Real.exp_le_exp.mpr
  have hi (i : D) : Real.log (1+t*p i) ≤ t*p i := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1+t*p i by
      have := hp.1 i; positivity)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [← Finset.mul_sum,hp.2,mul_one] at h
  linarith

private theorem coordinate_factor {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-(2*x)) ≤ 1/(1+x)^2 := by
  rw [show -(2*x) = -(x+x) by ring,Real.exp_neg,Real.exp_add,one_div]
  apply inv_anti₀ (by positivity)
  rw [← sq]
  exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) 2

/-- A lower bound for the part of the second derivative containing the
sum of squares. The omitted square of the log derivative is nonnegative. -/
theorem laplace_curvature_lower (hd : 2 ≤ Fintype.card D) {t : ℝ} (ht : 0 ≤ t)
    {p h : D → ℝ} (hp : p ∈ probabilitySimplex D) (hh : ∑ i, h i=0) :
    t^2 * Real.exp (-(rate (Fintype.card D)*t)) * energy h ≤
      laplace t p * (∑ i, (t*h i/(1+t*p i))^2) := by
  let c := fraction (Fintype.card D)
  let a := energy h
  have hmean : ∑ i, p i*h i^2 ≤ c*a := by
    calc _ ≤ ∑ i, p i*(c*a) := Finset.sum_le_sum fun i _ =>
                mul_le_mul_of_nonneg_left (coordinate_energy hd hh i) (hp.1 i)
         _ = _ := by rw [← Finset.sum_mul,hp.2,one_mul]
  have htan (i : D) : Real.exp (-(2*t*c))*(1+2*t*(c-p i)) ≤ Real.exp (-(2*(t*p i))) := by
    rw [show -(2*(t*p i)) = -(2*t*c)+2*t*(c-p i) by ring,Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    linarith [Real.add_one_le_exp (2*t*(c-p i))]
  have hi (i : D) : Real.exp (-(2*t*c))*(h i^2 + 2*t*(c*h i^2-p i*h i^2)) ≤
      h i^2/(1+t*p i)^2 := by
    have hx := (htan i).trans (coordinate_factor (mul_nonneg ht (hp.1 i)))
    calc _ = h i^2*(Real.exp (-(2*t*c))*(1+2*t*(c-p i))) := by ring
         _ ≤ _ := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hx (sq_nonneg _)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib] at hsum
  have hw : Real.exp (-(2*t*c))*a ≤ ∑ i, h i^2/(1+t*p i)^2 := by
    apply le_trans _ hsum
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    change a ≤ a + 2*t*(c*a - ∑ i, p i*h i^2)
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sub_nonneg.mpr hmean))
  have hscale : t^2*(Real.exp (-(2*t*c))*a) ≤ ∑ i, (t*h i/(1+t*p i))^2 := by
    calc _ ≤ t^2*(∑ i, h i^2/(1+t*p i)^2) := mul_le_mul_of_nonneg_left hw (sq_nonneg t)
         _ = _ := by
           rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
           rw [div_pow,mul_pow,mul_div_assoc]
  have hprod := mul_le_mul (laplace_lower ht hp) hscale
    (show 0 ≤ t^2*(Real.exp (-(2*t*c))*a) by dsimp [a,energy]; positivity) (Real.exp_nonneg _)
  apply le_trans _ hprod
  rw [show -(rate (Fintype.card D)*t) = -t + -(2*t*c) by dsimp [rate,c]; ring,Real.exp_add]
  exact le_of_eq (by dsimp [a]; ring)

end SubentropyCertificates.StrongConcavity
