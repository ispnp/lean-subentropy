module

public import SubentropyCertificates.ClassicalCurve
import Mathlib.Algebra.Order.Chebyshev

/-! Classical collision probabilities and the increasing branch of the
quadratic discrimination curve. The number of labels is n=m+2. -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SubentropyCertificates.Quadratic
open SubentropyCertificates.ClassicalCurve

def radius (m : ℕ) : ℝ := (m+1 : ℝ)/(m+2)
def curve (m : ℕ) (u : ℝ) := u - u^2/(2*radius m)
def inverse (m : ℕ) (c : ℝ) := radius m * (1 - Real.sqrt (1 - 2*c/radius m))
def collisionGap {X : Type*} [Fintype X] (b : X → ℝ) := (1 - ∑ x, b x ^ 2)/2

theorem radius_eq (m : ℕ) : radius m = uniformError m := by
  unfold radius uniformError
  push_cast
  field_simp
  ring

theorem radius_pos (m : ℕ) : 0 < radius m := by unfold radius; positivity

theorem curve_formula (m : ℕ) (u : ℝ) :
    curve m u = u - (m+2 : ℝ)/(2*(m+1))*u^2 := by
  unfold curve radius
  field_simp

/-- The distinguished coordinate may be any decision for the observed outcome. -/
theorem collision_coordinate {X : Type*} [Fintype X] [DecidableEq X]
    (m : ℕ) (hn : Fintype.card X = m+2) (b : X → ℝ) (hs : ∑ x, b x = 1) (i : X) :
    collisionGap b ≤ curve m (1-b i) := by
  let s := Finset.univ.erase i
  have hcard : (s.card : ℝ) = (m:ℝ)+1 := by
    simp [s,Finset.card_erase_of_mem,hn]
  have hsum : ∑ x ∈ s, b x = 1-b i := by
    have h := Finset.sum_erase_add (s := Finset.univ) b (Finset.mem_univ i)
    linarith [hs]
  have hsq : (∑ x ∈ s, b x^2) + b i^2 = ∑ x, b x^2 :=
    Finset.sum_erase_add (s := Finset.univ) _ (Finset.mem_univ i)
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := b)
  rw [hcard,hsum] at h
  rw [curve_formula]
  unfold collisionGap
  have hm : 0 < (m:ℝ)+1 := by positivity
  field_simp
  nlinarith [h,congrArg (fun z : ℝ => ((m:ℝ)+1)*z) hsq]

/-- Jensen's inequality for the concave quadratic, in scalar form. -/
theorem curve_average {Y : Type*} [Fintype Y] (m : ℕ) (q v : Y → ℝ)
    (hq : ∀ y, 0 ≤ q y) (hs : ∑ y, q y = 1) :
    (∑ y, q y * curve m (v y)) ≤ curve m (∑ y, q y*v y) := by
  let u := ∑ y, q y*v y
  have hv := Finset.sum_nonneg (s := Finset.univ)
    (fun y _ => mul_nonneg (hq y) (sq_nonneg (v y-u)))
  have hid (y) : q y*(v y-u)^2 = q y*v y^2 - 2*(q y*v y)*u + q y*u^2 := by ring
  simp only [hid,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,
    ← Finset.mul_sum,hs,one_mul] at hv
  have hsq : u^2 ≤ ∑ y, q y*v y^2 := by dsimp [u] at hv ⊢; linarith
  simp only [curve,mul_sub, mul_div_assoc',Finset.sum_sub_distrib,← Finset.sum_div]
  exact sub_le_sub_left (div_le_div_of_nonneg_right hsq (by positivity [radius_pos m])) _

theorem curve_strict (m : ℕ) : StrictMonoOn (curve m) (Icc 0 (radius m)) := by
  intro u hu v hv huv
  have hr := radius_pos m
  have hpos := mul_pos (sub_pos.mpr huv) (show 0 < 2*radius m-u-v by linarith [hu.2,hv.2])
  unfold curve
  field_simp
  nlinarith

theorem inverse_formula (m : ℕ) (c : ℝ) :
    inverse m c = (m+1 : ℝ)/(m+2) *
      (1-Real.sqrt (1-(2*(m+2 : ℝ)/(m+1))*c)) := by
  have h : 2*c/radius m = (2*(m+2 : ℝ)/(m+1))*c := by
    unfold radius
    rw [div_div_eq_mul_div]
    ring
  rw [inverse,h,radius]

theorem curve_le_max (m : ℕ) (u : ℝ) : curve m u ≤ radius m/2 := by
  have hr := radius_pos m
  unfold curve
  field_simp
  nlinarith [sq_nonneg (radius m-u)]

theorem inverse_spec (m : ℕ) (c : ℝ) (hc : c ∈ Icc 0 (radius m/2)) :
    inverse m c ∈ Icc 0 (radius m) ∧ curve m (inverse m c) = c := by
  have hr := radius_pos m
  have hv : 0 ≤ 1-2*c/radius m := by
    have := (div_le_one hr).mpr (show 2*c ≤ radius m by linarith [hc.2])
    linarith
  let s := Real.sqrt (1-2*c/radius m)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = 1-2*c/radius m := Real.sq_sqrt hv
  have hs1 : s ≤ 1 := by nlinarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hc.1) hr.le]
  change radius m*(1-s) ∈ Icc 0 (radius m) ∧ curve m (radius m*(1-s)) = c
  refine ⟨⟨mul_nonneg hr.le (by linarith), ?_⟩,?_⟩
  · nlinarith [mul_nonneg hr.le hs]
  · field_simp [hr.ne'] at hsq
    unfold curve
    field_simp [hr.ne']
    nlinarith [congrArg (fun z : ℝ => radius m*z) hsq]

end SubentropyCertificates.Quadratic
