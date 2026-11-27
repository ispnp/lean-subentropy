module
public import SubentropyCertificates.CurvatureEstimate

/-! A uniform second derivative bound along every simplex chord, at each
positive determinant parameter. All denominators are at least one. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators
namespace SubentropyCertificates.StrongConcavity
open SubentropyCertificates.ClassicalCurve
variable {D : Type*} [Fintype D]

theorem laplace_chord (hd : 2 ≤ Fintype.card D) {t : ℝ} (ht : 0 ≤ t)
    {p q : D → ℝ} (hp : p ∈ probabilitySimplex D) (hq : q ∈ probabilitySimplex D)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    laplace t (a • p+b • q) + (a*b/2*energy (q-p))*(t^2*Real.exp (-(rate (Fintype.card D)*t))) ≤
      a*laplace t p + b*laplace t q := by
  let h := q-p
  let P (x : ℝ) (i : D) := p i+x*h i
  let L (x : ℝ) := laplace t (P x)
  let v (x : ℝ) (i : D) := t*h i/(1+t*P x i)
  let V (x : ℝ) := ∑ i, v x i
  let W (x : ℝ) := ∑ i, (v x i)^2
  let k := t^2 * Real.exp (-(rate (Fintype.card D)*t)) * energy h
  have hsum : ∑ i, h i = 0 := by simp [h,Finset.sum_sub_distrib,hp.2,hq.2]
  have hP {x : ℝ} (hx : x ∈ Icc 0 1) : P x ∈ probabilitySimplex D := by
    have he : P x = (1-x) • p + x • q := by
      funext i; change p i+x*(q i-p i) = (1-x)*p i+x*q i; ring
    rw [he]; exact (simplex_convex D) hp hq (sub_nonneg.mpr hx.2) hx.1 (by ring)
  have derivatives {x : ℝ} (hx : x ∈ Icc 0 1) :
      HasDerivAt L (L x * -(V x)) x ∧ HasDerivAt V (-W x) x := by
    have hden (i : D) : 0 < 1+t*P x i := by have := (hP hx).1 i; positivity
    have hd₁ (i : D) : HasDerivAt (fun z => 1+t*P z i) (t*h i) x := by
      simpa [P] using (((hasDerivAt_id x).mul_const (h i)).const_add (p i) |>.const_mul t |>.const_add 1)
    have hl (i : D) : HasDerivAt (fun z => Real.log (1+t*P z i)) (v x i) x :=
      (hd₁ i).log (hden i).ne'
    have hv (i : D) : HasDerivAt (fun z => v z i) (-(v x i)^2) x := by
      convert (hasDerivAt_const x (t*h i)).div (hd₁ i) (hden i).ne' using 1
      dsimp [v]; rw [div_pow]; ring
    have hlog := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hl i)
    have hrat := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hv i)
    exact ⟨hlog.neg.exp,by simpa only [V,W,Finset.sum_neg_distrib] using hrat⟩
  let f (x : ℝ) := L x - k/2*x^2
  let f' (x : ℝ) := L x * -(V x) - k*x
  let f'' (x : ℝ) := L x *((V x)^2+W x)-k
  have hd₁ {x : ℝ} (hx : x ∈ Icc 0 1) : HasDerivAt f (f' x) x := by
    convert (derivatives hx).1.sub (((hasDerivAt_id x).pow 2).const_mul (k/2)) using 1
    · rfl
    · dsimp [f']; ring
  have hd₂ {x : ℝ} (hx : x ∈ Icc 0 1) : HasDerivAt f' (f'' x) x := by
    obtain ⟨hl,hv⟩ := derivatives hx
    convert (hl.mul hv.neg).sub ((hasDerivAt_id x).const_mul k) using 1
    · rfl
    · dsimp [f'']; ring
  have hconv : ConvexOn ℝ (Icc 0 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (fun x hx => (hd₁ hx).continuousAt.continuousWithinAt)
      (fun _ hx => (hd₁ (interior_subset hx)).hasDerivWithinAt)
      (fun _ hx => (hd₂ (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hc : k ≤ L x * W x := laplace_curvature_lower hd ht (hP (interior_subset hx)) hsum
    have hl : 0 ≤ L x := Real.exp_nonneg _
    dsimp [f'']; nlinarith [mul_nonneg hl (sq_nonneg (V x))]
  have h0 : P 0 = p := by funext i; simp [P]
  have h1 : P 1 = q := by funext i; simp [P,h]
  have hbP : P b = a • p+b • q := by
    funext i; change p i+b*(q i-p i)=a*p i+b*q i
    linear_combination -p i*hab
  have hmix := hconv.2 (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num) ha hb hab
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,f,L,h0,h1,hbP,one_pow] at hmix
  have hab' : a*b=b-b^2 := by linear_combination b*hab
  rw [hab']
  change _ ≤ _
  dsimp [k,h] at hmix
  nlinarith only [hmix]

end SubentropyCertificates.StrongConcavity
