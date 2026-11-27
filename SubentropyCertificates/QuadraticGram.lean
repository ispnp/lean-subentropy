module

public import SubentropyCertificates.QuantumMeasurement
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen

/-! Twice the off-block Hilbert--Schmidt energy of a Gram matrix. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.Quadratic
open SubentropyCertificates.MeasurementPosterior
variable {X B Y : Type*} [Fintype X] [DecidableEq X] [Fintype B] [Fintype Y]

def distinctPairs (X : Type*) [Fintype X] [DecidableEq X] :=
  (Finset.univ : Finset (X × X)).filter (fun z => z.1 ≠ z.2)
def blockSquare (H : Matrix (X × B) (X × B) ℂ) (xz : X × X) :=
  ∑ k : B × B, Complex.normSq (H (xz.1,k.1) (xz.2,k.2))
def offSquare (H : Matrix (X × B) (X × B) ℂ) :=
  ∑ xz ∈ distinctPairs X, blockSquare H xz

theorem distinct_sum (f : X → X → ℝ) :
    (∑ z ∈ distinctPairs X, f z.1 z.2) = (∑ x, ∑ z, f x z) - ∑ x, f x x := by
  have h (x z) : f x z = (if x≠z then f x z else 0) + (if x=z then f x z else 0) := by
    by_cases hz : x=z <;> simp [hz]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ =>
    Finset.sum_congr (s₁ := Finset.univ) rfl (fun z _ => h x z))
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at hs
  simp only [distinctPairs,Finset.sum_filter,Fintype.sum_prod_type]
  linarith

theorem offSquare_nonneg (H : Matrix (X × B) (X × B) ℂ) : 0 ≤ offSquare H :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private theorem entry_bound {D : Type*} {H : Matrix D D ℂ} (hH : H.PosSemidef) (i j : D) :
    Complex.normSq (H i j) ≤ (H i i).re*(H j j).re := by
  let f : Fin 2 → D := ![i,j]
  have h := (RCLike.nonneg_iff.mp ((hH.submatrix f).det_nonneg)).1
  have hd (a : D) : (H a a).im = 0 := (RCLike.nonneg_iff.mp (hH.diag_nonneg (i := a))).2
  have hh : H j i = star (H i j) := (hH.isHermitian.apply j i).symm
  simpa [Matrix.det_fin_two,f,hh,Complex.mul_re,Complex.normSq_apply,hd] using h

omit [Fintype X] [DecidableEq X] in
theorem blockSquare_le (H : Matrix (X × B) (X × B) ℂ) (hH : H.PosSemidef) (xz : X × X) :
    blockSquare H xz ≤ labelMass H xz.1 * labelMass H xz.2 := by
  unfold blockSquare labelMass
  simp only [Complex.re_sum,Fintype.sum_prod_type,Finset.sum_mul]
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => entry_bound hH _ _

private theorem normSq_mean (q : Y → ℝ) (hq : ∀ y, 0 ≤ q y) (hs : ∑ y, q y = 1)
    (z : Y → ℂ) : Complex.normSq (∑ y, q y • z y) ≤ ∑ y, q y * Complex.normSq (z y) := by
  have hsquare (a : Y → ℝ) : (∑ y, q y*a y)^2 ≤ ∑ y, q y*(a y)^2 := by
    have h := (even_two.convexOn_pow (𝕜 := ℝ)).map_sum_le
      (t := Finset.univ) (w := q) (p := a) (fun y _ => hq y) hs (fun _ _ => Set.mem_univ _)
    simpa only [smul_eq_mul] using h
  simp only [Complex.normSq_apply,Complex.re_sum,Complex.im_sum,Complex.smul_re,
    Complex.smul_im,smul_eq_mul,mul_add,Finset.sum_add_distrib,← sq]
  exact add_le_add (hsquare fun y => (z y).re) (hsquare fun y => (z y).im)

theorem offSquare_mean (q : Y → ℝ) (hq : ∀ y, 0 ≤ q y) (hs : ∑ y, q y = 1)
    (H : Y → Matrix (X × B) (X × B) ℂ) :
    offSquare (∑ y, q y • H y) ≤ ∑ y, q y*offSquare (H y) := by
  unfold offSquare blockSquare
  simp only [Matrix.sum_apply,Matrix.smul_apply,Finset.mul_sum]
  calc
    _ ≤ ∑ xz ∈ distinctPairs X, ∑ k : B × B, ∑ y,
          q y * Complex.normSq (H y (xz.1,k.1) (xz.2,k.2)) :=
      Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => normSq_mean q hq hs _
    _ = _ := by
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (B × B))) (t := (Finset.univ : Finset Y))]
      rw [Finset.sum_comm]

end SubentropyCertificates.Quadratic
