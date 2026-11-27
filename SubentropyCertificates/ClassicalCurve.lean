module

public import SubentropyCertificates.PinchingUpper
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The classical extremal spectrum

The parameter `m` represents `n - 2`: the label set is
`Option (Fin (m + 1))`, with distinguished coordinate `none` and `m + 1`
remaining coordinates. Thus `phi m` is exactly the manuscript's `Phi_(m+2)`.
No new definition of subentropy is introduced: `classicalSubentropy` is
the determinant-integral subentropy of the diagonal density matrix.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
open D5.S3.Quantum.Subentropy.PinchingGap

def probabilitySimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

def classicalSubentropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) : ℝ := matrixSubentropy (diagonal (fun i => (p i : ℂ)))

theorem diagonal_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : p ∈ probabilitySimplex ι) :
    (diagonal (fun i => (p i : ℂ))).PosSemidef ∧
      (diagonal (fun i => (p i : ℂ))).trace = 1 := by
  refine ⟨Matrix.PosSemidef.diagonal (fun i => by
    simpa [Complex.le_def] using hp.1 i), ?_⟩
  rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, hp.2, Complex.ofReal_one]

theorem simplex_convex (ι : Type*) [Fintype ι] :
    Convex ℝ (probabilitySimplex ι) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hp.2, hq.2, mul_one, hab]

theorem diagonal_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (a b : ℝ) :
    diagonal (fun i => ((a * p i + b * q i : ℝ) : ℂ)) =
      a • diagonal (fun i => (p i : ℂ)) + b • diagonal (fun i => (q i : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_add,
      Complex.ofReal_mul]
  · simp [h, Matrix.smul_apply]

theorem classical_subentropy_concave {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) : ConcaveOn ℝ (probabilitySimplex ι) classicalSubentropy := by
  refine ⟨simplex_convex ι, ?_⟩
  intro p hp q hq a b ha hb hab
  have h := (matrix_subentropy_concave i₀).2 (diagonal_density hp)
    (diagonal_density hq) ha hb hab
  simpa only [classicalSubentropy, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    diagonal_affine] using h

theorem classical_subentropy_reindex {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) (e : ι ≃ κ) :
    classicalSubentropy (p ∘ e) = classicalSubentropy p := by
  unfold classicalSubentropy matrixSubentropy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [kernel_diagonal _ t (ne_of_gt ht), kernel_diagonal _ t (ne_of_gt ht)]
  congr 1
  exact e.prod_comp (fun i => t / (t + p i))

def extremalVector (m : ℕ) (u : ℝ) : Option (Fin (m + 1)) → ℝ
  | none => 1 - u
  | some _ => u / (m + 1 : ℕ)

def phi (m : ℕ) (u : ℝ) : ℝ := classicalSubentropy (extremalVector m u)

def uniformError (m : ℕ) : ℝ := 1 - 1 / (m + 2 : ℕ)

theorem extremal_probability (m : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    extremalVector m u ∈ probabilitySimplex (Option (Fin (m + 1))) := by
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | none => exact sub_nonneg.mpr hu.2
    | some i => exact div_nonneg hu.1 (by positivity)
  · simp only [extremalVector, Fintype.sum_option, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm : (m + 1 : ℕ) ≠ (0 : ℝ) := by positivity
    field_simp
    ring

theorem extremal_affine (m : ℕ) (u v a b : ℝ) (hab : a + b = 1) :
    extremalVector m (a * u + b * v) =
      a • extremalVector m u + b • extremalVector m v := by
  funext i
  cases i with
  | none => simp only [extremalVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; nlinarith
  | some i => simp only [extremalVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem phi_concave (m : ℕ) : ConcaveOn ℝ (Icc (0 : ℝ) 1) (phi m) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro u hu v hv a b ha hb hab
  have h := (classical_subentropy_concave (none : Option (Fin (m + 1)))).2
    (extremal_probability m hu) (extremal_probability m hv) ha hb hab
  simpa only [phi, smul_eq_mul, ← extremal_affine m u v a b hab] using h

theorem phi_zero (m : ℕ) : phi m 0 = 0 := by
  unfold phi classicalSubentropy matrixSubentropy
  have hk : ∀ t ∈ Ioi (0 : ℝ),
      subentropyKernel (diagonal (fun i => (extremalVector m 0 i : ℂ))) t = 0 := by
    intro t ht
    rw [kernel_diagonal _ t (ne_of_gt ht)]
    simp [extremalVector, Fintype.prod_option]
    have ht0 : t ≠ 0 := ht.ne'
    have ht1 : t + 1 ≠ 0 := by linarith [ht.out]
    have ht2 : 1 + t ≠ 0 := by linarith [ht.out]
    field_simp [ht0, ht1, ht2, pow_succ]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hk]
  simp

theorem extremal_uniform (m : ℕ) :
    extremalVector m (uniformError m) = fun _ => (1 : ℝ) / (m + 2 : ℕ) := by
  funext i
  cases i <;> simp only [extremalVector, uniformError]
  · ring
  · have hm : (m + 1 : ℕ) ≠ (0 : ℝ) := by positivity
    have hn : (m + 2 : ℕ) ≠ (0 : ℝ) := by positivity
    push_cast
    push_cast at hm hn
    field_simp
    ring

end SubentropyCertificates.ClassicalCurve
