module

public import SubentropyCertificates.ClassicalSSAKernel
public import SubentropyCertificates.ClassicalStrict
import all SubentropyCertificates.BinaryTableDeficit

/-! Classical strong subadditivity for the library's determinant-integral
subentropy, including both directions of the equality condition. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped BigOperators
namespace SubentropyCertificates.ClassicalSSA
open SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

private def densityKernel {D : Type*} [Fintype D] [DecidableEq D] (w : D → ℝ) :=
  subentropyKernel (diagonal (fun i => (w i : ℂ)))

private theorem kernel_identity {D : Type*} [Fintype D] [DecidableEq D] (p : D → ℝ)
    {s : ℝ} (hs : 0 < s) : densityKernel p s = 1/(1+s⁻¹) - kernel s⁻¹ p := by
  rw [densityKernel, SubentropyCertificates.QubitDeficit.kernel_reciprocal p hs]
  simp [kernel, factor, Finset.prod_inv_distrib, one_div]

private theorem kernel_integrable {D : Type*} [Fintype D] [DecidableEq D] {p : D → ℝ}
    (hp : p ∈ probabilitySimplex D) : IntegrableOn (densityKernel p) (Ioi 0) :=
  integrable_subentropy_kernel (diagonal_density hp).1 (diagonal_density hp).2

/-- The accepted theorem thm:classical_ssa. The disjunction in determined
places the choice of outer variable outside the quantifier over B. -/
theorem classical_strong_subadditivity (p : A × B × C → ℝ) (hp : p ∈ probabilitySimplex _) :
    classicalSubentropy (marginalB p) + classicalSubentropy p ≤
        classicalSubentropy (marginalAB p) + classicalSubentropy (marginalBC p) ∧
    (classicalSubentropy (marginalB p) + classicalSubentropy p =
        classicalSubentropy (marginalAB p) + classicalSubentropy (marginalBC p) ↔
      determined p) := by
  classical
  let ab := marginalAB p
  let bc := marginalBC p
  let b := marginalB p
  have ht := hp.2
  simp only [Fintype.sum_prod_type] at ht
  have hab : ab ∈ probabilitySimplex _ := by
    refine ⟨fun u => Finset.sum_nonneg (fun k _ => hp.1 (u.1,u.2,k)), ?_⟩
    simpa only [ab, marginalAB, Fintype.sum_prod_type] using ht
  have hbc : bc ∈ probabilitySimplex _ := by
    refine ⟨fun u => Finset.sum_nonneg (fun i _ => hp.1 (i,u.1,u.2)), ?_⟩
    change (∑ u : B × C, ∑ i, p (i,u)) = 1
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact hp.2
  have hb : b ∈ probabilitySimplex _ := by
    refine ⟨fun j => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => hp.1 (i,j,k))), ?_⟩
    change (∑ j, ∑ i, ∑ k, p (i,j,k)) = 1
    rw [Finset.sum_comm]; exact ht
  have hlabels : Nonempty (A × B × C) := by
    by_contra hn
    have := not_nonempty_iff.mp hn
    have hz := hp.2
    simp at hz
  obtain ⟨⟨i,_,k⟩⟩ := hlabels
  have : Nonempty A := ⟨i⟩
  have : Nonempty C := ⟨k⟩
  let f := fun s => densityKernel b s + densityKernel p s
  let g := fun s => densityKernel ab s + densityKernel bc s
  have hf : IntegrableOn f (Ioi 0) := (kernel_integrable hb).add (kernel_integrable hp)
  have hg : IntegrableOn g (Ioi 0) := (kernel_integrable hab).add (kernel_integrable hbc)
  have hpoint (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : f s ≤ g s ∧ (f s = g s ↔ determined p) := by
    dsimp only [f,g,b,ab,bc]
    rw [kernel_identity _ hs, kernel_identity _ hs, kernel_identity _ hs, kernel_identity _ hs]
    have h := classical_ssa_kernel p hp.1 (inv_pos.mpr hs).le
    have he := classical_ssa_kernel_eq_iff p hp.1 (inv_pos.mpr hs)
    refine ⟨by linarith only [h], ?_⟩
    constructor
    · intro eq; exact he.mp (by linarith only [eq])
    · intro det; linarith only [he.mpr det]
  have hf' : (∫ s in Ioi (0 : ℝ), f s) = classicalSubentropy b + classicalSubentropy p :=
    integral_add (kernel_integrable hb) (kernel_integrable hp)
  have hg' : (∫ s in Ioi (0 : ℝ), g s) = classicalSubentropy ab + classicalSubentropy bc :=
    integral_add (kernel_integrable hab) (kernel_integrable hbc)
  change classicalSubentropy b + classicalSubentropy p ≤ classicalSubentropy ab + classicalSubentropy bc ∧
    (classicalSubentropy b + classicalSubentropy p = classicalSubentropy ab + classicalSubentropy bc ↔ _)
  rw [← hf', ← hg']
  refine ⟨setIntegral_mono_on hf hg measurableSet_Ioi (fun s hs => (hpoint s hs).1), ?_⟩
  constructor
  · intro he
    by_contra hn
    exact (integral_strict_mono_Ioi hf hg (fun s hs =>
      lt_of_le_of_ne (hpoint s hs).1 (fun eq => hn ((hpoint s hs).2.mp eq)))).ne he
  · intro h
    exact setIntegral_congr_fun measurableSet_Ioi fun s hs => (hpoint s hs).2.mpr h

end SubentropyCertificates.ClassicalSSA
