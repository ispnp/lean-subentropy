module

public import SubentropyCertificates.MarginalPurity
public import D5.S3.Quantum.Subentropy.SpectralFormula

/-! Identify the determinant definition with the continuous extension of
the manuscript's spectral expression at repeated or zero eigenvalues. -/
@[expose] public section
noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Topology BigOperators ComplexOrder
namespace SubentropyCertificates.Representations
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Subadditivity
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
open D5.S3.Quantum.Subentropy.SpectralFormula

variable {D : Type*} [Fintype D] [DecidableEq D]

def simpleSpectra (D : Type*) [Fintype D] : Set (D → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ (∑ i, p i) = 1 ∧ Function.Injective p}

def spectralExpression (p : D → ℝ) : ℝ :=
  -(∑ i, p i ^ Fintype.card D * Real.log (p i) / (∏ j ∈ Finset.univ.erase i, (p i - p j)))

omit [DecidableEq D] in
private theorem positive_simple_spectrum [Nonempty D] : (simpleSpectra D).Nonempty := by
  let w (i : D) : ℝ := ((Fintype.equivFin D i).val : ℝ) + 1
  have hw (i : D) : 0 < w i := by dsimp [w]; positivity
  have hsum : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  refine ⟨fun i => w i / ∑ j, w j, fun i => div_pos (hw i) hsum, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hsum.ne']
  · intro i j hij
    have he := (div_left_inj' hsum.ne').mp hij
    apply (Fintype.equivFin D).injective
    apply Fin.ext
    exact_mod_cast (add_right_cancel he : ((Fintype.equivFin D i).val : ℝ) = ((Fintype.equivFin D j).val : ℝ))

omit [DecidableEq D] in
/-- Every normalized spectrum is approached by strictly positive spectra
with pairwise distinct entries, including at the boundary of the simplex. -/
theorem mem_closure_simple_spectra (p : D → ℝ) (hp : p ∈ probabilitySimplex D) :
    p ∈ closure (simpleSpectra D) := by
  classical
  have : Nonempty D := by
    by_contra! he
    have : IsEmpty D := he
    simpa using hp.2
  obtain ⟨q, hqpos, hqsum, hqinj⟩ := positive_simple_spectrum (D := D)
  let v (t : ℝ) (i : D) := (1 - t) * p i + t * q i
  have hc : Continuous v := by unfold v; fun_prop
  have hv : Tendsto v (𝓝[>] 0) (𝓝 p) := by
    have h : Tendsto v (𝓝[>] 0) (𝓝 (v 0)) := hc.continuousAt.continuousWithinAt
    simpa [v] using h
  apply mem_closure_of_tendsto hv
  have hsep (i j : D) : ∀ᶠ t in 𝓝[>] (0 : ℝ), i ≠ j → v t i ≠ v t j := by
    by_cases hij : p i = p j
    · filter_upwards [self_mem_nhdsWithin] with t ht hne he
      have h : t * q i = t * q j := by simpa only [v, hij, add_right_inj] using he
      exact hne (hqinj (mul_left_cancel₀ (ne_of_gt ht) h))
    · have ho : IsOpen {t | v t i ≠ v t j} :=
        isOpen_ne_fun ((continuous_apply i).comp hc) ((continuous_apply j).comp hc)
      have hm := ho.mem_nhds (x := 0) (by simpa [v] using hij)
      filter_upwards [mem_nhdsWithin_of_mem_nhds hm] with t ht _
      exact ht
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j : D, i ≠ j → v t i ≠ v t j :=
    eventually_all.mpr fun i => eventually_all.mpr (hsep i)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)), hall] with t ht hlt hsep'
  refine ⟨fun i => add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hlt.le) (hp.1 i))
    (mul_pos ht (hqpos i)), ?_, ?_⟩
  · simp [v, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hqsum]
  · intro i j he
    exact of_not_not fun h => hsep' i j h he

theorem spectral_expression_extension (p : D → ℝ) (hp : p ∈ probabilitySimplex D) :
    p ∈ closure (simpleSpectra D) ∧
      Tendsto spectralExpression (𝓝[simpleSpectra D] p) (𝓝 (classicalSubentropy p)) := by
  refine ⟨mem_closure_simple_spectra p hp, ?_⟩
  have hd : Continuous (fun q : D → ℝ => diagonal (fun i => (q i : ℂ))) := by fun_prop
  have hc : ContinuousOn (classicalSubentropy (ι := D)) (probabilitySimplex D) :=
    continuousOn_matrixSubentropy.comp hd.continuousOn (fun _ hq => diagonal_density hq)
  have hs : simpleSpectra D ⊆ probabilitySimplex D := fun q hq => ⟨fun i => (hq.1 i).le, hq.2.1⟩
  apply ((hc p hp).mono hs).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact matrixSubentropy_diagonal_eq_distinct_formula q hq.1 hq.2.1 hq.2.2

theorem spectral_expression_at_state {A : Matrix D D ℂ} (hA : A.PosSemidef) (ht : A.trace = 1) :
    hA.isHermitian.eigenvalues ∈ closure (simpleSpectra D) ∧
      Tendsto spectralExpression (𝓝[simpleSpectra D] hA.isHermitian.eigenvalues) (𝓝 (matrixSubentropy A)) := by
  rw [subentropy_of_spectrum hA.isHermitian]
  exact spectral_expression_extension _ (spectral_prob hA ht)

end SubentropyCertificates.Representations
