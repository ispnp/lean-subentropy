module

public import D5.S3.Quantum.Subentropy.GaussianQuadratic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Monotonicity of each ordered Hermitian eigenvalue under addition of a positive
semidefinite matrix. The proof compares the two quadratic forms on a common vector. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open D5.S3.Quantum.Subentropy.GaussianQuadratic

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {A B : Matrix D D ℂ}

private abbrev indexEquiv (D : Type*) [Fintype D] : Fin (Fintype.card D) ≃ D :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

private def coord (hA : A.IsHermitian) (i : D) : EuclideanSpace ℂ D →ₗ[ℂ] ℂ :=
  (EuclideanSpace.projₗ i).comp hA.eigenvectorBasis.repr.toLinearEquiv.toLinearMap

private theorem spectral_sums (hA : A.IsHermitian) (x : EuclideanSpace ℂ D) :
    (∑ i, Complex.normSq (coord hA i x)) = ‖x‖ ^ 2 ∧
    (∑ i, hA.eigenvalues i * Complex.normSq (coord hA i x)) = 2 * gaussianQuadratic A x := by
  let z := hA.eigenvectorBasis.repr x
  have hn := hA.eigenvectorBasis.repr.norm_map x
  have h := (spectral_transport hA).1 z
  have hx : hA.eigenvectorBasis.repr.symm z = x := hA.eigenvectorBasis.repr.symm_apply_apply x
  rw [hx] at h
  refine ⟨?_, ?_⟩
  · change (∑ i, Complex.normSq (z i)) = _
    rw [← hn, EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm, z]
  · change (∑ i, hA.eigenvalues i * Complex.normSq (z i)) = _
    linarith only [h]

/-- Vanishing after index k in the eigenbasis of A and before k in that of B imposes
d-1 homogeneous linear conditions, so there is a nonzero common solution. -/
private theorem common_vector (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin (Fintype.card D)) :
    ∃ x : EuclideanSpace ℂ D, x ≠ 0 ∧
      (∀ j, k < j → coord hA (indexEquiv D j) x = 0) ∧
      (∀ j, j < k → coord hB (indexEquiv D j) x = 0) := by
  let I := (↥(Finset.Ioi k)) ⊕ (↥(Finset.Iio k))
  let f : EuclideanSpace ℂ D →ₗ[ℂ] (I → ℂ) := LinearMap.pi (fun j ↦
    Sum.elim (fun a ↦ coord hA (indexEquiv D a.val)) (fun b ↦ coord hB (indexEquiv D b.val)) j)
  have hdim : Module.finrank ℂ (I → ℂ) < Module.finrank ℂ (EuclideanSpace ℂ D) := by
    simp only [Module.finrank_pi, finrank_euclideanSpace, I, Fintype.card_sum, Fintype.card_coe,
      Fin.card_Ioi, Fin.card_Iio]
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  have hfx : f x = 0 := hx
  exact ⟨x, hx0, fun j hj ↦ congrFun hfx (Sum.inl ⟨j, Finset.mem_Ioi.mpr hj⟩),
    fun j hj ↦ congrFun hfx (Sum.inr ⟨j, Finset.mem_Iio.mpr hj⟩)⟩

/-- The ordered eigenvalues increase coordinatewise in the positive semidefinite order.
Mathlib's eigenvalues₀ uses decreasing order and includes multiplicities. -/
theorem ordered_eigenvalues_mono (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) (k : Fin (Fintype.card D)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  obtain ⟨x, hx, ha, hb⟩ := common_vector hA hB k
  let e := indexEquiv D
  have boundsA i : hA.eigenvalues₀ k * Complex.normSq (coord hA i x) ≤
      hA.eigenvalues i * Complex.normSq (coord hA i x) := by
    by_cases hi : e.symm i ≤ k
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hi) (Complex.normSq_nonneg _)
    · have hz := ha (e.symm i) (lt_of_not_ge hi)
      rw [show indexEquiv D (e.symm i) = i from e.apply_symm_apply i] at hz
      simp [hz]
  have boundsB i : hB.eigenvalues i * Complex.normSq (coord hB i x) ≤
      hB.eigenvalues₀ k * Complex.normSq (coord hB i x) := by
    by_cases hi : k ≤ e.symm i
    · exact mul_le_mul_of_nonneg_right (hB.eigenvalues₀_antitone hi) (Complex.normSq_nonneg _)
    · have hz := hb (e.symm i) (lt_of_not_ge hi)
      rw [show indexEquiv D (e.symm i) = i from e.apply_symm_apply i] at hz
      simp [hz]
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ boundsA i)
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ boundsB i)
  rw [← Finset.mul_sum, (spectral_sums hA x).1, (spectral_sums hA x).2] at hl
  rw [← Finset.mul_sum, (spectral_sums hB x).1, (spectral_sums hB x).2] at hu
  have hq := quadratic_nonnegative hAB x
  have hsub : gaussianQuadratic (B - A) x = gaussianQuadratic B x - gaussianQuadratic A x := by
    simp [gaussianQuadratic, inner_sub_right, sub_div]
  rw [hsub] at hq
  exact le_of_mul_le_mul_right (by linarith only [hl, hu, hq]) (sq_pos_of_pos (norm_pos_iff.mpr hx))

end SubentropyCertificates.SpectralContinuity
