module

public import D5.S3.Quantum.Subentropy.PinchingGap
public import Mathlib.Analysis.Convex.Jensen

/-!
# Upper bound for the pinching gap by the classical block probabilities

Supporting proof ported from The Omega Institute's trureturing,
revision d3e1e931e66ad4a3f54c95ef96cf723edcd7e792,
Subadditivity.lean, private lemma pinching_upper. This is existing upstream
work under Apache-2.0, not a newly authored result.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
namespace SubentropyCertificates
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.PinchingGap
variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

theorem pinching_gap_le_label_subentropy (G : Matrix (X × B) (X × B) ℂ)
    (hG : G.PosSemidef) (htr : G.trace = 1) (x₀ : X) (i₀ : X × B) :
    matrixSubentropy (blockPinch G) - matrixSubentropy G ≤
      matrixSubentropy (diagonal (fun x =>
        (((∑ b, G (x,b) (x,b)).re : ℝ) : ℂ))) := by
  let w := hG.isHermitian.eigenvalues
  let v : (X × B) → (X × B) → ℂ := fun j => ⇑(hG.isHermitian.eigenvectorBasis j)
  let R := fun j => Matrix.vecMulVec (v j) (star (v j))
  let r : (X × B) → X → ℝ := fun j x => ∑ b, Complex.normSq (v j (x,b))
  have hw := spectral_prob hG htr
  have hv (j : X × B) : ∑ i, star (v j i) * v j i = 1 := by
    change star (⇑(hG.isHermitian.eigenvectorBasis j)) ⬝ᵥ
      ⇑(hG.isHermitian.eigenvectorBasis j) = 1
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hG.isHermitian.eigenvectorBasis.orthonormal.1 j]
    norm_num
  have hdecomp : G = ∑ j, w j • R j := by
    ext a b
    conv_lhs => rw [hG.isHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, w, v, R]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hstates (j : X × B) : (R j).PosSemidef ∧ (R j).trace = 1 := by
    refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
    change (∑ i, v j i * star (v j i)) = 1
    simpa only [mul_comm] using hv j
  have hr (j : X × B) : (∀ x, 0 ≤ r j x) ∧ ∑ x, r j x = 1 := by
    refine ⟨fun x => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _, ?_⟩
    have hC : ((∑ x, r j x : ℝ) : ℂ) = 1 := by
      simpa only [r, Complex.ofReal_sum, Fintype.sum_prod_type,
        Complex.normSq_eq_conj_mul_self, starRingEnd_apply] using hv j
    exact_mod_cast hC
  have hD (j : X × B) :
      (diagonal (fun x => (r j x : ℂ))).PosSemidef ∧
        (diagonal (fun x => (r j x : ℂ))).trace = 1 := by
    refine ⟨Matrix.PosSemidef.diagonal (fun x => by
      simpa [Complex.le_def] using (hr j).1 x), ?_⟩
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, (hr j).2, Complex.ofReal_one]
  have hmass (x : X) : (∑ j, w j * r j x) = (∑ b, G (x,b) (x,b)).re := by
    rw [hdecomp]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul,
      R, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum, r]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hDsum : (∑ j, w j • diagonal (fun x => (r j x : ℂ))) =
      diagonal (fun x => (((∑ b, G (x,b) (x,b)).re : ℝ) : ℂ)) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
        Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sum, hmass]
    · simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hxy]
  have hc := (actual_pinching_gap_laws i₀).1.map_sum_le
    (t := Finset.univ) (w := w) (p := R)
    (fun j _ => hw.1 j) hw.2 (fun j _ => hstates j)
  have hd := ConcaveOn.le_map_sum (matrix_subentropy_concave x₀)
    (t := Finset.univ) (w := w) (p := fun j => diagonal (fun x => (r j x : ℂ)))
    (fun j _ => hw.1 j) hw.2 (fun j _ => hD j)
  change matrixSubentropy (blockPinch (∑ j, w j • R j)) -
    matrixSubentropy (∑ j, w j • R j) ≤
      ∑ j, w j * (matrixSubentropy (blockPinch (R j)) - matrixSubentropy (R j)) at hc
  rw [← hdecomp] at hc
  rw [hDsum] at hd
  calc
    _ ≤ ∑ j, w j * (matrixSubentropy (blockPinch (R j)) - matrixSubentropy (R j)) := hc
    _ = ∑ j, w j * matrixSubentropy (diagonal (fun x => (r j x : ℂ))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [(pure_block_pinching (v j) (hv j)).1]
    _ ≤ _ := hd

end SubentropyCertificates
