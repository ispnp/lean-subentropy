module
public import SubentropyCertificates.MarginalPurity
public import Mathlib.Analysis.Convex.Birkhoff

/-! Lifting a concave symmetric function of a probability vector to a
concave function of the spectrum of a density matrix. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.StrongConcavity
open SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.DensityKernel
variable {D J : Type*} [Fintype D] [DecidableEq D] [Fintype J]

private def diagRe (A : Matrix D D ℂ) (i : D) := (A i i).re

private theorem rotated_diagonal (U : Matrix.unitaryGroup D ℂ) (p : D → ℝ) :
    ∃ w : Equiv.Perm D → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ=1 ∧
      diagRe (Unitary.conjStarAlgAut ℂ _ U (diagonal (fun i => (p i : ℂ)))) =
        ∑ σ, w σ • (p ∘ σ) := by
  classical
  let B : Matrix D D ℝ := fun i j => Complex.normSq (U i j)
  have hr (i : D) : ∑ j, B i j = 1 := by
    have h := congrArg (fun M : Matrix D D ℂ => (M i i).re) (Unitary.coe_mul_star_self U)
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,B,Complex.normSq_apply] using h
  have hc (j : D) : ∑ i, B i j = 1 := by
    have h := congrArg (fun M : Matrix D D ℂ => (M j j).re) (Unitary.coe_star_mul_self U)
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,B,Complex.normSq_apply] using h
  have hB : B ∈ doublyStochastic ℝ D :=
    mem_doublyStochastic_iff_sum.mpr ⟨fun _ _ => Complex.normSq_nonneg _,hr,hc⟩
  obtain ⟨w,hw,hs,hperm⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hB
  refine ⟨w,hw,hs,?_⟩
  calc
    _ = B *ᵥ p := by
      funext i
      change (((U : Matrix D D ℂ)*diagonal (fun j => (p j:ℂ))*(U : Matrix D D ℂ).conjTranspose) i i).re = _
      rw [Matrix.mul_apply,Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,B]
      rw [mul_right_comm,show U i j * star (U i j) = (Complex.normSq (U i j):ℂ) from Complex.mul_conj _]
      simp
    _ = _ := by rw [← hperm,Matrix.sum_mulVec]; simp only [Matrix.smul_mulVec,Matrix.permMatrix_mulVec]

private def coords (U : Matrix.unitaryGroup D ℂ) (A : Matrix D D ℂ) :=
  diagRe (Unitary.conjStarAlgAut ℂ _ (star U) A)

private theorem coords_mix (U : Matrix.unitaryGroup D ℂ) (w : J → ℝ) (A : J → Matrix D D ℂ) :
    coords U (∑ j, w j • A j) = ∑ j, w j • coords U (A j) := by
  funext i
  change (((((star U : Matrix.unitaryGroup D ℂ) : Matrix D D ℂ) * (∑ j, w j • A j)) * star (((star U : Matrix.unitaryGroup D ℂ) : Matrix D D ℂ))) i i).re = _
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.sum_apply,
    Matrix.smul_apply,Complex.re_sum,Complex.smul_re,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rfl

private theorem coords_own {A : Matrix D D ℂ} (hA : A.IsHermitian) :
    coords hA.eigenvectorUnitary A = hA.eigenvalues := by
  calc _ = coords hA.eigenvectorUnitary
        (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary (diagonal (fun i => (hA.eigenvalues i:ℂ)))) :=
          congrArg _ hA.spectral_theorem
       _ = _ := by
         funext i
         unfold coords
         have he := DFunLike.congr_fun (map_mul (Unitary.conjStarAlgAut ℂ (Matrix D D ℂ)) (star hA.eigenvectorUnitary) hA.eigenvectorUnitary) (diagonal (fun i => (hA.eigenvalues i:ℂ)))
         change diagRe (((Unitary.conjStarAlgAut ℂ _) (star hA.eigenvectorUnitary) * (Unitary.conjStarAlgAut ℂ _) hA.eigenvectorUnitary) _) i = _
         rw [← he]; simp [diagRe]

private theorem coords_bounds {f : (D → ℝ) → ℝ} (hf : ConcaveOn ℝ (probabilitySimplex D) f)
    (hsym : ∀ p : D → ℝ, ∀ σ : Equiv.Perm D, f (p ∘ σ) = f p)
    (U : Matrix.unitaryGroup D ℂ) {A : Matrix D D ℂ} (hA : A.PosSemidef) (ht : A.trace = 1) :
    coords U A ∈ probabilitySimplex D ∧ f hA.isHermitian.eigenvalues ≤ f (coords U A) := by
  let H := hA.isHermitian
  let V := H.eigenvectorUnitary
  let p := H.eigenvalues
  have hp : p ∈ probabilitySimplex D := spectral_prob hA ht
  have hc : coords U A = diagRe (Unitary.conjStarAlgAut ℂ _ (star U*V)
      (diagonal (fun i => (p i:ℂ)))) := by
    unfold coords
    rw [show A = Unitary.conjStarAlgAut ℂ _ V (diagonal (fun i => (p i:ℂ))) from H.spectral_theorem]
    rw [map_mul]; rfl
  obtain ⟨w,hw,hs,he⟩ := rotated_diagonal (star U*V) p
  have hdom (σ : Equiv.Perm D) : p ∘ σ ∈ probabilitySimplex D :=
    ⟨fun i => hp.1 _,(Equiv.sum_comp σ p).trans hp.2⟩
  rw [hc,he]
  refine ⟨hf.1.sum_mem (fun σ _ => hw σ) hs (fun σ _ => hdom σ),?_⟩
  have h := hf.le_map_sum (t := Finset.univ) (w := w) (p := fun σ => p ∘ σ) (fun σ _ => hw σ)
    hs (fun σ _ => hdom σ)
  simpa only [hsym,smul_eq_mul,← Finset.sum_mul,hs,one_mul] using h

theorem spectral_jensen {f : (D → ℝ) → ℝ} (hf : ConcaveOn ℝ (probabilitySimplex D) f)
    (hsym : ∀ p : D → ℝ, ∀ σ : Equiv.Perm D, f (p ∘ σ) = f p)
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j=1)
    (A : J → Matrix D D ℂ) (hA : ∀ j, (A j).PosSemidef) (ht : ∀ j, (A j).trace=1)
    {M : Matrix D D ℂ} (hM : M.IsHermitian) (hm : M = ∑ j, w j • A j) :
    ∑ j, w j*f (hA j).isHermitian.eigenvalues ≤ f hM.eigenvalues := by
  let U := hM.eigenvectorUnitary
  have hg j := coords_bounds hf hsym U (hA j) (ht j)
  have he : ∑ j, w j • coords U (A j) = hM.eigenvalues := by
    rw [← coords_mix,← hm]; exact coords_own hM
  calc _ ≤ ∑ j, w j*f (coords U (A j)) := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hg j).2 (hw j)
       _ ≤ _ := by
          have h := hf.le_map_sum (t := Finset.univ) (w := w) (p := fun j => coords U (A j))
            (fun j _ => hw j) hs (fun j _ => (hg j).1)
          simpa only [he,smul_eq_mul] using h

end SubentropyCertificates.StrongConcavity
