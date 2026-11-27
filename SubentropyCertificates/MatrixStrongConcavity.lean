module
public import SubentropyCertificates.ClassicalStrongConcavity
public import SubentropyCertificates.SpectralJensen
import all SubentropyCertificates.HelstromSpectral

/-! Lemma 11. A finite mixture of arbitrary density matrices, including
singular ones. Diagonal matrices give the posterior form. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.StrongConcavity
open SubentropyCertificates.Helstrom SubentropyCertificates.Subadditivity
open SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.Basic
variable {D J : Type*} [Fintype D] [DecidableEq D] [Fintype J]

/-- Squared Hilbert–Schmidt norm, with the real part of the complex trace. -/
def hsSquared (A : Matrix D D ℂ) : ℝ := (A.conjTranspose*A).trace.re

private theorem hs_spectrum {A : Matrix D D ℂ} (H : A.IsHermitian) :
    hsSquared A = energy H.eigenvalues := by
  let U := H.eigenvectorUnitary
  let p := H.eigenvalues
  have hd : A = spectralMatrix U p := H.spectral_theorem
  change (A.conjTranspose*A).trace.re = ∑ i, p i^2
  rw [H.eq,hd,spectral_mul,spectral_trace]
  simp only [sq]

omit [DecidableEq D] in
private theorem hs_variance (w : J → ℝ) (hw : ∑ j, w j=1)
    (A : J → Matrix D D ℂ) (hA : ∀ j, (A j).IsHermitian)
    {M : Matrix D D ℂ} (hM : M.IsHermitian) (hm : M=∑ j,w j • A j) :
    ∑ j,w j*hsSquared (A j-M) = (∑ j,w j*hsSquared (A j))-hsSquared M := by
  have he : M*M=∑ j,w j • (A j*M) := by
    calc M*M = (∑ j,w j • A j)*M := congrArg (fun X : Matrix D D ℂ => X*M) hm
         _ = _ := by rw [Matrix.sum_mul]; simp only [Matrix.smul_mul]
  have hc : ∑ j,w j*(A j*M).trace.re=(M*M).trace.re := by
    simpa only [Matrix.trace_sum,Matrix.trace_smul,Complex.re_sum,Complex.smul_re,smul_eq_mul] using
      (congrArg (fun X : Matrix D D ℂ => X.trace.re) he.symm)
  have one j : w j*hsSquared (A j-M) = w j*hsSquared (A j)-2*(w j*(A j*M).trace.re)+w j*hsSquared M := by
    unfold hsSquared
    rw [((hA j).sub hM).eq,(hA j).eq,hM.eq,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,
      Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_mul_comm M (A j)]
    simp only [Complex.sub_re]; ring
  simp_rw [one]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,hw,one_mul,hc]
  simp only [hsSquared,hM.eq]; ring

/-- Lemma 11 in the Hilbert–Schmidt norm. Neither the states nor their mean
need be invertible. Zero weights are permitted. -/
theorem matrix_strong_concavity (hd : 2 ≤ Fintype.card D)
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j,w j=1)
    (A : J → Matrix D D ℂ) (hA : ∀ j,(A j).PosSemidef) (ht : ∀ j,(A j).trace=1) :
    let M := ∑ j,w j • A j
    mu (Fintype.card D)/2*(∑ j,w j*hsSquared (A j-M)) ≤
      matrixSubentropy M - ∑ j,w j*matrixSubentropy (A j) := by
  let M := ∑ j,w j • A j
  have hM : M.PosSemidef := Matrix.posSemidef_sum _ (fun j _ => (hA j).smul (hw j))
  have he {B : Matrix D D ℂ} (H : B.IsHermitian) :
      corrected H.eigenvalues = matrixSubentropy B+mu (Fintype.card D)/2*hsSquared B := by
    rw [corrected,← hs_spectrum H,subentropy_of_spectrum H]
  have h := spectral_jensen (corrected_concave hd) corrected_perm w hw hs A hA ht hM.isHermitian rfl
  simp_rw [he] at h
  have expand j : w j*(matrixSubentropy (A j)+mu (Fintype.card D)/2*hsSquared (A j)) =
      w j*matrixSubentropy (A j)+mu (Fintype.card D)/2*(w j*hsSquared (A j)) := by ring
  simp_rw [expand] at h
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at h
  change _ * (∑ j,w j*hsSquared (A j-M)) ≤ matrixSubentropy M - _
  rw [hs_variance w hs A (fun j => (hA j).isHermitian) hM.isHermitian rfl]
  linarith only [h]

/-- Diagonal specialization, in ordinary Euclidean coordinates. -/
theorem posterior_strong_concavity (hd : 2 ≤ Fintype.card D)
    (w : J → ℝ) (hw : ∀ j,0 ≤ w j) (hs : ∑ j,w j=1)
    (p : J → D → ℝ) (hp : ∀ j,p j ∈ probabilitySimplex D) :
    let m := ∑ j,w j • p j
    mu (Fintype.card D)/2*(∑ j,w j*energy (p j-m)) ≤
      classicalSubentropy m - ∑ j,w j*classicalSubentropy (p j) := by
  let m := ∑ j,w j • p j
  let diag (v : D → ℝ) := diagonal (fun i => (v i:ℂ))
  have hm : ∑ j,w j • diag (p j) = diag m := by
    ext i k
    by_cases he : i=k
    · subst k
      simp [diag,m,Matrix.sum_apply,Matrix.smul_apply,Complex.real_smul,Finset.sum_apply]
    · simp [diag,he,Matrix.sum_apply,Matrix.smul_apply]
  have hv (v : D → ℝ) : hsSquared (diag v - diag m) = energy (v-m) := by
    unfold hsSquared diag
    rw [Matrix.diagonal_sub,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal,Complex.re_sum]
    unfold energy
    apply Finset.sum_congr rfl
    intro i _
    simp [sq]
  have h := matrix_strong_concavity hd w hw hs (fun j => diag (p j))
    (fun j => (diagonal_density (hp j)).1) (fun j => (diagonal_density (hp j)).2)
  dsimp only at h
  rw [hm] at h
  simpa only [hv,diag,m,classicalSubentropy] using h

/-- In dimension one every trace-one matrix is the identity. -/
theorem variance_one_dim (hd : Fintype.card D=1) (w : J → ℝ) (hs : ∑ j,w j=1)
    (A : J → Matrix D D ℂ) (ht : ∀ j,(A j).trace=1) :
    ∑ j,w j*hsSquared (A j-∑ k,w k • A k)=0 := by
  obtain ⟨x,hx⟩ := Fintype.card_eq_one_iff.mp hd
  let _ : Unique D := ⟨⟨x⟩,hx⟩
  have one (j : J) : A j = 1 := by
    ext i k
    rw [Subsingleton.elim i default, Subsingleton.elim k default]
    simpa [Matrix.trace] using ht j
  simp only [one,← Finset.sum_smul,hs,one_smul,sub_self]
  simp [hsSquared]

end SubentropyCertificates.StrongConcavity
