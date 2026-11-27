module

public import SubentropyCertificates.MatrixStrongConcavity
public import SubentropyCertificates.MarginalPurity

/-! An interior mixture of two distinct density matrices has rank at least two. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.ConditionalContinuity
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel
open SubentropyCertificates.Subadditivity
open SubentropyCertificates.QuantumEquality
open SubentropyCertificates.StrongConcavity

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
private theorem hsSquared_nonneg_eq_zero (T : Matrix D D ℂ) :
    0 ≤ hsSquared T ∧ (hsSquared T = 0 → T = 0) := by
  have h := Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self T).trace_nonneg
  exact ⟨h.1, fun hz ↦ trace_conjTranspose_mul_self_eq_zero_iff.mp
    (Complex.ext hz h.2.symm)⟩

/-- Strong concavity makes the subentropy of an interior mixture of two distinct
normalized marginals positive. A rank-one state would have zero subentropy. -/
theorem segment_rank_gt_one_of_ne (M N : Matrix D D ℂ) (hm : M.PosSemidef) (hn : N.PosSemidef)
    (htm : M.trace = 1) (htn : N.trace = 1) (hne : M ≠ N) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    1 < ((1-s) • M + s • N).rank := by
  let C := (1-s) • M + s • N
  have hs₀ := hs.1
  have hs₁ : 0 < 1-s := sub_pos.mpr hs.2
  have hC : C.PosSemidef := (hm.smul hs₁.le).add (hn.smul hs₀.le)
  have htC : C.trace = 1 := by simp [C, trace_add, trace_smul, htm, htn, Complex.real_smul]
  have hd : 2 ≤ Fintype.card D := by
    by_contra! hc
    have : Subsingleton D := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have entry (P : Matrix D D ℂ) (ht : P.trace = 1) (i : D) : P i i = 1 := by
      change ∑ j, P j j = 1 at ht
      rwa [Finset.sum_eq_single i (fun j _ hj ↦ (hj (Subsingleton.elim j i)).elim)
        (fun h ↦ (h (Finset.mem_univ i)).elim)] at ht
    apply hne
    ext i j
    rw [Subsingleton.elim j i, entry M htm, entry N htn]
  have hQ (P : Matrix D D ℂ) (hp : P.PosSemidef) (ht : P.trace = 1) :
      0 ≤ matrixSubentropy P := by
    rw [subentropy_of_spectrum hp.isHermitian]
    exact classical_subentropy_nonneg _ (spectral_prob hp ht)
  have hc := matrix_strong_concavity hd ![1-s, s]
    (by intro i; fin_cases i <;> simp [hs₀.le, hs₁.le])
    (by simp [Fin.sum_univ_two]) ![M, N]
    (by intro i; fin_cases i <;> simp [hm, hn])
    (by intro i; fin_cases i <;> simp [htm, htn])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  change mu (Fintype.card D) / 2 * ((1-s)*hsSquared (M-C) + s*hsSquared (N-C)) ≤
    matrixSubentropy C - ((1-s)*matrixSubentropy M + s*matrixSubentropy N) at hc
  have hv : 0 < (1-s)*hsSquared (M-C) + s*hsSquared (N-C) := by
    have ha := hsSquared_nonneg_eq_zero (M-C)
    have hb := hsSquared_nonneg_eq_zero (N-C)
    by_contra! hz
    have hleft := (mul_nonneg hs₁.le ha.1).antisymm'
      (by linarith [mul_nonneg hs₀.le hb.1] : (1-s)*hsSquared (M-C) ≤ 0)
    have hright := (mul_nonneg hs₀.le hb.1).antisymm'
      (by linarith [mul_nonneg hs₁.le ha.1] : s*hsSquared (N-C) ≤ 0)
    exact hne ((sub_eq_zero.mp (ha.2 ((mul_eq_zero.mp hleft).resolve_left hs₁.ne'))).trans
      (sub_eq_zero.mp (hb.2 ((mul_eq_zero.mp hright).resolve_left hs₀.ne'))).symm)
  have hmupos : 0 < mu (Fintype.card D)/2 := by linarith [mu_ge_third hd]
  have hpos : 0 < matrixSubentropy C := by
    linarith [mul_pos hmupos hv, mul_nonneg hs₁.le (hQ M hm htm), mul_nonneg hs₀.le (hQ N hn htn)]
  have hnotone := mt (matrixSubentropy_zero_iff_rank_one hC htC).mpr hpos.ne'
  have hp : 0 < C.rank := by
    rw [hC.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_pos_iff]
    by_contra! he
    have hz : hC.isHermitian.eigenvalues = 0 := funext fun i ↦ by
      by_contra hi
      exact he.false ⟨i, hi⟩
    have hz' := hC.isHermitian.eigenvalues_eq_zero_iff.mp hz
    simp [hz'] at htC
  change 1 < C.rank
  omega

end SubentropyCertificates.ConditionalContinuity
