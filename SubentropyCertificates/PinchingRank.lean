module
public import SubentropyCertificates.PinchingRatios
public import SubentropyCertificates.PinchingIntegral
public import SubentropyCertificates.PinchingGeometry
import all D5.S3.Quantum.Subentropy.EntropyJensenGap

/-! A positive pinching gain can be affine on a pure decomposition only when
all positive-weight components have the same normalized projector. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.PinchingEquality
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.PinchingGap
open D5.S3.Quantum.Subentropy.EntropyJensenGap
open D5.S3.Quantum.Subentropy.GaussianQuadratic
variable {X B I : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] [Fintype I]

private theorem coherent_coords (v : X × B → ℂ) (h : 0 < gain (projector v)) :
    ∃ i j : X × B, i.1 ≠ j.1 ∧ v i ≠ 0 ∧ v j ≠ 0 := by
  by_contra! hn
  have hfix : blockPinch (projector v) = projector v := by
    apply Matrix.ext
    intro i j
    by_cases hij : i.1 = j.1
    · simp [blockPinch, hij]
    · by_cases hi : v i = 0
      · simp [blockPinch, hij, projector, vecMulVec, hi]
      · simp [blockPinch, hij, projector, vecMulVec, hn i j hij hi]
  simp [gain, hfix] at h

theorem common_projector_of_positive_gain_equality (i₀ : X × B) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (v : I → X × B → ℂ)
    (hv : ∀ i, amplitude (v i) (v i) = 1)
    (hpos : 0 < gain (∑ i, w i • projector (v i)))
    (he : gain (∑ i, w i • projector (v i)) = ∑ i, w i * gain (projector (v i))) :
    ∃ k, 0 < w k ∧ ∀ j, 0 < w j → projector (v j) = projector (v k) := by
  classical
  have hA i : (projector (v i)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have htr i : (projector (v i)).trace = 1 := by
    change (∑ k, v i k * star (v i k)) = 1
    simpa only [amplitude, dotProduct, Pi.star_apply, mul_comm] using hv i
  obtain ⟨k, hk⟩ : ∃ k, 0 < w k * gain (projector (v k)) := by
    by_contra! h
    exact (he ▸ hpos).not_ge (Finset.sum_nonpos (fun i _ => h i))
  have hwk : 0 < w k := lt_of_le_of_ne (hw k) (fun h => by simp [← h] at hk)
  obtain ⟨a,b,hab,ha,hb⟩ := coherent_coords _ (pos_of_mul_pos_right hk (hw k))
  refine ⟨k, hwk, ?_⟩
  intro j hwj
  apply projector_eq_of_cross_block _ _ (hv k) (hv j) a b hab ha hb
  intro z s hzero hflip
  let f (i : I) (t : X → Bool) := w i * orbit (projector (v i)) (WithLp.toLp 2 z) t
  have hf i t : 0 ≤ f i t := mul_nonneg (hw i)
    (quadratic_nonnegative ((hA i).mul_mul_conjTranspose_same _) _)
  have hr := orbit_ratios_of_gap_equality f hf
    (orbit_gap_eq_of_gain_eq i₀ w hw hs (fun i => projector (v i)) hA htr he _)
  have hval i t : f i t = w i * (Complex.normSq (amplitude (signed t (v i)) z) / 2) := by
    unfold f orbit
    rw [signed_projector, quadratic_projector]
  let e : X → Bool := fun _ => false
  have heval i : f i e = w i * (Complex.normSq (amplitude (v i) z) / 2) := by
    rw [hval]
    rw [show signed e (v i) = v i by funext b; simp [signed, e, blockSign]]
  have hke : f k e = 0 := by rw [heval, hzero]; simp
  have hks : f k s ≠ 0 := by
    rw [hval]
    exact mul_ne_zero hwk.ne' (div_ne_zero (Complex.normSq_eq_zero.not.mpr hflip) (by norm_num))
  have hbk : finiteAverage (f k) ≠ 0 := by
    intro hz
    exact hks (congrFun ((average_zero_iff (f k) (hf k)).mp hz) s)
  have hr' := hr j k e
  rw [hke, zero_mul] at hr'
  have hje := (mul_eq_zero.mp hr').resolve_right hbk
  rw [heval] at hje
  by_contra hn
  exact (mul_ne_zero hwj.ne' (div_ne_zero (Complex.normSq_eq_zero.not.mpr hn) (by norm_num))) hje

theorem projector_of_positive_gain_equality (i₀ : X × B) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (v : I → X × B → ℂ)
    (hv : ∀ i, amplitude (v i) (v i) = 1)
    (hpos : 0 < gain (∑ i, w i • projector (v i)))
    (he : gain (∑ i, w i • projector (v i)) = ∑ i, w i * gain (projector (v i))) :
    ∃ u, amplitude u u = 1 ∧ (∑ i, w i • projector (v i)) = projector u := by
  obtain ⟨k, _, hall⟩ := common_projector_of_positive_gain_equality i₀ w hw hs v hv hpos he
  have hterm i : w i • projector (v i) = w i • projector (v k) := by
    by_cases hi : w i = 0
    · simp [hi]
    · rw [hall i (lt_of_le_of_ne (hw i) (Ne.symm hi))]
  refine ⟨v k, hv k, ?_⟩
  simp_rw [hterm]
  rw [← Finset.sum_smul, hs, one_smul]

theorem rank_one_of_positive_gain_equality (i₀ : X × B) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (v : I → X × B → ℂ)
    (hv : ∀ i, amplitude (v i) (v i) = 1)
    (hpos : 0 < gain (∑ i, w i • projector (v i)))
    (he : gain (∑ i, w i • projector (v i)) = ∑ i, w i * gain (projector (v i))) :
    (∑ i, w i • projector (v i)).rank = 1 := by
  obtain ⟨u, hu, heq⟩ := projector_of_positive_gain_equality i₀ w hw hs v hv hpos he
  rw [heq, projector_rank_one u hu]

end SubentropyCertificates.PinchingEquality
