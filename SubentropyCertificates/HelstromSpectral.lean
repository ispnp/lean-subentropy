module

public import SubentropyCertificates.BinaryBasisGuessing

/-! The positive spectral projector of a finite Hermitian matrix maximizes
the trace pairing over all effects. A second-moment estimate will be sharp
for the difference of two prior-weighted pure states. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace SubentropyCertificates.Helstrom
variable {D : Type*} [Fintype D] [DecidableEq D]

private def spectralMatrix (U : Matrix.unitaryGroup D ℂ) (f : D → ℝ) : Matrix D D ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (diagonal (fun i => (f i : ℂ)))

private theorem spectral_mul (U : Matrix.unitaryGroup D ℂ) (f g : D → ℝ) :
    spectralMatrix U f * spectralMatrix U g = spectralMatrix U (fun i => f i*g i) := by
  simp only [spectralMatrix, ← map_mul, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

private theorem spectral_sub (U : Matrix.unitaryGroup D ℂ) (f g : D → ℝ) :
    spectralMatrix U f - spectralMatrix U g = spectralMatrix U (fun i => f i-g i) := by
  simp only [spectralMatrix, ← map_sub, ← Matrix.diagonal_sub, Complex.ofReal_sub]

private theorem spectral_one (U : Matrix.unitaryGroup D ℂ) :
    spectralMatrix U (fun _ => 1) = 1 := by
  change Unitary.conjStarAlgAut ℂ _ U (diagonal (fun _ => ((1:ℝ):ℂ))) = 1
  simp

private theorem spectral_pos (U : Matrix.unitaryGroup D ℂ) (f : D → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (spectralMatrix U f).PosSemidef := by
  have hd : (diagonal (fun i => (f i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by simpa [Complex.le_def] using hf i)
  exact hd.mul_mul_conjTranspose_same (U : Matrix D D ℂ)

private theorem spectral_trace (U : Matrix.unitaryGroup D ℂ) (f : D → ℝ) :
    (spectralMatrix U f).trace.re = ∑ i, f i := by
  change (((U : Matrix D D ℂ) * diagonal (fun i => (f i : ℂ))) *
    (U : Matrix D D ℂ).conjTranspose).trace.re = _
  have hu : (U : Matrix D D ℂ).conjTranspose * U = 1 := Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul,
    Matrix.trace_diagonal, ← Complex.ofReal_sum, Complex.ofReal_re]

omit [DecidableEq D] in
private theorem abs_sum_sq (f : D → ℝ) :
    2*(∑ i, f i^2) ≤ (∑ i, |f i|)^2 + (∑ i, f i)^2 := by
  have term (i j : D) : 0 ≤ |f i| * |f j| + f i*f j := by
    rw [← abs_mul]; linarith [neg_abs_le (f i*f j)]
  have row (i : D) : 2*f i^2 ≤ ∑ j, (|f i| * |f j| + f i*f j) := by
    have h := Finset.single_le_sum (s := Finset.univ) (fun j _ => term i j) (Finset.mem_univ i)
    simpa only [← sq,sq_abs,two_mul] using h
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => row i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← sq] using h

/-- A projective binary test attaining the positive spectral part, together
with the variational upper bound for every competing effect. Zero eigenvalues
may be assigned to either outcome; this construction assigns them to E. -/
theorem spectral_test {H : Matrix D D ℂ} (hH : H.IsHermitian) :
    ∃ E : Matrix D D ℂ, E.PosSemidef ∧ (1-E).PosSemidef ∧ E*E=E ∧
      2*(E*H).trace.re-H.trace.re = ∑ i, |hH.eigenvalues i| ∧
      ∀ F : Matrix D D ℂ, F.PosSemidef → (1-F).PosSemidef →
        (F*H).trace.re ≤ (E*H).trace.re := by
  let U := hH.eigenvectorUnitary
  let w := hH.eigenvalues
  let k (i : D) : ℝ := if 0 ≤ w i then 1 else 0
  let a i := k i*w i
  let b i := a i-w i
  let E := spectralMatrix U k
  let A := spectralMatrix U a
  let B := spectralMatrix U b
  have hd : H = spectralMatrix U w := hH.spectral_theorem
  have ha : A.PosSemidef := spectral_pos U a (fun i => by dsimp [a,k]; split_ifs <;> simp_all)
  have hb : B.PosSemidef := spectral_pos U b (fun i => by
    dsimp [b,a,k]; split_ifs <;> simp_all
    linarith)
  have hab : H = A-B := by
    rw [show A-B = _ from spectral_sub U a b]
    convert hd using 2
    funext i
    dsimp [b]
    ring
  have heh : E*H = A := by rw [hd]; exact spectral_mul U k w
  refine ⟨E, spectral_pos U k (fun i => by dsimp [k]; split_ifs <;> norm_num), ?_, ?_, ?_, ?_⟩
  · rw [← spectral_one U, show spectralMatrix U (fun _ => 1) - E = _ from spectral_sub U _ k]
    exact spectral_pos U _ (fun i => by dsimp [k]; split_ifs <;> norm_num)
  · change spectralMatrix U k * spectralMatrix U k = spectralMatrix U k
    rw [spectral_mul]
    apply congrArg (spectralMatrix U)
    funext i
    simp [k]
  · rw [heh, show A.trace.re = _ from spectral_trace U a, show H.trace.re = ∑ i, w i from
      (congrArg (fun M : Matrix D D ℂ => M.trace.re) hd).trans (spectral_trace U w),
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change 2*(k i*w i)-w i=|w i|
    by_cases hi : 0 ≤ w i
    · rw [abs_of_nonneg hi]; simp [k,hi]; ring
    · rw [abs_of_neg (lt_of_not_ge hi)]; simp [k,hi]
  · intro F hF hC
    have h₁ : 0 ≤ (F*B).trace.re := RHLinalg.trace_mul_nonneg_of_posSemidef hF hb
    have h₂ : 0 ≤ ((1-F)*A).trace.re := RHLinalg.trace_mul_nonneg_of_posSemidef hC ha
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re] at h₂
    rw [heh,hab,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]
    linarith

/-- A lower bound on the square of the Hermitian trace norm. -/
theorem spectral_second_moment {H : Matrix D D ℂ} (hH : H.IsHermitian) :
    2*(H*H).trace.re ≤ (∑ i, |hH.eigenvalues i|)^2 + H.trace.re^2 := by
  let U := hH.eigenvectorUnitary
  let w := hH.eigenvalues
  have hd : H = spectralMatrix U w := hH.spectral_theorem
  have ht : H.trace.re = ∑ i, w i :=
    (congrArg (fun M : Matrix D D ℂ => M.trace.re) hd).trans (spectral_trace U w)
  have hsq : (H*H).trace.re = ∑ i, w i ^ 2 := by
    rw [hd,spectral_mul,spectral_trace]
    simp only [sq]
  rw [ht,hsq]
  exact abs_sum_sq w

end SubentropyCertificates.Helstrom
