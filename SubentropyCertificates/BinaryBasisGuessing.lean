module

public import SubentropyCertificates.CounterexampleState
public import D5.S3.Quantum.Subentropy.GuessingProbability

/-! A binary discrimination problem whose difference of density matrices
is supported on two computational basis vectors. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped ComplexOrder MatrixOrder BigOperators
namespace SubentropyCertificates.QuantumCounterexample
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.GuessingProbability

variable {D : Type*} [Fintype D] [DecidableEq D]
abbrev mat (ρ : DensityState D) := CStarMatrix.ofMatrix.symm ρ.1
def fair (_ : Bit) : ℝ := 1/2
def basisProjector (u : D) : Matrix D D ℂ := diagonal (fun i => if i=u then 1 else 0)

/-- Read a binary function of the computational basis outcome. -/
def basisReadout (read : D → Bit) (x : Bit) : Matrix D D ℂ :=
  diagonal (fun i => if read i=x then 1 else 0)

omit [Fintype D] in
theorem basis_readout_is_povm (read : D → Bit) :
    (∀ x, (basisReadout read x).PosSemidef) ∧ ∑ x, basisReadout read x = 1 := by
  constructor
  · intro x
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases h : read i=x <;> simp [h]
  · rw [Fin.sum_univ_two]
    ext i j
    by_cases hij : i=j
    · subst j
      have cases (x : Bit) : x=0 ∨ x=1 := by fin_cases x <;> simp
      rcases cases (read i) with hx | hx <;> simp [basisReadout,hx]
    · simp [basisReadout, hij]

private theorem trace_projector (M : Matrix D D ℂ) (u : D) :
    (M * basisProjector u).trace = M u u := by
  simp [Matrix.trace, basisProjector, Matrix.mul_diagonal]

/-- For equal priors and density difference c(Pu-Pv), only two diagonal
entries of the first effect can change the success probability. -/
theorem binary_success_of_difference (ρ : Bit → DensityState D) (u v : D) (c : ℝ)
    (hd : mat (ρ 0) - mat (ρ 1) = c • (basisProjector u - basisProjector v))
    (M : Bit → Matrix D D ℂ) (hs : ∑ x, M x = 1) :
    successProbability fair ρ M =
      1/2 + c/2 * ((M 0 u u).re - (M 0 v v).re) := by
  rw [Fin.sum_univ_two] at hs
  have hm : M 1 = 1 - M 0 := by rw [← hs]; abel
  have htr : (mat (ρ 1)).trace = 1 := (ρ 1).2.2
  have h : (M 0 * mat (ρ 0)).trace + (M 1 * mat (ρ 1)).trace =
      1 + (c : ℂ)*(M 0 u u - M 0 v v) := by
    rw [hm, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, htr]
    rw [show ∀ a b : ℂ, a+(1-b)=1+(a-b) by intros; ring,
      ← Matrix.trace_sub, ← Matrix.mul_sub, hd, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub,
      trace_projector, trace_projector, Complex.real_smul]
  have hr := congrArg Complex.re h
  simp [Complex.mul_re] at hr
  unfold successProbability
  rw [Fin.sum_univ_two]
  change 1/2 * (M 0 * mat (ρ 0)).trace.re + 1/2 * (M 1 * mat (ρ 1)).trace.re = _
  linarith

/-- A computational basis readout distinguishing u and v attains the
supremum over all binary POVMs when c is nonnegative. -/
theorem basis_optimal_of_difference (ρ : Bit → DensityState D) (u v : D) (c : ℝ)
    (hc : 0 ≤ c) (hd : mat (ρ 0) - mat (ρ 1) = c • (basisProjector u - basisProjector v))
    (read : D → Bit) (hu : read u = 0) (hv : read v = 1) :
    successProbability fair ρ (basisReadout read) = 1/2+c/2 ∧ pGuess fair ρ = 1/2+c/2 := by
  obtain ⟨hpos, hsum⟩ := basis_readout_is_povm read
  have hatt : successProbability fair ρ (basisReadout read) = 1/2+c/2 := by
    rw [binary_success_of_difference ρ u v c hd _ hsum]
    simp [basisReadout, hu, hv]
  refine ⟨hatt, ?_⟩
  have hmem : 1/2+c/2 ∈ successProbabilitySet fair ρ :=
    ⟨basisReadout read,hpos,hsum,hatt.symm⟩
  have hub : ∀ r ∈ successProbabilitySet fair ρ, r ≤ 1/2+c/2 := by
    rintro _ ⟨M,hM,hs,rfl⟩
    rw [binary_success_of_difference ρ u v c hd M hs]
    have hz (x : Bit) (i : D) : 0 ≤ (M x i i).re :=
      (RCLike.nonneg_iff.mp ((hM x).diag_nonneg (i := i))).1
    rw [Fin.sum_univ_two] at hs
    have hnorm := congrArg (fun N : Matrix D D ℂ => (N u u).re) hs
    simp only [Matrix.add_apply, Complex.add_re, Matrix.one_apply_eq, Complex.one_re] at hnorm
    have hle : (M 0 u u).re - (M 0 v v).re ≤ 1 := by linarith [hz 1 u,hz 0 v]
    linarith [mul_le_mul_of_nonneg_left hle (show 0 ≤ c/2 by positivity)]
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hub) (le_csSup ⟨_,hub⟩ hmem)

end SubentropyCertificates.QuantumCounterexample
