module

public import SubentropyCertificates.QuadraticStatistic
public import SubentropyCertificates.QuadraticCurve
public import SubentropyCertificates.IdenticalPureSignals

/-! Pointwise sharpness of the complementary quadratic lower bound
for every prescribed attainable value of the purity difference. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators
namespace SubentropyCertificates.Quadratic
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Discrimination
variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

private theorem identical_pointer (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1) (b : B) :
    statistic p hp hs (fun _ => pointerState b) = collisionGap p := by
  let P := CStarMatrix.ofMatrix.symm (pointerState b).1
  have hid : P*P=P := by
    change (diagonal (fun j : B => if j=b then (1:ℂ) else 0)) *
      diagonal (fun j => if j=b then 1 else 0) = diagonal (fun j => if j=b then 1 else 0)
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg diagonal
    funext j
    by_cases h : j=b <;> simp [h]
  have ht : P.trace = 1 := (pointerState b).2.2
  have ho (x z : X) : overlap p (fun _ => pointerState b) x z = p x*p z := by
    change ((p x • P)*(p z • P)).trace.re = _
    simp [hid,Matrix.trace_smul,ht,Complex.real_smul,mul_comm]
  rw [statistic_eq_overlaps]
  simp only [ho]
  rw [distinct_sum (fun x z => p x*p z)]
  simp only [← Finset.mul_sum,hs,mul_one,← sq,collisionGap]

private theorem extremal_collision (m : ℕ) (e : ℝ) :
    collisionGap (extremalVector m e) = curve m e := by
  rw [curve_formula]
  simp [collisionGap,Fintype.sum_option,extremalVector,nsmul_eq_mul]
  field_simp
  ring

/-- On the same label type and signal space, identical pure signals attain
each c in the full interval, including both endpoints. -/
theorem quadratic_attainment [Nonempty B] (m : ℕ) (hn : Fintype.card X=m+2)
    (c : ℝ) (hc : c ∈ Icc 0 (radius m/2)) :
    ∃ (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1) (b : B),
      statistic p hp hs (fun _ => pointerState b) = c ∧
      1 - pGuess p (fun _ => pointerState b) = inverse m c := by
  classical
  let e := inverse m c
  obtain ⟨he,hec⟩ := inverse_spec m c hc
  rw [radius_eq] at he
  let f : X ≃ Option (Fin (m+1)) := Fintype.equivOfCardEq (by simp [hn,Nat.add_assoc])
  let w := extremalVector m e ∘ f
  have hw := simplex_reindex _ (extremal_probability_admissible m he) f
  let i := f.symm none
  have hi : w i = 1-e := by simp [w,i,extremalVector]
  have hmax (x : X) : w x ≤ w i := by
    simpa only [w,i,Function.comp_apply,Equiv.apply_symm_apply] using extremal_none_largest m he (f x)
  let b : B := Classical.arbitrary B
  refine ⟨w,hw.1,hw.2,b,?_,?_⟩
  · rw [identical_pointer]
    have hre : collisionGap w = collisionGap (extremalVector m e) := by
      unfold collisionGap
      rw [show (∑ x, w x^2) = _ from f.sum_comp (fun x => extremalVector m e x ^ 2)]
    exact hre.trans ((extremal_collision m e).trans hec)
  · rw [pGuess_identical w hw.1 hw.2 _ i hmax,hi]
    change 1-(1-e)=e
    ring

end SubentropyCertificates.Quadratic
