module

public import SubentropyCertificates.GuessingAttainment
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Projective discrimination of mutually orthogonal signal supports.
The unused orthogonal complement is assigned to one label. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.ZeroConditional
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.Discrimination

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

/-- In finite dimension the support of a density operator is its range. -/
def signalSupport (σ : DensityState B) : Submodule ℂ (EuclideanSpace ℂ B) :=
  LinearMap.range (CStarMatrix.ofMatrix.symm σ.1).toEuclideanLin

def orthogonalSupports (p : X → ℝ) (ρ : X → DensityState B) : Prop :=
  ∀ x y, x ≠ y → 0 < p x → 0 < p y → signalSupport (ρ x) ⟂ signalSupport (ρ y)

private def projection (K : Submodule ℂ (EuclideanSpace ℂ B)) : Matrix B B ℂ :=
  Matrix.toEuclideanLin.symm K.starProjection.toLinearMap

private theorem projection_lin (K : Submodule ℂ (EuclideanSpace ℂ B)) :
    (projection K).toEuclideanLin = K.starProjection.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

private theorem projection_star (K : Submodule ℂ (EuclideanSpace ℂ B)) :
    IsStarProjection (projection K) := by
  refine ⟨?_, Matrix.isHermitian_iff_isSelfAdjoint.mp
    (Matrix.isSymmetric_toEuclideanLin_iff.mp (by rw [projection_lin]; exact K.starProjection_isSymmetric))⟩
  change projection K * projection K = projection K
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, projection_lin]
  exact congrArg ContinuousLinearMap.toLinearMap K.isIdempotentElem_starProjection

/-- Given pairwise orthogonal subspaces, a labelled projective measurement can
fix every vector in its own subspace, even if their span is proper. -/
theorem projective_measurement_of_orthogonal_subspaces (i : X)
    (K : X → Submodule ℂ (EuclideanSpace ℂ B)) (hK : Pairwise (fun x y => K x ⟂ K y)) :
    ∃ M : X → Matrix B B ℂ, (∀ x, IsStarProjection (M x)) ∧ ∑ x, M x = 1 ∧
      ∀ x v, v ∈ K x → (M x).toEuclideanLin v = v := by
  classical
  let P (x : X) := projection (K x)
  let T := Finset.univ.erase i
  let S := ∑ x ∈ T, P x
  have hoff {x y : X} (hxy : x ≠ y) : P x * P y = 0 := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, map_zero, projection_lin, projection_lin]
    exact congrArg ContinuousLinearMap.toLinearMap ((hK hxy).starProjection_comp_starProjection)
  have hS : IsStarProjection S := by
    refine ⟨?_, isSelfAdjoint_sum _ (fun x _ => (projection_star (K x)).isSelfAdjoint)⟩
    change S * S = S
    dsimp only [S]
    rw [Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Matrix.mul_sum, Finset.sum_eq_single_of_mem x hx (fun y _ hy => hoff hy.symm)]
    exact (projection_star (K x)).isIdempotentElem
  let M (x : X) := if x = i then 1 - S else P x
  refine ⟨M, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = i
    · simpa only [M, ite_eq_left hx] using hS.one_sub
    · simpa only [M, ite_eq_right hx] using projection_star (K x)
  · rw [← Finset.sum_erase_add _ M (Finset.mem_univ i)]
    have hsum : ∑ x ∈ T, M x = S := Finset.sum_congr rfl (fun x hx =>
      ite_eq_right (Finset.mem_erase.mp hx).1)
    change (∑ x ∈ T, M x) + M i = 1
    rw [hsum]
    simp [M]
  · intro x v hv
    by_cases hx : x = i
    · subst x
      have hz : S.toEuclideanLin v = 0 := by
        change Matrix.toEuclideanLin (∑ x ∈ T, P x) v = 0
        rw [map_sum, LinearMap.sum_apply]
        apply Finset.sum_eq_zero
        intro x hx
        rw [projection_lin]
        exact (Submodule.starProjection_apply_eq_zero_iff (K := K x)).mpr
          ((hK (Finset.mem_erase.mp hx).1.symm) hv)
      simp [M, map_sub, Matrix.toLpLin_one, hz]
    · change Matrix.toEuclideanLin (if x = i then 1 - S else P x) v = v
      rw [ite_eq_right hx, projection_lin]
      exact Submodule.starProjection_eq_self_iff.mpr hv

/-- Zero-prior signals are unrestricted. The measurement is projective and
its actual success probability equals one. -/
theorem perfect_projective_measurement_of_orthogonal_supports
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (ρ : X → DensityState B)
    (ho : orthogonalSupports p ρ) :
    ∃ M : X → Matrix B B ℂ, (∀ x, IsStarProjection (M x)) ∧ ∑ x, M x = 1 ∧
      successProbability p ρ M = 1 := by
  classical
  have hX : Nonempty X := by
    by_contra h
    have : IsEmpty X := not_nonempty_iff.mp h
    simp at hs
  let K (x : X) := if 0 < p x then signalSupport (ρ x) else ⊥
  have hK : Pairwise (fun x y => K x ⟂ K y) := by
    intro x y hxy
    by_cases hx : 0 < p x <;> by_cases hy : 0 < p y <;> simp [K, hx, hy, ho x y hxy]
  obtain ⟨M, hM, hsM, hfix⟩ := projective_measurement_of_orthogonal_subspaces
    (Classical.choice hX) K hK
  refine ⟨M, hM, hsM, ?_⟩
  unfold successProbability
  rw [← hs]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 < p x
  · let A := CStarMatrix.ofMatrix.symm (ρ x).1
    have hMA : M x * A = A := by
      apply Matrix.toEuclideanLin.injective
      rw [Matrix.toLpLin_mul_same]
      apply LinearMap.ext
      intro v
      apply hfix x
      rw [show K x = signalSupport (ρ x) from ite_eq_left hx]
      exact ⟨v, rfl⟩
    change p x * (M x * A).trace.re = p x
    rw [hMA, show A.trace = 1 from (ρ x).2.2]
    simp
  · simp [le_antisymm (le_of_not_gt hx) (hp x)]

end SubentropyCertificates.ZeroConditional
