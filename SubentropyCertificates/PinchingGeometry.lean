module
public import D5.S3.Quantum.Subentropy.PinchingGap
public import Mathlib.LinearAlgebra.Matrix.Rank
import all D5.S3.Quantum.Subentropy.PinchingGap

/-! Linear algebra for the equality case. Two coordinates in different blocks
give a test vector annihilated by one amplitude but not by its sign flip.
Translation by this vector recovers the entire kernel. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.PinchingEquality
open D5.S3.Quantum.Subentropy.GaussianQuadratic
open D5.S3.Quantum.Subentropy.PinchingGap
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram

variable {D X B : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X]
  [Fintype B] [DecidableEq B]

def projector (v : D → ℂ) := vecMulVec v (star v)
def amplitude (v z : D → ℂ) := star v ⬝ᵥ z
def signed (s : X → Bool) (v : X × B → ℂ) := fun k => blockSign s k.1 * v k

theorem quadratic_projector (v z : D → ℂ) :
    gaussianQuadratic (projector v) (WithLp.toLp 2 z) = Complex.normSq (amplitude v z) / 2 := by
  have hact : projector v *ᵥ z = amplitude v z • v := by
    funext i
    simp only [projector, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, amplitude,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hstar : v ⬝ᵥ star z = star (amplitude v z) := by
    simp [amplitude, dotProduct, star_sum, mul_comm]
  change ((projector v *ᵥ z) ⬝ᵥ star z).re / 2 = _
  rw [hact, smul_dotProduct, smul_eq_mul, hstar, Complex.star_def, Complex.mul_conj]
  rfl

theorem signed_projector (s : X → Bool) (v : X × B → ℂ) :
    signUnitary s * projector v * (signUnitary s).conjTranspose = projector (signed s v) := by
  apply Matrix.ext
  intro i j
  rw [sign_conjugate_entries]
  cases hi : s i.1 <;> cases hj : s j.1 <;>
    simp [signed, projector, vecMulVec, blockSign, hi, hj]

theorem projector_eq_of_cross_block (v u : X × B → ℂ)
    (hv : amplitude v v = 1) (hu : amplitude u u = 1)
    (i j : X × B) (hij : i.1 ≠ j.1) (hi : v i ≠ 0) (hj : v j ≠ 0)
    (hker : ∀ z s, amplitude v z = 0 → amplitude (signed s v) z ≠ 0 → amplitude u z = 0) :
    projector u = projector v := by
  let s : X → Bool := fun x => decide (x = i.1)
  let d : X × B → ℂ := Pi.single i (star (v i))⁻¹ - Pi.single j (star (v j))⁻¹
  have hvi : (starRingEnd ℂ) (v i) ≠ 0 := by simpa using hi
  have hvj : (starRingEnd ℂ) (v j) ≠ 0 := by simpa using hj
  have hd : amplitude v d = 0 := by
    simp [d, amplitude, dotProduct_sub, dotProduct_single, hvi, hvj]
  have hds : amplitude (signed s v) d ≠ 0 := by
    simp [d, amplitude, dotProduct_sub, dotProduct_single, signed, s, blockSign, hij.symm,
      hvi, hvj]
    norm_num
  have hud := hker d s hd hds
  have hle (z : X × B → ℂ) (hz : amplitude v z = 0) : amplitude u z = 0 := by
    by_cases hsz : amplitude (signed s v) z = 0
    · have hsum := hker (z + d) s (by
          rw [amplitude, dotProduct_add]
          change amplitude v z + amplitude v d = 0
          rw [hz, hd, add_zero])
        (by simp only [amplitude, dotProduct_add] at hsz hds ⊢; rwa [hsz, zero_add])
      change _ ⬝ᵥ (z + d) = 0 at hsum
      rw [dotProduct_add] at hsum
      change amplitude u z + amplitude u d = 0 at hsum
      rwa [hud, add_zero] at hsum
    · exact hker z s hz hsz
  let c := amplitude u v
  have heval (z : X × B → ℂ) : amplitude u z = amplitude v z * c := by
    have hk : amplitude v (z - amplitude v z • v) = 0 := by
      rw [amplitude, dotProduct_sub, dotProduct_smul]
      change amplitude v z - amplitude v z * amplitude v v = 0
      rw [hv, mul_one, sub_self]
    have hu' := hle _ hk
    rw [amplitude, dotProduct_sub, dotProduct_smul] at hu'
    exact sub_eq_zero.mp hu'
  have coeff (k : X × B) : star (u k) = star (v k) * c := by
    simpa [amplitude, dotProduct_single] using heval (Pi.single k 1)
  have coeff' (k : X × B) : u k = star c * v k := by
    simpa [mul_comm] using congrArg star (coeff k)
  have hnorm : star c * c = 1 := by
    have huu := heval u
    have huv : amplitude v u = star c := by
      have he : u = star c • v := funext coeff'
      rw [he, amplitude, dotProduct_smul]
      change star c * amplitude v v = star c
      rw [hv, mul_one]
    rw [hu, huv] at huu
    exact huu.symm
  apply Matrix.ext
  intro k l
  change u k * star (u l) = v k * star (v l)
  rw [coeff' k, coeff l]
  calc
    _ = (star c * c) * (v k * star (v l)) := by ring
    _ = _ := by rw [hnorm, one_mul]

omit [DecidableEq D] in
theorem projector_rank_one (v : D → ℂ) (hv : amplitude v v = 1) :
    (projector v).rank = 1 := by
  let V : Matrix D Unit ℂ := fun i _ => v i
  have hleft : V.conjTranspose * V = 1 := by
    ext i j
    change amplitude v v = (1 : Matrix Unit Unit ℂ) i j
    simpa using hv
  have hright : V * V.conjTranspose = projector v := by
    ext i j
    change (∑ _k : Unit, v i * star (v j)) = _
    simp [projector, vecMulVec]
  rw [← hright, Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self V,
    hleft, Matrix.rank_one, Fintype.card_unit]

end SubentropyCertificates.PinchingEquality
