module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Instances.Matrix

/-! Order and continuity of the resolvent factor in the spatial sign covariance integral. -/
@[expose] public section
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SubentropyCertificates.ConditionalContinuity

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The matrix factor M(I+tM)⁻¹. -/
def signResolvent (M : Matrix D D ℂ) (t : ℝ) := M * (1 + t • M)⁻¹

omit [Fintype D] in
theorem shifted_posDef {M : Matrix D D ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t • M).PosDef := Matrix.PosDef.one.add_posSemidef (hM.smul ht)

private theorem inverse_antitone {A B : Matrix D D ℂ} (ha : A.PosDef) (hb : B.PosDef)
    (hab : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  have h := CStarAlgebra.inv_le_inv (a := ha.isUnit.unit) (b := hb.isUnit.unit)
    (by simpa only [IsUnit.unit_spec] using ha.posSemidef.nonneg)
    (by simpa only [IsUnit.unit_spec] using hab)
  simpa only [Matrix.coe_units_inv, IsUnit.unit_spec] using h

theorem signResolvent_eq {M : Matrix D D ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 < t) :
    signResolvent M t = t⁻¹ • (1 - (1 + t • M)⁻¹) := by
  have hi := Matrix.mul_nonsing_inv (1 + t • M)
    ((Matrix.isUnit_iff_isUnit_det _).mp (shifted_posDef hM ht.le).isUnit)
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at hi
  have hh : t • signResolvent M t = 1 - (1 + t • M)⁻¹ := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hi
  rw [← hh, inv_smul_smul₀ ht.ne']

/-- The resolvent is operator monotone on positive semidefinite matrices for t ≥ 0. -/
theorem signResolvent_mono {A B : Matrix D D ℂ} (ha : A.PosSemidef) (hb : B.PosSemidef)
    (hab : A ≤ B) {t : ℝ} (ht : 0 ≤ t) : signResolvent A t ≤ signResolvent B t := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa [signResolvent] using hab
  rw [signResolvent_eq ha ht, signResolvent_eq hb ht]
  apply smul_le_smul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
  apply sub_le_sub_left
  exact inverse_antitone (shifted_posDef ha ht.le) (shifted_posDef hb ht.le)
    (add_le_add_right (smul_le_smul_of_nonneg_left hab ht.le) 1)

/-- The resolvent is positive, and at positive parameters is bounded above by I/t. -/
theorem signResolvent_bounds {M : Matrix D D ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 < t) :
    0 ≤ signResolvent M t ∧ signResolvent M t ≤ t⁻¹ • 1 := by
  refine ⟨?_, ?_⟩
  · simpa [signResolvent] using signResolvent_mono Matrix.PosSemidef.zero hM hM.nonneg ht.le
  · rw [signResolvent_eq hM ht]
    exact smul_le_smul_of_nonneg_left
      (sub_le_self _ (shifted_posDef hM ht.le).inv.posSemidef.nonneg) (inv_nonneg.mpr ht.le)

theorem signResolvent_continuousAt {M : Matrix D D ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (signResolvent M) t := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (shifted_posDef hM ht).isUnit
  apply continuousAt_const.mul
  apply (continuousAt_matrix_inv _ ?_).comp
  · fun_prop
  · simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet.ne_zero

end SubentropyCertificates.ConditionalContinuity
