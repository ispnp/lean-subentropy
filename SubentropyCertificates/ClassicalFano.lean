module

public import SubentropyCertificates.ClassicalStrict

/-! Permutation averaging gives the fixed-coordinate classical extremum. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators

namespace SubentropyCertificates.ClassicalCurve

theorem simplex_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : κ → ℝ) (hp : p ∈ probabilitySimplex κ) (e : ι ≃ κ) :
    p ∘ e ∈ probabilitySimplex ι := by
  exact ⟨fun i => hp.1 (e i), (e.sum_comp p).trans hp.2⟩

def tailShift (m : ℕ) (j : Fin (m + 1)) :
    Option (Fin (m + 1)) ≃ Option (Fin (m + 1)) :=
  Equiv.optionCongr (Equiv.addRight j)

theorem average_tail_shifts (m : ℕ) (p : Option (Fin (m + 1)) → ℝ)
    (hp : p ∈ probabilitySimplex (Option (Fin (m + 1)))) :
    (∑ j : Fin (m + 1), ((m + 1 : ℕ) : ℝ)⁻¹ • (p ∘ tailShift m j)) =
      extremalVector m (1 - p none) := by
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have htail : ∑ j : Fin (m + 1), p (some j) = 1 - p none := by
    have h := hp.2
    rw [Fintype.sum_option] at h
    linarith
  funext i
  cases i with
  | none =>
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      tailShift, Equiv.optionCongr_apply, Option.map_none, extremalVector]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hm, one_mul]
    ring
  | some i =>
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      tailShift, Equiv.optionCongr_apply, Option.map_some, Equiv.coe_addRight,
      ← Finset.mul_sum, extremalVector]
    have hsum := Equiv.sum_comp (Equiv.addLeft i) (fun j => p (some j))
    simp only [Equiv.coe_addLeft] at hsum
    rw [hsum, htail]
    ring

theorem classical_coordinate_bound (m : ℕ) (p : Option (Fin (m + 1)) → ℝ)
    (hp : p ∈ probabilitySimplex (Option (Fin (m + 1)))) :
    classicalSubentropy p ≤ phi m (1 - p none) := by
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hw : ∑ _j : Fin (m + 1), ((m + 1 : ℕ) : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hm
  have h := (classical_subentropy_concave (none : Option (Fin (m + 1)))).le_map_sum
    (t := Finset.univ) (w := fun _ : Fin (m + 1) => ((m + 1 : ℕ) : ℝ)⁻¹)
    (p := fun j => p ∘ tailShift m j) (fun _ _ => by positivity) hw
    (fun j _ => simplex_reindex p hp (tailShift m j))
  rw [average_tail_shifts m p hp] at h
  simp only [classical_subentropy_reindex, smul_eq_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  simpa only [mul_inv_cancel_left₀ hm, phi] using h

theorem classical_selected_coordinate_bound (m : ℕ)
    (p : Option (Fin (m + 1)) → ℝ)
    (hp : p ∈ probabilitySimplex (Option (Fin (m + 1))))
    (i : Option (Fin (m + 1))) :
    classicalSubentropy p ≤ phi m (1 - p i) := by
  let e := Equiv.swap none i
  have h := classical_coordinate_bound m (p ∘ e) (simplex_reindex p hp e)
  simpa [classical_subentropy_reindex, e] using h

theorem classical_coordinate_bound_finite {X : Type*} [Fintype X] [DecidableEq X]
    (m : ℕ) (hn : Fintype.card X = m + 2) (p : X → ℝ)
    (hp : p ∈ probabilitySimplex X) (i : X) :
    classicalSubentropy p ≤ phi m (1 - p i) := by
  let e : Option (Fin (m + 1)) ≃ X := Fintype.equivOfCardEq (by simp [hn, Nat.add_assoc])
  have h := classical_selected_coordinate_bound m (p ∘ e)
    (simplex_reindex p hp e) (e.symm i)
  simpa [classical_subentropy_reindex] using h

theorem classical_error_range {X : Type*} [Fintype X] [DecidableEq X]
    (m : ℕ) (hn : Fintype.card X = m + 2) (p : X → ℝ)
    (hp : p ∈ probabilitySimplex X) (i : X) (hmax : ∀ j, p j ≤ p i) :
    1 - p i ∈ Icc 0 (uniformError m) := by
  have hi : p i ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ _)
  have hsum : 1 ≤ ((m + 2 : ℕ) : ℝ) * p i := by
    calc
      1 = ∑ j, p j := hp.2.symm
      _ ≤ ∑ _j : X, p i := Finset.sum_le_sum (fun j _ => hmax j)
      _ = _ := by simp [hn, nsmul_eq_mul]
  have hnR : (0 : ℝ) < (m + 2 : ℕ) := by positivity
  have hlow : 1 / ((m + 2 : ℕ) : ℝ) ≤ p i := (div_le_iff₀ hnR).mpr (by
    simpa only [mul_comm] using hsum)
  exact ⟨sub_nonneg.mpr hi, by unfold uniformError; linarith⟩

theorem classical_posterior_bound {Y : Type*} [Fintype Y] (m : ℕ)
    (q : Y → ℝ) (hq : ∀ y, 0 ≤ q y) (hs : ∑ y, q y = 1)
    (p : Y → Option (Fin (m + 1)) → ℝ)
    (hp : ∀ y, p y ∈ probabilitySimplex (Option (Fin (m + 1))))
    (selected : Y → Option (Fin (m + 1))) :
    (∑ y, q y * classicalSubentropy (p y)) ≤
      phi m (∑ y, q y * (1 - p y (selected y))) := by
  have herr (y : Y) : 1 - p y (selected y) ∈ Icc (0 : ℝ) 1 := by
    have hle : p y (selected y) ≤ 1 := by
      rw [← (hp y).2]
      exact Finset.single_le_sum (fun i _ => (hp y).1 i) (Finset.mem_univ _)
    exact ⟨sub_nonneg.mpr hle, by linarith [(hp y).1 (selected y)]⟩
  calc
    _ ≤ ∑ y, q y * phi m (1 - p y (selected y)) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (classical_selected_coordinate_bound m (p y) (hp y) (selected y)) (hq y)
    _ ≤ _ := (phi_concave m).le_map_sum (fun y _ => hq y) hs (fun y _ => herr y)

end SubentropyCertificates.ClassicalCurve
