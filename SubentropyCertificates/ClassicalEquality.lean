module

public import SubentropyCertificates.ClassicalFano

/-!
# Equality on the classical subentropy error curve

The first equality is strict Jensen applied to the cyclic permutations already
used in the fixed-coordinate bound. The second is strict Jensen for the
outcome errors. The selected label may depend on the outcome. Selecting any
maximizer gives the MAP statement, including ties.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators

namespace SubentropyCertificates.ClassicalCurve

theorem classical_coordinate_eq_iff_extremal (m : ℕ) (p : Option (Fin (m + 1)) → ℝ)
    (hp : p ∈ probabilitySimplex (Option (Fin (m + 1)))) :
    classicalSubentropy p = phi m (1 - p none) ↔ p = extremalVector m (1 - p none) := by
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hw : ∑ _j : Fin (m + 1), ((m + 1 : ℕ) : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hm
  have h := classical_subentropy_strictConcave.map_sum_eq_iff
    (t := Finset.univ) (w := fun _ : Fin (m + 1) => ((m + 1 : ℕ) : ℝ)⁻¹)
    (p := fun j => p ∘ tailShift m j) (fun _ _ => by positivity) hw
    (fun j _ => simplex_reindex p hp (tailShift m j))
  rw [average_tail_shifts m p hp] at h
  simp only [classical_subentropy_reindex, smul_eq_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel_left₀ hm] at h
  constructor
  · intro he
    have h0 := h.mp he.symm 0 (Finset.mem_univ _)
    calc
      p = p ∘ tailShift m 0 := by
        funext x
        cases x <;> simp [tailShift]
      _ = _ := h0
  · exact fun he => congrArg classicalSubentropy he

/-- The other coordinates must each carry exactly their share of the error. -/
theorem classical_coordinate_eq_iff {X : Type*} [Fintype X] [DecidableEq X]
    (m : ℕ) (hn : Fintype.card X = m + 2) (p : X → ℝ)
    (hp : p ∈ probabilitySimplex X) (i : X) :
    classicalSubentropy p = phi m (1 - p i) ↔
      ∀ j, j ≠ i → p j = (1 - p i) / (m + 1 : ℕ) := by
  let a : Option (Fin (m + 1)) ≃ X := Fintype.equivOfCardEq (by simp [hn, Nat.add_assoc])
  let e := a.trans (Equiv.swap (a none) i)
  have hi : e none = i := by simp [e]
  have he : classicalSubentropy p = phi m (1 - p i) ↔
      p ∘ e = extremalVector m (1 - p i) := by
    simpa only [classical_subentropy_reindex, Function.comp_apply, hi] using
      classical_coordinate_eq_iff_extremal m (p ∘ e) (simplex_reindex p hp e)
  rw [he]
  constructor
  · intro h j hj
    obtain ⟨k, rfl⟩ := e.surjective j
    cases k with
    | none => exact (hj hi).elim
    | some k => exact congrFun h (some k)
  · intro h
    funext k
    cases k with
    | none => simp [hi, extremalVector]
    | some k =>
      exact h _ (fun heq => Option.some_ne_none k (e.injective (heq.trans hi.symm)))

/-- Equal unselected coordinates suffice, since their sum is fixed. -/
theorem classical_coordinate_eq_iff_equal_tail {X : Type*} [Fintype X] [DecidableEq X]
    (m : ℕ) (hn : Fintype.card X = m + 2) (p : X → ℝ)
    (hp : p ∈ probabilitySimplex X) (i : X) :
    classicalSubentropy p = phi m (1 - p i) ↔
      ∀ j, j ≠ i → ∀ k, k ≠ i → p j = p k := by
  rw [classical_coordinate_eq_iff m hn p hp i]
  constructor
  · exact fun h j hj k hk => (h j hj).trans (h k hk).symm
  · intro h j hj
    have hsum := Finset.sum_erase_add Finset.univ p (Finset.mem_univ i)
    have hconst : ∑ k ∈ Finset.univ.erase i, p k = ∑ _k ∈ Finset.univ.erase i, p j :=
      Finset.sum_congr rfl (fun k hk => h k (Finset.mem_erase.mp hk).1 j hj)
    have hcard : (Finset.univ.erase i).card = m + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hn]
      omega
    rw [hp.2, hconst, Finset.sum_const, hcard, nsmul_eq_mul] at hsum
    apply (eq_div_iff (by positivity : ((m + 1 : ℕ) : ℝ) ≠ 0)).mpr
    rw [mul_comm]
    exact eq_sub_of_add_eq hsum

theorem binary_coordinate_eq {X : Type*} [Fintype X] [DecidableEq X]
    (hn : Fintype.card X = 2) (p : X → ℝ) (hp : p ∈ probabilitySimplex X) (i : X) :
    classicalSubentropy p = phi 0 (1 - p i) := by
  apply (classical_coordinate_eq_iff_equal_tail 0 hn p hp i).mpr
  have hc : (Finset.univ.erase i).card ≤ 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hn]
  intro j hj k hk
  exact congrArg p (Finset.card_le_one_iff.mp hc
    (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
    (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩))

theorem positive_priors_of_map_equality {X : Type*} [Fintype X] [DecidableEq X]
    (m : ℕ) (hn : Fintype.card X = m + 2) (p : X → ℝ) (hp : p ∈ probabilitySimplex X)
    (i : X) (hmax : ∀ j, p j ≤ p i) (herr : 0 < 1 - p i)
    (heq : classicalSubentropy p = phi m (1 - p i)) : ∀ j, 0 < p j := by
  intro j
  by_cases hji : j = i
  · rw [hji]
    have hr := (classical_error_range m hn p hp i hmax).2
    unfold uniformError at hr
    have : (0 : ℝ) < 1 / (m + 2 : ℕ) := by positivity
    linarith
  · rw [(classical_coordinate_eq_iff m hn p hp i).mp heq j hji]
    exact div_pos herr (by positivity)

/-- Equality for an average over the support of the outcome distribution.
The value `e` is its average error. No posterior is required outside `S`. -/
theorem classical_posterior_eq_iff {X Y : Type*} [Fintype X] [DecidableEq X]
    (m : ℕ) (hn : Fintype.card X = m + 2) (S : Finset Y) (q : Y → ℝ)
    (hq : ∀ y ∈ S, 0 < q y) (hs : ∑ y ∈ S, q y = 1)
    (b : Y → X → ℝ) (hb : ∀ y ∈ S, b y ∈ probabilitySimplex X)
    (selected : Y → X) (e : ℝ) (he : ∑ y ∈ S, q y * (1 - b y (selected y)) = e) :
    (∑ y ∈ S, q y * classicalSubentropy (b y)) = phi m e ↔
      ∀ y ∈ S, 1 - b y (selected y) = e ∧
        ∀ j, j ≠ selected y → b y j = e / (m + 1 : ℕ) := by
  let err (y : Y) := 1 - b y (selected y)
  have hmem (y : Y) (hy : y ∈ S) : err y ∈ Icc (0 : ℝ) 1 := by
    have hle : b y (selected y) ≤ 1 := by
      rw [← (hb y hy).2]
      exact Finset.single_le_sum (fun i _ => (hb y hy).1 i) (Finset.mem_univ _)
    exact ⟨sub_nonneg.mpr hle, sub_le_self _ ((hb y hy).1 _)⟩
  have hterm (y : Y) (hy : y ∈ S) :
      q y * classicalSubentropy (b y) ≤ q y * phi m (err y) :=
    mul_le_mul_of_nonneg_left
      (classical_coordinate_bound_finite m hn (b y) (hb y hy) (selected y)) (hq y hy).le
  have havg : ∑ y ∈ S, q y • err y = e := he
  have hj := (phi_strictConcave m).map_sum_eq_iff hq hs hmem
  have hbound := (phi_concave m).le_map_sum (fun y hy => (hq y hy).le) hs hmem
  rw [havg] at hj hbound
  simp only [smul_eq_mul] at hj hbound
  constructor
  · intro h
    have hsum := Finset.sum_le_sum hterm
    have hmiddle := le_antisymm hsum (hbound.trans_eq h.symm)
    have herr := hj.mp (h.symm.trans hmiddle)
    intro y hy
    have hlocal := (Finset.sum_eq_sum_iff_of_le hterm).mp hmiddle y hy
    have hycurve := mul_left_cancel₀ (hq y hy).ne' hlocal
    have htail := (classical_coordinate_eq_iff m hn (b y) (hb y hy) (selected y)).mp hycurve
    have hyerr : 1 - b y (selected y) = e := herr y hy
    exact ⟨hyerr, fun j hne => by rw [htail j hne, hyerr]⟩
  · intro h
    apply Eq.trans _ (hj.mpr (fun y hy => (h y hy).1)).symm
    apply Finset.sum_congr rfl
    intro y hy
    apply congrArg (q y * ·)
    apply (classical_coordinate_eq_iff m hn (b y) (hb y hy) (selected y)).mpr
    intro j hne
    rw [(h y hy).1]
    exact (h y hy).2 j hne

end SubentropyCertificates.ClassicalCurve
