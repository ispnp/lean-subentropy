module

public import SubentropyCertificates.ClassicalFano
public import SubentropyCertificates.UniformEndpoint

/-! The uniform maximum and the strictly increasing admissible branch. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped BigOperators

namespace SubentropyCertificates.ClassicalCurve
open D5.S3.Quantum.Subentropy.DensityKernel

theorem fin_subentropy_le_uniform (k : ℕ) (p : Fin (k + 1) → ℝ)
    (hp : p ∈ probabilitySimplex (Fin (k + 1))) :
    classicalSubentropy p ≤ classicalSubentropy (fun _ : Fin (k + 1) =>
      (1 : ℝ) / (k + 1 : ℕ)) := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hw : ∑ _j : Fin (k + 1), ((k + 1 : ℕ) : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hk
  have havg : (∑ j : Fin (k + 1), ((k + 1 : ℕ) : ℝ)⁻¹ •
      (p ∘ Equiv.addRight j)) = fun _ : Fin (k + 1) => (1 : ℝ) / (k + 1 : ℕ) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      Equiv.coe_addRight, ← Finset.mul_sum]
    have hsum := Equiv.sum_comp (Equiv.addLeft i) p
    simp only [Equiv.coe_addLeft] at hsum
    rw [hsum, hp.2]
    simp [one_div]
  have h := (classical_subentropy_concave (0 : Fin (k + 1))).le_map_sum
    (t := Finset.univ) (w := fun _ : Fin (k + 1) => ((k + 1 : ℕ) : ℝ)⁻¹)
    (p := fun j => p ∘ Equiv.addRight j) (fun _ _ => by positivity) hw
    (fun j _ => simplex_reindex p hp (Equiv.addRight j))
  rw [havg] at h
  simp only [classical_subentropy_reindex, smul_eq_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  simpa only [mul_inv_cancel_left₀ hk] using h

theorem subentropy_le_uniform (m : ℕ) (p : Option (Fin (m + 1)) → ℝ)
    (hp : p ∈ probabilitySimplex (Option (Fin (m + 1)))) :
    classicalSubentropy p ≤ classicalSubentropy
      (fun _ : Option (Fin (m + 1)) => (1 : ℝ) / (m + 2 : ℕ)) := by
  let e : Fin (m + 2) ≃ Option (Fin (m + 1)) := Fintype.equivOfCardEq (by simp [Nat.add_assoc])
  have h := fin_subentropy_le_uniform (m + 1) (p ∘ e) (simplex_reindex p hp e)
  have he : classicalSubentropy (fun _ : Fin (m + 2) => (1 : ℝ) / (m + 2 : ℕ)) =
      classicalSubentropy (fun _ : Option (Fin (m + 1)) => (1 : ℝ) / (m + 2 : ℕ)) :=
    classical_subentropy_reindex
      (fun _ : Option (Fin (m + 1)) => (1 : ℝ) / (m + 2 : ℕ)) e
  rw [classical_subentropy_reindex p e] at h
  exact h.trans_eq he

theorem uniformError_mem (m : ℕ) : uniformError m ∈ Icc (0 : ℝ) 1 := by
  have hn : (1 : ℝ) ≤ (m + 2 : ℕ) := by norm_cast; omega
  have hn0 : (0 : ℝ) < (m + 2 : ℕ) := by positivity
  exact ⟨by unfold uniformError; linarith [(div_le_one hn0).mpr hn],
    by unfold uniformError; linarith [div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hn0.le]⟩

theorem phi_le_uniform_max (m : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    phi m u ≤ phi m (uniformError m) := by
  have h := subentropy_le_uniform m (extremalVector m u) (extremal_probability m hu)
  simpa only [phi, extremal_uniform] using h

theorem phi_lt_uniform_max (m : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hne : u ≠ uniformError m) : phi m u < phi m (uniformError m) := by
  apply lt_of_le_of_ne (phi_le_uniform_max m hu)
  intro heq
  have hmu : IsMaxOn (phi m) (Icc (0 : ℝ) 1) u := by
    intro v hv
    rw [heq]
    exact phi_le_uniform_max m hv
  have hme : IsMaxOn (phi m) (Icc (0 : ℝ) 1) (uniformError m) :=
    fun _ hv => phi_le_uniform_max m hv
  exact hne ((phi_strictConcave m).eq_of_isMaxOn hmu hme hu (uniformError_mem m))

theorem phi_strictMono (m : ℕ) :
    StrictMonoOn (phi m) (Icc 0 (uniformError m)) := by
  intro u hu v hv huv
  have hue : u < uniformError m := huv.trans_le hv.2
  have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans (uniformError_mem m).2⟩
  by_cases hve : v = uniformError m
  · rw [hve]
    exact phi_lt_uniform_max m hu01 hue.ne
  · have hve' : v < uniformError m := lt_of_le_of_ne hv.2 hve
    have hseg : v ∈ openSegment ℝ u (uniformError m) :=
      Ioo_subset_openSegment ⟨huv, hve'⟩
    have h := (phi_strictConcave m).lt_on_openSegment hu01 (uniformError_mem m) hue.ne hseg
    simpa only [min_eq_left (phi_le_uniform_max m hu01)] using h

theorem phi_pos (m : ℕ) {u : ℝ} (hu : 0 < u) (hue : u ≤ uniformError m) :
    0 < phi m u := by
  have h := phi_strictMono m ⟨le_rfl, (uniformError_mem m).1⟩ ⟨hu.le, hue⟩ hu
  simpa only [phi_zero] using h

theorem phi_continuous (m : ℕ) : ContinuousOn (phi m) (Icc (0 : ℝ) 1) := by
  have hD : Continuous (fun u : ℝ => diagonal (fun i => (extremalVector m u i : ℂ))) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      cases i <;> simp only [extremalVector] <;> fun_prop
    · simp only [Matrix.diagonal_apply_ne _ hij]
      fun_prop
  exact continuousOn_matrixSubentropy.comp hD.continuousOn
    (fun _ hu => diagonal_density (extremal_probability m hu))

end SubentropyCertificates.ClassicalCurve
